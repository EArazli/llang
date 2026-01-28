# Polygraph kernel specification (implemented)

This document specifies the **polygraph kernel** implemented in the project. It is the primary semantic reference for the current implementation. The previous (GAT/term) kernel is now **legacy**; see `SPEC-LEGACY.md`.

---

## 0. Scope and architecture

The project implements a polygraph-based kernel and a DSL (“llang”) for describing:

1. **Polygraphic doctrines**: modes, types, generators, and 2‑cells (rewrite rules).
2. **Diagrams**: open hypergraphs with ordered boundaries.
3. **Rewriting**: deterministic, fuel‑bounded subdiagram rewriting (DPO‑style).
4. **Morphisms**: structure‑preserving translations between doctrines, checked by normalization/joinability.
5. **Surfaces and models**: diagram surfaces (`polysurface`) and evaluator models (`polymodel`).
6. **Runs**: diagram‑level normalization/evaluation pipelines (`polyrun`).

Legacy GAT syntax, Surface2, and model evaluation remain implemented but are treated as **legacy surfaces**; they are not the kernel reference in this document.

---

## 1. Mode theory and types

### 1.1 Modes

A **mode theory** consists of:

- A finite set of **modes**.
- Optional modality declarations and equations (currently stored but not used in diagram typing).

Modes are identified by `ModeName` (text). In practice, examples use a single mode `M`.

### 1.2 Type expressions

Types are **mode‑indexed objects**, not GAT sorts. The polygraph kernel uses a first‑order type language:

```
TypeExpr = TVar TyVar | TCon TypeName [TypeExpr]
Context  = [TypeExpr]
```

- `TyVar` and `TypeName` are textual names.
- Type constructors have fixed **arity**.

### 1.3 Type unification

The kernel provides a unifier:

- `unifyTy :: TypeExpr -> TypeExpr -> Either Text Subst`
- `unifyCtx :: Context -> Context -> Either Text Subst`

with an **occurs check**. Composition and rule matching rely on this unifier to reconcile diagram boundaries.

---

## 2. Doctrines

A **polygraphic doctrine** packages:

- a mode theory,
- a per‑mode type constructor table (`TypeName -> arity`),
- generator declarations, and
- 2‑cells (rewrite rules).

### 2.1 Generators

A generator declaration is:

```
GenDecl = { name, mode, tyvars, dom, cod }
```

- `dom` and `cod` are contexts in the generator’s mode.
- `tyvars` are schematic type parameters for generic generators.
- `tyvars` are **binders**: their names are α‑irrelevant, and duplicates are rejected.

### 2.2 2‑cells

A 2‑cell is a named rewrite equation between diagrams:

```
Cell2 = { name, class, orient, tyvars, lhs, rhs }
```

- `lhs` and `rhs` are diagrams of the same mode.
- Their boundaries must unify (same context lengths; types unify under a substitution).
- `tyvars` are **binders**: their names are α‑irrelevant, and duplicates are rejected.

### 2.3 Validation

`validateDoctrine` checks:

- referenced modes exist,
- type constructor arities match,
- generator domains/codomains are well‑formed,
- 2‑cell diagrams validate and have compatible boundaries,
- all type variables used are declared in the generator or cell scope.

---

## 3. Diagrams: open hypergraphs

### 3.1 Representation

A diagram is an **open directed hypergraph** with **ports as vertices** and generator instances as hyperedges:

- **Ports** have types.
- **Edges** have ordered input ports and ordered output ports; each edge payload is either
  a **generator instance** or a **box** containing a nested diagram.
- **Boundary** consists of ordered input ports and ordered output ports.
- **Linearity invariant**: each port has at most one producer and at most one consumer.

For a **box** edge, the nested diagram must:

- share the outer diagram’s mode, and
- have input/output boundary types matching the edge’s input/output port types.

The internal representation (`Strat.Poly.Graph`) stores:

- port types, producer/consumer incidence maps,
- edge table, and
- boundary port lists.

Box names are **metadata only**: diagram equality and matching ignore the `BoxName`,
but the box *structure* still matters (matching only penetrates boxes when the pattern
explicitly contains a box edge).

### 3.2 Constructors

- `idD mode [A1..Ak]` creates k boundary ports and no edges.
- `genD` creates a single edge with fresh ports for its boundary.
- `tensorD` forms a disjoint union (boundary concatenation).
- `compD g f` glues `f`’s outputs to `g`’s inputs (port identification), after unifying boundary contexts.

### 3.3 Validation

`validateDiagram` checks:

- boundary ports exist,
- edge incidences are consistent,
- producer/consumer maps agree with edges,
- linearity (≤1 producer/consumer per port).

For box edges, validation recurses into the nested diagram and checks boundary agreement.

It is enforced after composition, tensor, rewrite steps, and morphism application.

---

## 4. Rewriting (DPO‑style)

### 4.1 Matching

A match is a structure‑preserving embedding of a pattern diagram into a host diagram:

```
Match = { mPorts, mEdges, mTySub }
```

Constraints:

- generator labels must match,
- ordered incidences must match,
- port types unify under `mTySub`,
- **dangling condition**: ports internal to the pattern must not connect to host edges outside the matched image.

Matching order is deterministic (by edge id, then adjacent edges, then candidate host edges by id).

Boxes are **opaque** to matching unless the pattern explicitly contains a box edge.
Box names are ignored during matching.

### 4.2 Rewrite step

A rewrite step replaces a matched subdiagram `L` by `R`:

1. Delete the matched edges.
2. Delete matched **internal** ports (dangling‑safe by construction).
3. Instantiate `R` by the match substitution.
4. Insert a fresh copy of `R` and glue its boundary to the matched boundary ports.

### 4.3 Normalization and joinability

- `rewriteOnce` applies the **first** matching rule in rule order.
- `normalize` repeats `rewriteOnce` until no rule applies or fuel is exhausted.
- `joinableWithin` performs a BFS (depth‑bounded by fuel, branching capped) and succeeds if a common diagram is found.

Normalization is deterministic for a fixed rule order and fuel.

Rewriting is **outermost‑leftmost** with respect to boxes: a top‑level rewrite is attempted first; if none applies, the engine searches inside box edges in edge‑id order.

---

## 5. Morphisms

A morphism `F : D → E` consists of:

- a **mode‑indexed type map** (`(ModeName, TypeName) ↦ (a1…an ⊢ τ)` templates),
- a **mode‑indexed generator map** (`(ModeName, GenName) ↦ Diagram`),
- rewrite policy and fuel for equation checking.

### 5.1 Applying a morphism

To apply `F` to a diagram:

1. Map all port types using the type map templates.
2. For each edge, instantiate the generator mapping (using unification to recover type parameters), in the edge’s mode.
3. Splice the mapped diagram into the host by boundary identification.

### 5.2 Morphism checking

For each source 2‑cell `L == R`:

1. Translate both sides under `F`.
2. Normalize in the target doctrine (fuel‑bounded).
3. If both normalize, require syntactic equality.
4. Otherwise, use `joinableWithin` under the target rewrite system.

This mirrors the implementation’s `checkMorphism` behavior.

**Current limitation:** mode mapping is identity only (modes are not translated).

---

## 6. Polygraph DSL

The DSL introduces `polydoctrine` blocks and diagram expressions.

### 6.1 Polydoctrine

```
polydoctrine <Name> [extends <Base>] where {
  mode <ModeName>;
  type <TypeName> [<tyvar> ...] @<ModeName>;
  gen  <GenName>  [<tyvar> ...] : <Ctx> -> <Ctx> @<ModeName>;
  rule <class> <RuleName> <orient> [<tyvar> ...] : <Ctx> -> <Ctx> @<ModeName> =
    <DiagExpr> == <DiagExpr>;
}
```

Polydoctrines can also be defined as colimits of existing polydoctrines:

```
polydoctrine <Name> = pushout <morphism> <morphism>;
polydoctrine <Name> = coproduct <Left> <Right>;
```

- `pushout` requires morphisms with **renaming/inclusion** behavior (single‑generator images) and injective interface maps.
- The pushout produces canonical morphisms `<Name>.inl`, `<Name>.inr`, and `<Name>.glue`.
- Non‑interface generators and types are automatically **disjoint‑renamed** in the pushout (prefixing by the target doctrine name plus `_inl`/`_inr`) to avoid collisions.
- `coproduct` is implemented as a pushout over an empty interface (so all symbols are renamed disjointly).

### 6.2 Polymorphisms

```
polymorphism <Name> : <Src> -> <Tgt> where {
  type <SrcType>(a1,...,an) @<Mode> -> <TgtTypeExpr> @<Mode>;
  gen  <SrcGen>  @<Mode> -> <DiagExpr>;
  policy <RewritePolicy>;
  fuel <N>;
}
```

- Every source generator must be mapped.
- Type mappings are **templates with explicit binders**: the RHS may be any type expression
  whose free variables are a subset of `{a1,...,an}`.
- When a polymorphism is used as a **pushout leg**, its type mappings must be **invertible renamings**
  (constructor rename + parameter permutation).
- Generator mappings must elaborate to diagrams in the target doctrine/mode.

### 6.3 Types and contexts

- A context is a bracketed list: `[A, B, ...]` or `[]`.
- Types are either:
  - lowercase identifiers (type variables), or
  - uppercase constructors with optional argument lists.

### 6.4 Diagram expressions

```
id[<Ctx>]
<GenName>{<Ty>,...}   -- optional type arguments
<d1> ; <d2>           -- composition (first d1 then d2)
<d1> * <d2>           -- tensor
```

Composition/tensor are parsed with the usual precedence (`*` binds tighter than `;`).

---

### 6.5 Polysurfaces

```
polysurface <Name> : doctrine <PolyDoctrine> mode <Mode> where { }
```

Polysurfaces select a **diagram surface language**:

- **SSA surface** (declared via `polysurface`): expects a `diag { ... }` block with
  `in`, assignment statements, optional `box` statements, and `out`.
- **CartTermSurface** (built‑in): expects a `term { ... }` block and elaborates
  function‑style terms to diagrams by inserting `dup`/`drop` from the doctrine.

### 6.6 Polymodels

```
polymodel <Name> : <PolyDoctrine> where {
  default symbolic;
  op <GenName>(args...) = <expr>;
}
```

Polymodels use the same expression language as legacy models. Evaluation is defined
only for **closed** diagrams and is currently restricted to **acyclic** diagrams.
Generators `dup`, `drop`, and `swap` have built‑in interpretations.

---

## 7. Runs

`polyrun` blocks evaluate diagram expressions or surface programs:

```
polyrun <Name> where {
  doctrine <PolyDoctrine>;
  mode <Mode>;          -- required if the doctrine has multiple modes
  surface <Surface>;    -- optional; chooses SSA or CartTerm surface
  surface_syntax <SurfaceSyntax>; -- required for legacy Surface2 surfaces
  core_doctrine <Doctrine>;       -- optional; defaults to doctrine (legacy Surface2 elaboration)
  model <PolyModel>;    -- optional; required for show value
  apply <PolyMorphism>; -- optional; may be repeated, applied in order
  policy <RewritePolicy>;
  fuel <N>;
  show normalized;
  show input;        -- optional
  show value;        -- optional, requires model and closed diagram
}
---
<DiagExpr | SurfaceProgram>
```

The run pipeline:

1. Parses either a diagram expression or a surface program.
2. Elaborates it against the chosen doctrine/mode.
3. Applies any `apply` polymorphisms in order, updating the current doctrine each time.
4. Normalizes via the polygraph rewrite engine (filtered by the policy; default `UseStructuralAsBidirectional`).
5. Optionally evaluates via a polymodel (closed diagrams only, and the model must match the final doctrine).
6. Prints the normalized diagram, input, and/or value depending on flags.

If `surface` refers to a legacy Surface2 surface (i.e. not a poly surface), `surface_syntax` is required and `core_doctrine` selects the kernel doctrine used for surface elaboration (defaults to `doctrine`).

`show cat` is currently not supported for polyruns.

---

## 8. Legacy kernel note

The earlier GAT/term kernel (presentations, terms, Surface2, and model evaluation) remains implemented as a **legacy surface**. It is no longer the primary kernel reference; see `SPEC-LEGACY.md` for the previous formalism.
