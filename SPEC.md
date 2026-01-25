# Polygraph kernel specification (implemented)

This document specifies the **polygraph kernel** implemented in the project. It is the primary semantic reference for the current implementation. The previous (GAT/term) kernel is now **legacy**; see `SPEC-LEGACY.md`.

---

## 0. Scope and architecture

The project implements a polygraph-based kernel and a DSL (“llang”) for describing:

1. **Polygraphic doctrines**: modes, types, generators, and 2‑cells (rewrite rules).
2. **Diagrams**: open hypergraphs with ordered boundaries.
3. **Rewriting**: deterministic, fuel‑bounded subdiagram rewriting (DPO‑style).
4. **Morphisms**: structure‑preserving translations between doctrines, checked by normalization/joinability.
5. **Runs**: diagram‑level normalization pipelines (`polyrun`).

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

### 2.2 2‑cells

A 2‑cell is a named rewrite equation between diagrams:

```
Cell2 = { name, class, orient, tyvars, lhs, rhs }
```

- `lhs` and `rhs` are diagrams of the same mode.
- Their boundaries must unify (same context lengths; types unify under a substitution).

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
- **Edges** have ordered input ports and ordered output ports.
- **Boundary** consists of ordered input ports and ordered output ports.
- **Linearity invariant**: each port has at most one producer and at most one consumer.

The internal representation (`Strat.Poly.Graph`) stores:

- port types, producer/consumer incidence maps,
- edge table, and
- boundary port lists.

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

---

## 5. Morphisms

A morphism `F : D → E` consists of:

- a **type constructor map** (`TypeName ↦ TypeExpr`),
- a **generator map** (`GenName ↦ Diagram`),
- rewrite policy and fuel for equation checking.

### 5.1 Applying a morphism

To apply `F` to a diagram:

1. Map all port types using the type map.
2. For each edge, instantiate the generator mapping (using unification to recover type parameters).
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

### 6.2 Types and contexts

- A context is a bracketed list: `[A, B, ...]` or `[]`.
- Types are either:
  - lowercase identifiers (type variables), or
  - uppercase constructors with optional argument lists.

### 6.3 Diagram expressions

```
id[<Ctx>]
<GenName>{<Ty>,...}   -- optional type arguments
<d1> ; <d2>           -- composition (first d1 then d2)
<d1> * <d2>           -- tensor
```

Composition/tensor are parsed with the usual precedence (`*` binds tighter than `;`).

---

## 7. Runs

`polyrun` blocks evaluate diagram expressions directly:

```
polyrun <Name> where {
  doctrine <PolyDoctrine>;
  fuel <N>;
  show normalized;
  show input;        -- optional
}
---
<DiagExpr>
```

The run pipeline:

1. Parses the diagram expression.
2. Elaborates it against the chosen doctrine.
3. Normalizes via the polygraph rewrite engine.
4. Prints the normalized diagram (and input, if requested).

Only diagram‑level output is produced for `polyrun` runs.

---

## 8. Legacy kernel note

The earlier GAT/term kernel (presentations, terms, Surface2, and model evaluation) remains implemented as a **legacy surface**. It is no longer the primary kernel reference; see `SPEC-LEGACY.md` for the previous formalism.
