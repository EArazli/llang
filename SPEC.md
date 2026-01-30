# Polygraph kernel specification (implemented)

This document specifies the **polygraph kernel** implemented in the project. It is the primary semantic reference for the current implementation.

---

## 0. Scope and architecture

The project implements a polygraph-based kernel and a DSL (“llang”) for describing:

1. **Polygraphic doctrines**: modes, types, generators, and 2‑cells (rewrite rules).
2. **Diagrams**: open hypergraphs with ordered boundaries.
3. **Rewriting**: deterministic, fuel‑bounded subdiagram rewriting (DPO‑style).
4. **Morphisms**: structure‑preserving translations between doctrines, checked by normalization/joinability.
5. **Surfaces and models**: diagram surfaces (`surface`) and evaluator models (`model`).
6. **Runs**: diagram‑level normalization/evaluation pipelines (`run`).

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
- **Cycles are allowed**: diagrams need not be acyclic, as long as linearity and boundary
  invariants hold.

For a **box** edge, the nested diagram must:

- share the outer diagram’s mode, and
- have input/output boundary types matching the edge’s input/output port types.

The internal representation (`Strat.Poly.Graph`) stores:

- port types, producer/consumer incidence maps,
- edge table, and
- boundary port lists.

Box names are **metadata only**: diagram equality and matching ignore the `BoxName`,
but the **box structure is part of matching**. A box edge matches another box edge
iff their inner diagrams are isomorphic **modulo type‑variable unification** and
boundary ordering, and matching does not ignore box structure.

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

Boxes are matched **structurally** when the pattern contains a box edge:
the inner diagrams must be isomorphic up to type‑variable unification and
boundary order. Box names are ignored.

**Type variable discipline:** for every rule/cell, `freeTyVars(RHS) ⊆ freeTyVars(LHS)`.
RHS terms cannot introduce fresh type variables.

### 4.2 Rewrite step

A rewrite step replaces a matched subdiagram `L` by `R`:

1. Delete the matched edges.
2. Delete matched **internal** ports (dangling‑safe by construction).
3. Instantiate `R` by the match substitution.
4. Insert a fresh copy of `R` and glue its boundary to the matched boundary ports.

**Empty‑LHS rules are disallowed.** Rules must match at least one edge.

### 4.3 Normalization and joinability

- `rewriteOnce` applies the **first** matching rule in rule order.
- `normalize` repeats `rewriteOnce` until no rule applies or fuel is exhausted.
- `joinableWithin` performs a BFS (depth‑bounded by fuel, branching capped) and succeeds if a common diagram is found.

Normalization is deterministic for a fixed rule order and fuel.

Rewriting is **outermost‑leftmost** with respect to boxes: a top‑level rewrite is attempted first; if none applies, the engine searches inside box edges in edge‑id order.

### 4.4 Critical branchings and coherence

The polygraph kernel computes **critical branchings** (critical pairs) by overlapping
rule LHS diagrams:

- Enumerate **connected, non‑empty** partial isomorphisms between two LHS diagrams
  (respecting generators, incidence order, and box‑structure; types unify under `unifyTyFlex`).
- Build the **overlap host** by gluing the two LHS diagrams along the overlap.
- Apply each rule at its induced match in the overlap host, producing a peak
  `O ↠ L` and `O ↠ R`.
- Deduplicate overlaps up to diagram isomorphism.

**Coherence obligations** depend on rule classes:

- Structural vs Structural ⇒ **NeedsCommute**
- Structural vs Computational (either order) ⇒ **NeedsJoin**
- Computational vs Computational ⇒ optional (enabled under `CP_All`)

Joinability is checked with bounded search (fuel + breadth cap), and the engine can
return witnesses (a meeting diagram with rewrite paths).

**Current limitations (known, not fixed yet):**

- Overlap enumeration includes **non‑maximal** connected overlaps, so coherence
  obligations can be larger than the minimal critical branching set.
- Joinability uses **bounded search** (fuel + breadth cap), so it can report a
  failure for a joinable peak when the cap is exceeded.

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

The DSL introduces `doctrine` blocks and diagram expressions.

### 6.1 Doctrine

```
doctrine <Name> [extends <Base>] where {
  mode <ModeName>;
  type <TypeName> [<tyvar> ...] @<ModeName>;
  gen  <GenName>  [<tyvar> ...] : <Ctx> -> <Ctx> @<ModeName>;
  rule <class> <RuleName> <orient> [<tyvar> ...] : <Ctx> -> <Ctx> @<ModeName> =
    <DiagExpr> == <DiagExpr>;
}
```

Doctrines can also be defined as colimits of existing doctrines:

```
doctrine <Name> = pushout <morphism> <morphism>;
doctrine <Name> = coproduct <Left> <Right>;
```

- `pushout` requires morphisms with **renaming/inclusion** behavior (single‑generator images) and injective interface maps.
- The pushout produces canonical morphisms `<Name>.inl`, `<Name>.inr`, and `<Name>.glue`.
- Non‑interface generators and types are automatically **disjoint‑renamed** in the pushout (prefixing by the target doctrine name plus `_inl`/`_inr`) to avoid collisions.
- `coproduct` is implemented as a pushout over an empty interface (so all symbols are renamed disjointly).
- If interface 2‑cells with the same name are **iso‑equal by body**, they are merged:
  `Structural` wins over `Computational`, and orientations are joined
  (`Bidirectional` dominates; `LR` + `RL` ⇒ `Bidirectional`; `Unoriented` is identity).
  If bodies differ, the pushout fails with a name‑collision error.

### 6.2 Morphisms

```
morphism <Name> : <Src> -> <Tgt> where {
  type <SrcType>(a1,...,an) @<Mode> -> <TgtTypeExpr> @<Mode>;
  gen  <SrcGen>  @<Mode> -> <DiagExpr>;
  policy <RewritePolicy>;
  fuel <N>;
}
```

- Every source generator must be mapped.
- Type mappings are **templates with explicit binders**: the RHS may be any type expression
  whose free variables are a subset of `{a1,...,an}`.
- When a morphism is used as a **pushout leg**, its type mappings must be **invertible renamings**
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
box <Name> { <d> }    -- boxed subdiagram
loop { <d> }          -- feedback: connects the single output of <d> to its single input
<d1> ; <d2>           -- composition (first d1 then d2)
<d1> * <d2>           -- tensor
```

Composition/tensor are parsed with the usual precedence (`*` binds tighter than `;`).

`loop { <d> }` requires `<d>` to have exactly one input and **at least one output**.
The **first** output port is identified with the input port (feedback); the remaining
outputs become the outputs of the looped diagram. The result has **no inputs** and
`(n−1)` outputs.

---

### 6.5 Surfaces

Surfaces define a surface language and its
elaboration to diagrams.

```
surface <Name> where {
  doctrine <Doctrine>;
  mode <Mode>;
  context <ctx> = <Type>;  -- optional

  lexer { ... }
  expr  { ... }
  elaborate { ... }
}
```

#### Lexer

```
lexer {
  keywords: kw1, kw2, ...;
  symbols: "(", ")", "->", ...;
}
```

Identifiers use the fixed pattern `[a-zA-Z_][a-zA-Z0-9_]*` and must not be in
`keywords`. `symbols` are literal tokens matched as punctuation/operators.

#### Expression grammar

The expression grammar is a deterministic Pratt parser with four kinds of rules:

```
expr {
  atom:   <pattern> => <action> | ... ;
  prefix: <pattern> => <action> | ... ;
  infixl <prec> "<tok>" => <action>;
  infixr <prec> "<tok>" => <action>;
  application: <expr> <expr> => <action>;   -- optional
}
```

Patterns are sequences of items:

```
ident       -- identifier capture
<expr>      -- expression capture
<type>      -- type capture
"literal"   -- exact token match
```

Actions construct the surface AST:

- `=> <expr>` returns the single captured expression (exactly one is required).
- `=> Ctor(a, b, ...)` builds an AST node with the captured items in order.

#### Elaboration rules

```
elaborate {
  Ctor(x, y, z) => <template>;
  ...
}
```

Rules in `elaborate` blocks are separated by `;;` to avoid ambiguity with the
composition operator `;` inside templates.

Templates use the diagram-expression language (`id`, `box`, `loop`, `;`, `*`,
generators) plus **placeholders**:

- `$1`, `$2`, ... refer to child elaborations (positional).
- `$x` refers to a bound variable occurrence (see binding rules below).

A constructor named `CALL` with arguments `(name, arg)` is treated as a generator
call: `name` is the generator name, and `arg` elaborates to its argument diagram.

#### Binding rules + cartesian structure

Binding is inferred by syntax:

- If a constructor captures `ident` immediately followed by `<type>`, it is an
  **input binder**. The last expression capture is the body.
- Otherwise, if it captures an `ident` and **at least two** expression captures,
  it is a **value binder**. The first expression after the ident is the bound
  value; the last expression capture is the body.

Elaboration semantics:

- Input binders introduce a fresh input port of the annotated type.
- Variable occurrences elaborate to wire references to that port.
- Multiple uses insert `dup` to supply copies (left‑associated duplication);
  zero uses insert `drop`. Therefore any surface with binders requires the
  doctrine mode to provide `dup` and `drop` with the cartesian shapes.

Optional `context <ctx> = <Type>` enables CCC‑style context threading:

- The binder variable is interpreted as `Hom(prod(ctx, ty), ty)`.
- The `ctx` type variable is updated to `prod(ctx, ty)` while elaborating the body.

### 6.6 Models

```
model <Name> : <Doctrine> where {
  default symbolic;
  op <GenName>(args...) = <expr>;
}
```

Models use the same expression language for generator clauses. Evaluation is defined
only for **closed** diagrams (no boundary inputs/outputs).

**Cycles are supported** using SCC‑based evaluation:

- Acyclic components are evaluated concretely via the model clauses.
- Cyclic components are evaluated symbolically with placeholders `$pN`, producing a
  `letrec` wrapper in the output value:

  ```
  [letrec, [[ $p0, expr0 ], [ $p1, expr1 ], ...], body]
  ```

Generators (including `dup`, `drop`, and `swap`) are interpreted only via the model
clauses or the model’s default behavior; no special built‑ins are assumed.

---

## 7. Runs

`run` blocks evaluate diagram expressions or surface programs:

```
run <Name> where {
  doctrine <Doctrine>;
  mode <Mode>;          -- required if the doctrine has multiple modes
  surface <Surface>;    -- optional; parses with a surface definition
  model <Model>;        -- optional; required for show value
  apply <Morphism>;     -- optional; may be repeated, applied in order
  policy <RewritePolicy>;
  fuel <N>;
  show normalized;
  show input;        -- optional
  show value;        -- optional, requires model and closed diagram
  show coherence;    -- optional, prints critical‑pair coherence report
}
---
<DiagExpr | SurfaceProgram>
```

The run pipeline:

1. Parses either a diagram expression or a surface program.
2. Elaborates it against the chosen doctrine/mode.
3. Applies any `apply` morphisms in order, updating the current doctrine each time.
4. Normalizes via the polygraph rewrite engine (filtered by the policy; default `UseStructuralAsBidirectional`).
5. Optionally evaluates via a model (closed diagrams only, and the model must match the final doctrine).
6. Optionally checks coherence (critical branchings) and renders a report.
7. Prints the requested outputs depending on flags.

`show cat` is currently not supported for runs.
