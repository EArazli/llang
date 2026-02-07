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
6. **Runs**: diagram‑level normalization/evaluation pipelines (`run_spec` + `run`).

---

## 1. Mode theory and types

### 1.1 Modes

A **mode theory** consists of:

- A finite set of **modes**.
- A per-mode variable discipline (`linear`, `affine`, `relevant`, `cartesian`).
- Modality declarations (`modality μ : M -> N;`).
- Ordered oriented modality equations (`mod_eq <lhs> -> <rhs>;`), used as rewrite rules.
- Optional adjunction declarations (`adjunction F dashv U;`).

Modes are identified by `ModeName` (text). Discipline is monotone-upgraded with:
`linear <= affine <= cartesian` and `linear <= relevant <= cartesian`.

### 1.2 Type expressions

Types are **mode-indexed objects**, not GAT sorts. The polygraph kernel uses a first-order type language:

```
TypeRef  = { trMode :: ModeName, trName :: TypeName }
TyVar    = { tvName :: Text, tvMode :: ModeName }
TypeExpr = TVar TyVar | TCon TypeRef [TypeExpr] | TMod ModExpr TypeExpr
Context  = [TypeExpr]
```

- `TypeRef` pairs a constructor name with its mode; nested constructors may come from other modes.
- `TyVar` names are textual; variables are **mode-indexed**.
- Type constructors have fixed **mode signatures** `(m1,...,mk) -> m`.
- `TMod me ty` applies a modality expression to a type. Its mode is `me`'s target mode.
- Within any binder list (generator, rule, or template), tyvar names must be unique by **name**
  (uniqueness is not by `(name, mode)`).

### 1.3 Type unification

The kernel provides a unifier:

- `unifyTy :: ModeTheory -> TypeExpr -> TypeExpr -> Either Text Subst`
- `unifyCtx :: ModeTheory -> Context -> Context -> Either Text Subst`

with an **occurs check**. Composition and rule matching rely on this unifier to reconcile diagram boundaries.
All unification and substitution operations normalize modality expressions/types using the current mode theory.

Unification respects modes:

- `TVar v` can only unify with a type `t` when `tvMode v == typeMode t`.
- `TCon r ...` only unifies with `TCon r ...` with the same `TypeRef` (mode + name).

---

## 2. Doctrines

A **polygraphic doctrine** packages:

- a mode theory,
- an attribute-sort table (`AttrSort -> AttrSortDecl`),
- a per-mode type constructor table (`TypeName -> TypeSig`),
- generator declarations, and
- 2‑cells (rewrite rules).

Where:

```
TypeSig      = { tsParams :: [ModeName] }   -- parameter modes
AttrLitKind  = int | string | bool
AttrSortDecl = { asName :: AttrSort, asLitKind :: Maybe AttrLitKind }
```

- Attribute sorts may be declared with or without a literal kind.
- If an attribute sort has no literal kind (`asLitKind = Nothing`), literals of that sort are rejected.

### 2.1 Generators

A generator declaration is:

```
GenDecl = { name, mode, tyvars, attrs, dom, cod }

attrs :: [(AttrName, AttrSort)]
```

- `dom` and `cod` are contexts in the generator’s mode.
- `tyvars` are schematic type parameters for generic generators.
- `tyvars` are **binders**: their names are α‑irrelevant, and duplicates are rejected.
- Attribute field names are distinct within a generator.
- Every attribute field sort must exist in `dAttrSorts`.
- Generator instances in diagrams carry exactly the declared attribute fields.

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
- attribute-sort declarations are well-formed,
- type constructor arities match,
- generator domains/codomains are well‑formed,
- generator attribute fields are well-formed,
- 2‑cell diagrams validate and have compatible boundaries,
- all type variables used are declared in the generator or cell scope,
- every cell satisfies both variable disciplines:
  `freeTyVars(RHS) ⊆ freeTyVars(LHS)` and
  `freeAttrVars(RHS) ⊆ freeAttrVars(LHS)`,
- attribute-variable name/sort hygiene holds (the same variable name cannot appear at multiple sorts).

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

Generator payloads carry attributes:

```
EdgePayload = PGen GenName AttrMap | PBox BoxName Diagram
AttrMap     = AttrName -> AttrTerm
AttrTerm    = ATVar AttrVar | ATLit AttrLit
AttrVar     = { name :: Text, sort :: AttrSort }
AttrLit     = Int | String | Bool
```

For a **box** edge, the nested diagram must:

- share the outer diagram’s mode, and
- have input/output boundary types matching the edge’s input/output port types.
- recursively carry generator payload attributes by the same representation.

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
Match = { mPorts, mEdges, mTySub, mAttrSub }
```

Constraints:

- generator labels must match,
- ordered incidences must match,
- port types unify under `mTySub`,
- generator attribute key sets must match,
- corresponding generator attribute terms unify under `mAttrSub`,
- **dangling condition**: ports internal to the pattern must not connect to host edges outside the matched image.

Attribute unification uses `unifyAttrFlex`:

- flexible variables are exactly `freeAttrVars(LHS)` for the rule being matched,
- rigid variables (not in that set) must match exactly.

Matching order is deterministic (by edge id, then adjacent edges, then candidate host edges by id).

Boxes are matched **structurally** when the pattern contains a box edge:
the inner diagrams must be isomorphic up to type‑variable unification and
boundary order. Box names are ignored.

Variable discipline for every rule/cell:

- `freeTyVars(RHS) ⊆ freeTyVars(LHS)` (no fresh type variables on RHS),
- `freeAttrVars(RHS) ⊆ freeAttrVars(LHS)` (no fresh attribute variables on RHS),
- attribute-variable names are globally sort-consistent within a diagram
  (name -> sort is a partial function).

### 4.2 Rewrite step

A rewrite step replaces a matched subdiagram `L` by `R`:

1. Delete the matched edges.
2. Delete matched **internal** ports (dangling‑safe by construction).
3. Instantiate `R` by both match substitutions (`mTySub` and `mAttrSub`).
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
  (respecting generators, incidence order, and box‑structure; types unify under `unifyTyFlex`,
  attributes unify under `unifyAttrFlex`).
- Freshen variables of each rule before overlap search, including **attribute variables**
  (not only type variables), to avoid accidental capture across rules.
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

- a **mode map** (a total mapping from source modes to target modes),
- an **attribute-sort map** (`AttrSort -> AttrSort`),
- a **mode-indexed type map** (`TypeRef ↦ (a1…an ⊢ τ)` templates),
- a **mode‑indexed generator map** (`(ModeName, GenName) ↦ Diagram`),
- rewrite policy and fuel for equation checking.

### 5.1 Applying a morphism

To apply `F` to a diagram:

1. Map the diagram mode using the mode map, and map all port types using the type map
   templates (type‑variable modes are mapped by the mode map; unmapped constructors keep
   their name and only their mode is translated).
2. Map attribute-variable sorts via the attribute-sort map.
3. For each edge in source mode `m`, instantiate the generator mapping (using unification
   to recover type parameters and attribute substitutions), then apply it in target mode `mapMode(m)`.
4. Splice the mapped diagram into the host by boundary identification.

### 5.2 Morphism checking

For each source 2‑cell `L == R`:

1. Translate both sides under `F`.
2. Normalize in the target doctrine (fuel‑bounded).
3. If both normalize, require syntactic equality.
4. Otherwise, use `joinableWithin` under the target rewrite system.

This mirrors the implementation’s `checkMorphism` behavior.

The mode map must be total on source modes and must land in modes that exist in the
target doctrine; generator mappings must elaborate to diagrams in the mapped target mode.
The attribute-sort map must map used source attribute sorts to existing target sorts.
Literal-kind preservation is enforced: if a source sort admits literal kind `k`,
its mapped target sort must also admit `k`.

---

## 6. Polygraph DSL

The DSL introduces `doctrine` blocks and diagram expressions.

### 6.1 Doctrine

```
doctrine <Name> [extends <Base>] where {
  mode <ModeName>;
  structure <ModeName> = linear | affine | relevant | cartesian;
  modality <ModName> : <ModeName> -> <ModeName>;
  mod_eq <ModExpr> -> <ModExpr>;
  adjunction <ModName> dashv <ModName>;
  attrsort <SortName> [= int | string | bool];
  type <TypeName> (<tyvar> [, ...]) @<ModeName>;
  gen  <GenName>  (<tyvar> [, ...]) [ { f1:S1, ..., fk:Sk } ] : <Ctx> -> <Ctx> @<ModeName>;
  rule <class> <RuleName> <orient> (<tyvar> [, ...]) : <Ctx> -> <Ctx> @<ModeName> =
    <DiagExpr> == <DiagExpr>;
}
```

- A tyvar binder is `a` or `a@Mode`. If the mode is omitted, it defaults to the declaration mode.
- Binder lists may be empty or omitted when no parameters are needed.
- `structure` can only upgrade discipline according to the partial order
  `linear <= affine <= cartesian` and `linear <= relevant <= cartesian`.
- Modality expressions use:
  - `id@M` for identity on mode `M`.
  - `U.F` for composition (`U ∘ F`, rightmost applies first).
- `mod_eq` rules are oriented rewrites and must be strictly length-decreasing in modality-path length.
- `adjunction F dashv U` requires opposite directions and auto-generates
  `unit_F`/`counit_F` generators with the expected modality-typed boundaries.
- `attrsort S = int|string|bool;` declares a literal-admitting sort.
- `attrsort S;` declares a sort with no literal kind (literals are rejected at that sort).
- Generator attribute blocks `{ ... }` are optional; when present, each entry is `field:Sort`.

Inside doctrine blocks, `data` is syntactic sugar for a type plus constructor generators:

```
data List (a@M) @M where {
  Nil  : [];
  Cons : [a, List(a)];
}
```

This expands to:

```
type List (a@M) @M;
gen Nil  (a@M) : [] -> [List(a)] @M;
gen Cons (a@M) : [a, List(a)] -> [List(a)] @M;
```

Constructor names must be unique within the `data` block and must not collide with existing
generator names in that mode.

When a doctrine extends a base (`extends Base`), the system automatically generates a
coercion morphism `<Name>.fromBase : Base -> Name` mapping each base generator to itself.

Doctrines can also be defined as colimits of existing doctrines:

```
doctrine <Name> = pushout <morphism> <morphism>;
doctrine <Name> = coproduct <Left> <Right>;
```

- `pushout` requires morphisms with **renaming/inclusion** behavior (single‑generator images) and injective interface maps.
- `pushout` additionally requires **mode‑preserving** morphisms (the mode map must be the identity).
- The pushout produces canonical morphisms `<Name>.inl`, `<Name>.inr`, and `<Name>.glue`.
- Non‑interface generators and types are automatically **disjoint‑renamed** in the pushout (prefixing by the target doctrine name plus `_inl`/`_inr`) to avoid collisions.
- `coproduct` is implemented as a pushout over an empty interface (so all symbols are renamed disjointly).
- If interface 2‑cells with the same name are **iso‑equal by body**, they are merged:
  `Structural` wins over `Computational`, and orientations are joined
  (`Bidirectional` dominates; `LR` + `RL` ⇒ `Bidirectional`; `Unoriented` is identity).
  If bodies differ, the pushout fails with a name‑collision error.

Doctrines can also be defined via macros:

```
doctrine_template Temp(P1, ..., Pn) where {
  doctrine Temp [extends Base] where { ... }
}

doctrine New = instantiate Temp(A1, ..., An);

doctrine Combined = effects Base { E1, E2, ... };
```

- `doctrine_template` must contain exactly one inner `doctrine` block. Instantiation
  substitutes template parameters into **identifiers** (doctrine, mode, type, generator,
  and term/box names), but **does not** substitute type variable binders or `RPTVar`s.
  The resulting doctrine name is overridden to the instantiation name.
- `effects` expands to iterated pushouts over a base doctrine:
  - empty list ⇒ `Combined extends Base`;
  - singleton ⇒ `Combined extends E1`;
  - otherwise, compute `Combined__step1 = pushout E1.fromBase E2.fromBase`,
    then `Combined__stepk = pushout Combined__step(k-1).glue E(k+1).fromBase`,
    and finally `Combined extends Combined__step(n-1)`.
  Each `Ei` must provide a mode‑preserving `Ei.fromBase : Base -> Ei`.

### 6.2 Morphisms

```
morphism <Name> : <Src> -> <Tgt> where {
  mode <SrcMode> -> <TgtMode>;
  modality <SrcModName> -> <TgtModExpr>;
  attrsort <SrcSort> -> <TgtSort>;
  type <SrcType>(<tyvar> [, ...]) @<Mode> -> <TgtTypeExpr> @<Mode>;
  gen  <SrcGen>  @<Mode> -> <DiagExpr>;
  coercion;
  policy <RewritePolicy>;
  fuel <N>;
}
```

- Every source generator must be mapped.
- Every source modality must be mapped (explicitly or by same-name default when src/tgt modes match).
- Mode mappings are optional; if omitted, each source mode maps to the same‑named target
  mode (and it is an error if that target mode does not exist).
- The mode map is total on source modes; duplicate mode mappings are rejected.
- Attrsort mappings are optional; if omitted, source sorts map to same‑named target sorts.
- Type mappings are **templates with explicit binders**: the RHS may be any type expression
  whose free variables are a subset of `{a1,...,an}`.
- Binder modes are checked against the source type's mode signature **mapped by the mode map**.
- The target `@<Mode>` on a type mapping must equal the mode map of the source type’s mode.
- When a morphism is used as a **pushout leg**, its type mappings must be **invertible renamings**
  (constructor rename + parameter permutation).
- Generator mappings must elaborate to diagrams in the target doctrine/mode `mapMode(<Mode>)`.
- Generator mappings may use target generator attribute arguments; attribute terms are
  identifiers or literals (`int`, `string`, `bool`) under the target field sorts.
- Attrsort mappings must preserve literal kinds (`int`, `string`, `bool`) when the source
  sort declares one.
- `coercion;` marks the morphism as eligible for implicit coercion paths (no change to morphism
  checking). Morphisms generated by `extends`, `pushout`, and `coproduct` are marked coercions.

### 6.3 Types and contexts

- A context is a bracketed list: `[A, B, ...]` or `[]`.
- Types are either:
  - lowercase identifiers (type variables), or
  - constructors with optional arguments, optionally qualified by mode:
    `Mode.Type(args)` or `Type(args)`, or
  - modality application:
    `mu(Type)` or composed forms such as `U.F(Type)`, and identity `id@Mode(Type)`.
- Unqualified constructors must be unique across all modes; otherwise they must be written
  with a `Mode.` qualifier.
- `mu(Type)` is interpreted as modality application when `mu` is a declared modality.

### 6.4 Diagram expressions

```
id[<Ctx>]
<GenName>{<Ty>,...}(<AttrArgs>)   -- optional type args; optional attr args
@<TermName>           -- splice a named term
box <Name> { <d> }    -- boxed subdiagram
loop { <d> }          -- feedback: connects the single output of <d> to its single input
<d1> ; <d2>           -- composition (first d1 then d2)
<d1> * <d2>           -- tensor
```

Generator calls:

- Type arguments `{...}` are optional.
- Attribute arguments `(...)` are optional syntactically, but required when the generator
  declares attributes, and disallowed when it declares none.
- Attribute arguments must be either all named or all positional:

```
<AttrArgs> ::= <AttrArg> (, <AttrArg>)*
<AttrArg>  ::= <AttrName> = <AttrTerm> | <AttrTerm>
<AttrTerm> ::= <ident> | <int> | <string> | true | false
```

- Positional attribute arguments must have exactly the declared field count.

Composition/tensor are parsed with the usual precedence (`*` binds tighter than `;`).

`@<TermName>` splices the **normalized** diagram stored by a `term` declaration. If the term’s
doctrine differs from the current doctrine, the compiler attempts to coerce it along a unique
shortest coercion path; ambiguity or absence is an error.

`loop { <d> }` requires `<d>` to have exactly one input and **at least one output**.
The **first** output port is identified with the input port (feedback); the remaining
outputs become the outputs of the looped diagram. The result has **no inputs** and
`(n−1)` outputs.

---

### 6.5 Terms

```
term <Name> where {
  doctrine <Doctrine>;
  mode <Mode>;        -- required if the doctrine has multiple modes
  surface <Surface>;  -- optional; parses with a surface definition
  uses <Iface>, ...;  -- optional; expands to default interface morphisms
  apply <Morphism>;   -- optional; may be repeated, applied in order
  policy <RewritePolicy>;
  fuel <N>;
}
---
<DiagExpr | SurfaceProgram>
```

A `term` compiles a diagram using the same pipeline as `run`, but stores the **normalized**
diagram under its name. `term` blocks do not allow `model` or `show` clauses. The stored term
remembers its doctrine and mode and can be referenced via `@<TermName>`.

### 6.6 Surfaces

Surfaces define a surface language and its
elaboration to diagrams.

```
surface <Name> where {
  doctrine <Doctrine>;
  mode <Mode>;
  lexer { ... }
  expr  { ... }
  elaborate { ... }
}
```

Surface variable-use behavior is derived from the doctrine mode structure only:

- `linear`: no drop/no duplication.
- `affine`: drop allowed (requires generator `drop` in the surface mode).
- `relevant`: duplication allowed (requires generator `dup` in the surface mode).
- `cartesian`: both allowed (requires both `dup` and `drop`).

Required structural generator names are fixed: `dup` and `drop`.

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
int         -- integer literal capture
string      -- string literal capture
bool        -- boolean literal capture
<expr>      -- expression capture
<type>      -- type capture
"literal"   -- exact token match
```

Actions construct the surface AST:

- `=> <expr>` returns the single captured expression (exactly one is required).
- `=> Ctor(a, b, ...)` builds an AST node with the captured items in order.
- Literal captures become `SALit` nodes.

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
- `@TermName` splices a previously-defined term diagram into the template.
- Template generator calls may include attribute arguments (named or positional), e.g.
  `Gen{...}(n=#hole, ...)` or `Gen{...}(...)`.

Template `@TermName` splicing is strict: the referenced term must exist and have the
same doctrine and mode as the current surface elaboration.

Template attribute terms are:

- literals (`42`, `"x"`, `true`, `false`),
- variables (`x`, interpreted as an attribute variable at the field’s expected sort),
- holes (`#name`), filled from captures:
  - literal capture -> same literal,
  - identifier capture -> string literal of the identifier text.

A constructor named `CALL` with arguments `(name, arg)` is treated as a generator
call: `name` is the generator name, and `arg` elaborates to its argument diagram.
Direct calls via `CALL` or bare identifiers cannot target generators with attributes;
those must be called from templates that explicitly provide attribute arguments.

#### Binding rules + structural discipline

Binding is inferred by syntax:

- If a constructor captures `ident` immediately followed by `<type>`, it is an
  **input binder**. The last expression capture is the body.
- Otherwise, if it captures an `ident` and **at least two** expression captures,
  it is a **value binder**. The first expression after the ident is the bound
  value; the last expression capture is the body.

Elaboration semantics:

- Input binders introduce a fresh input port of the annotated type.
- Variable occurrences elaborate to wire references to that port.
- Variable uses are checked against the discipline:
  - **linear**: exactly once (0 or >1 uses is an error).
  - **affine**: at most once; 0 uses insert `drop`.
  - **relevant**: at least once; multiple uses insert `dup`
    (left‑associated duplication).
  - **cartesian**: any number of uses; 0 uses insert `drop`,
    >1 uses insert `dup` (left‑associated duplication).

### 6.7 Models

```
model <Name> : <Doctrine> where {
  default symbolic;
  op <GenName>(args...) = <expr>;
}
```

Models use the same expression language for generator clauses. Evaluation is defined
only for **closed** diagrams (no boundary inputs/outputs).

For each `op Gen(args...)` clause, arguments are passed in this order:

1. generator attributes (field declaration order),
2. wire inputs (generator domain order).

**Cycles are supported** using SCC‑based evaluation:

- Acyclic components are evaluated concretely via the model clauses.
- Cyclic components are evaluated symbolically with placeholders `$pN`, producing a
  `letrec` wrapper in the output value:

  ```
  [letrec, [[ $p0, expr0 ], [ $p1, expr1 ], ...], body]
  ```

Generators (including `dup`, `drop`, and `swap`) are interpreted only via the model
clauses or the model’s default behavior; no special built‑ins are assumed.
Attribute variables evaluate to atoms rendered as `name:Sort`.

---

## 7. Runs

Runs are configured through `run_spec` and `run`.

```
run_spec <Name> [using <Base>] where { <RunItems> }
[--- <ExprText> ---]

run <Name> [using <Spec>] [where { <RunItems> }]
[--- <ExprText> ---]
```

`<RunItems>` are the same run configuration clauses (`doctrine`, `mode`, `surface`,
`model`, `apply`, `uses`, `policy`, `fuel`, `show ...`).

Resolution semantics:

1. Resolve `run_spec` inheritance by following `using` recursively.
2. Reject cycles with error `run_spec inheritance cycle: ...`.
3. Merge parent -> child at each step.
4. When a `run` uses a spec, merge resolved spec -> run body.

Merge policy:

- Singleton fields (`doctrine`, `mode`, `surface`, `model`, `policy`, `fuel`):
  child overrides parent when present.
- List fields (`uses`, `apply`, `show`):
  concatenate in implemented order: parent list first, then child list.
- Expression:
  - use the run body if present;
  - otherwise inherit the first available body from the resolved `run_spec` chain;
  - if no body exists after merge, error `run: missing expression`.

Execution pipeline for the effective run configuration:

1. Parse either a diagram expression or a surface program.
2. Elaborate against the chosen doctrine/mode.
3. Apply `uses` morphisms and then `apply` morphisms in order.
4. If needed, coerce to the declared doctrine along a unique shortest coercion path.
5. Normalize (policy default: `UseStructuralAsBidirectional`).
6. Optionally evaluate via the selected model (requires closed diagram).
7. Optionally check coherence and render its report.
8. Print requested outputs.

`show cat` is currently not supported.

Example (shared expression via `run_spec`):

```llang
import "../../lib/codegen/arith_literals.llang";

run_spec Base where {
  doctrine Arith;
  mode M;
  surface ArithInfix;
  show value;
}
---
2 + 3 * 4
---

run eval using Base where { model Eval; }
run rpn using Base where { model RPN; }
run lisp using Base where { model Lisp; }
run prefix using Base where { model Prefix; }
run infix using Base where { model Infix; }
```
