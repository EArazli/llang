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

Types are mode-indexed and support an explicit index world. The kernel uses:

```
TypeRef  = { trMode :: ModeName, trName :: TypeName }
TyVar    = { tvName :: Text, tvMode :: ModeName }
IxVar    = { ixvName :: Text, ixvSort :: TypeExpr, ixvScope :: Int }
IxTerm   = IXVar IxVar | IXBound Int | IXFun IxFunName [IxTerm]
TypeArg  = TAType TypeExpr | TAIndex IxTerm
TypeExpr = TVar TyVar | TCon TypeRef [TypeArg] | TMod ModExpr TypeExpr
Context  = [TypeExpr]
```

- Type constructors carry mixed arguments: type arguments and index arguments.
- `IXVar` are index metavariables, unified during typing/matching.
- `IXBound i` are rigid bound indices introduced only by binder slots (`i` is de Bruijn-style).
- `typeMode` is computed from the constructor/modality structure and ignores index arguments.
- Type-level definitional equality is strictly:
  1. mode-theory normalization (modalities),
  2. index-term normalization in the doctrine’s index theory.
  Diagram reduction is never used for type equality.
- Binder lists reject duplicate variable names within their namespace.

### 1.3 Type unification

The kernel uses a combined substitution:

```
Subst = { sTy :: Map TyVar TypeExpr, sIx :: Map IxVar IxTerm }
```

and a combined theory parameter:

```
TypeTheory = { ttModes :: ModeTheory, ttIndex :: Map ModeName IxTheory, ttIxFuel :: Int }
```

with default `ttIxFuel = 200`.

Unification is kind-directed by constructor signatures:

- `PS_Ty` positions unify as types.
- `PS_Ix sort` positions unify as index terms at expected sort `sort`.

Index unification (`unifyIx`) is scoped first-order unification:

- substitutes and normalizes both sides first,
- unifies structurally (`IXBound` rigid, `IXFun` pointwise),
- may bind only flex metas,
- enforces occurs check,
- enforces scope safety: if `v := t`, every `IXBound i` in `t` must satisfy `i < ixvScope v`.
  Scope-0 metas cannot be solved with terms containing bound indices.

All substitution application re-normalizes modalities and index terms.

---

## 2. Doctrines

A **polygraphic doctrine** packages:

- a mode theory,
- an index world (`index_mode`, per-mode index theory),
- an attribute-sort table (`AttrSort -> AttrSortDecl`),
- a per-mode type constructor table (`TypeName -> TypeSig`),
- generator declarations, and
- 2‑cells (rewrite rules).

Where:

```
ParamSig     = PS_Ty ModeName | PS_Ix TypeExpr
TypeSig      = { tsParams :: [ParamSig] }
IxTheory     = { itFuns :: Map IxFunName IxFunSig, itRules :: [IxRule] }
IxFunSig     = { ifArgs :: [TypeExpr], ifRes :: TypeExpr }
IxRule       = { irVars :: [IxVar], irLHS :: IxTerm, irRHS :: IxTerm }
AttrLitKind  = int | string | bool
AttrSortDecl = { asName :: AttrSort, asLitKind :: Maybe AttrLitKind }
```

- `PS_Ix sort` parameters must use index sorts (`typeMode sort ∈ dIndexModes`).
- `index_fun`/`index_rule` are grouped per index mode by result sort mode.
- `index_rule` matching is first-order on index terms only (no diagram rewriting).
- Attribute sorts may be declared with or without a literal kind.
- If an attribute sort has no literal kind (`asLitKind = Nothing`), literals of that sort are rejected.

### 2.1 Generators

A generator declaration is:

```
BinderSig   = { bsIxCtx :: [TypeExpr], bsDom :: Context, bsCod :: Context }
InputShape  = InPort TypeExpr | InBinder BinderSig
GenDecl     = { name, mode, gdTyVars, gdIxVars, attrs, dom :: [InputShape], cod }

attrs :: [(AttrName, AttrSort)]
```

- `gdTyVars` are type metas in declarations, `gdIxVars` are index metas with `ixvScope = 0`.
- Plain input ports are `InPort`.
- Binder slots are `InBinder` with:
  - `bsIxCtx`: bound index sorts (index modes only),
  - `bsDom`: term-bound input ports for the binder body,
  - `bsCod`: binder body codomain.
- Types in `bsDom`/`bsCod` may use `IXBound i` referencing `bsIxCtx[i]`.
- Binder names are surface metadata only and are not stored in kernel objects.
- `gdPlainDom` extracts only `InPort` entries (a convenience projection for the port-only input domain).
- Attribute field names are distinct within a generator.
- Every attribute field sort must exist in `dAttrSorts`.
- Generator instances in diagrams carry exactly the declared attribute fields.

### 2.2 2‑cells

A 2‑cell is a named rewrite equation between diagrams:

```
Cell2 = { name, class, orient, c2TyVars, c2IxVars, lhs, rhs }
```

- `lhs` and `rhs` are diagrams of the same mode.
- Their boundaries must unify (same context lengths; types unify under a substitution).
- `c2TyVars` and `c2IxVars` are binders (α‑irrelevant, duplicate names rejected).

### 2.3 Validation

`validateDoctrine` checks:

- referenced modes exist,
- each `index_mode` names an existing mode,
- index function/rule sorts live in index modes and are mode-consistent by result sort,
- attribute-sort declarations are well-formed,
- type constructor arities and mixed parameter kinds match,
- generator domains/codomains are well‑formed,
- binder slot signatures are well-formed (`bsIxCtx` index-only, bound indices in range),
- generator attribute fields are well-formed,
- 2‑cell diagrams validate and have compatible boundaries,
- all type variables used are declared in the generator or cell scope,
- all index variables used are declared in scope,
- every cell satisfies both variable disciplines:
  `freeTyVars(RHS) ⊆ freeTyVars(LHS)` and
  `freeIxVars(RHS) ⊆ freeIxVars(LHS)` and
  `freeAttrVars(RHS) ⊆ freeAttrVars(LHS)`,
- binder metas satisfy `binderMetas(RHS) ⊆ binderMetas(LHS)`,
- attribute-variable name/sort hygiene holds (the same variable name cannot appear at multiple sorts).

---

## 3. Diagrams: open hypergraphs

### 3.1 Representation

A diagram is an **open directed hypergraph** with **ports as vertices** and generator instances as hyperedges:

- **Ports** have types.
- **Edges** have ordered input ports and ordered output ports; each edge payload is either
  a generator instance, a box, a feedback edge, or a splice edge.
- **Boundary** consists of ordered input ports and ordered output ports.
- **Index context** `dIxCtx :: [TypeExpr]` stores bound index sorts in scope.
- **Linearity invariant**: each port has at most one producer and at most one consumer.
- **Cycles are allowed**: diagrams need not be acyclic, as long as linearity and boundary
  invariants hold.

Generator payloads carry attributes and binder arguments:

```
BinderArg   = BAConcrete Diagram | BAMeta BinderMetaVar
EdgePayload = PGen GenName AttrMap [BinderArg] | PBox BoxName Diagram | PFeedback Diagram | PSplice BinderMetaVar
AttrMap     = AttrName -> AttrTerm
AttrTerm    = ATVar AttrVar | ATLit AttrLit
AttrVar     = { name :: Text, sort :: AttrSort }
AttrLit     = Int | String | Bool
```

Rules for index context:

- top-level/normal term diagrams use `dIxCtx = []`,
- binder-argument diagrams must use the slot’s `bsIxCtx`,
- boxes do not bind indices (`PBox` inner `dIxCtx` must equal outer `dIxCtx`),
- any `IXBound i` in diagram port types must satisfy `i < length dIxCtx`.

For a **box** edge, the nested diagram must:

- share the outer diagram’s mode, and
- share the outer diagram’s `dIxCtx`,
- have input/output boundary types matching the edge’s input/output port types.
- recursively carry generator payload attributes by the same representation.

For a **feedback** edge, the nested diagram must:

- share the outer diagram’s mode and `dIxCtx`,
- have exactly one input and at least one output,
- have no outer inputs on the feedback edge (`eIns = []`),
- with inner outputs `(stateOut : outsTail)` and the single inner input `stateIn`:
  `type(stateIn) == type(stateOut)`,
- and the feedback edge outputs must match `outsTail` (in order and type).

The internal representation (`Strat.Poly.Graph`) stores:

- port types, producer/consumer incidence maps,
- port labels (`dPortLabel : PortId ↦ Maybe Text`),
- edge table, and
- boundary port lists.

Port labels are metadata only:

- they do not affect diagram equality, matching, or coherence checks,
- they are carried through structural operations, and
- surface input/value binders assign labels to the corresponding ports.

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
Match = { mPorts, mEdges, mTySub, mAttrSub, mBinderSub }
```

Constraints:

- generator labels must match,
- ordered incidences must match,
- diagram `dIxCtx` must agree,
- port types unify under combined type/index substitution `mTySub`,
- generator attribute key sets must match,
- corresponding generator attribute terms unify under `mAttrSub`,
- binder argument arities must match,
- binder metas are valid only at binder-argument positions:
  - `BAMeta X` captures a concrete binder diagram on first use,
  - repeated `BAMeta X` requires iso-equality with the existing capture,
  - binder metas outside binder-arg positions are rejected by elaboration,
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
3. Instantiate `R` by type/index and attribute substitutions.
4. Substitute binder metas in RHS binder arguments using `mBinderSub`.
5. Expand splice edges `PSplice X` in RHS by grafting captured diagram `mBinderSub[X]`:
   - require exact `dIxCtx` equality between captured diagram and splice context,
   - require captured boundary equals splice edge boundary,
   - remove splice edge,
   - insert shifted captured diagram,
   - merge splice boundary ports with captured boundary ports.
6. Insert the resulting fresh RHS and glue its boundary to the matched boundary ports.

**Empty‑LHS rules are disallowed.** Rules must match at least one edge.

`PSplice` is rejected in:

- term/evaluation diagrams,
- rewrite-rule LHS,
- any context other than rule RHS elaboration.

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
- a **mode‑indexed generator map** (`(ModeName, GenName) ↦` diagram template + binder-hole signatures),
- an equation-check mode (`all | structural | none`),
- rewrite policy and fuel for equation checking.

### 5.1 Applying a morphism

To apply `F` to a diagram:

1. Map the diagram mode using the mode map, and map all port types using the type map
   templates (type‑variable modes are mapped by the mode map; unmapped constructors keep
   their name and only their mode is translated).
2. Map attribute-variable sorts via the attribute-sort map.
3. For each edge in source mode `m`, instantiate the generator mapping (using unification
   to recover type/index parameters and attribute substitutions), then instantiate binder holes
   (`?b0..?b(k-1)`) with the source edge’s mapped binder arguments and apply it in target mode `mapMode(m)`.
4. Splice the mapped diagram into the host by boundary identification.

### 5.2 Morphism checking

Source obligations are selected by `check`:

- `check all` (default): all source 2-cells are obligations.
- `check structural`: only source `rule structural` cells are obligations.
- `check none`: skip equation-preservation obligations.

For each selected source 2‑cell `L == R`:

1. Translate both sides under `F`.
2. Normalize in the target doctrine (fuel‑bounded) using the morphism `policy`/`fuel`.
3. If both normalize, require syntactic equality.
4. Otherwise, use `joinableWithin` under the target rewrite system.

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
  index_mode <ModeName>;
  structure <ModeName> = linear | affine | relevant | cartesian;
  modality <ModName> : <ModeName> -> <ModeName>;
  mod_eq <ModExpr> -> <ModExpr>;
  adjunction <ModName> dashv <ModName>;
  attrsort <SortName> [= int | string | bool];
  index_fun <IxFun>(x1:Sort1, ..., xn:SortN) : SortR @<ModeName>;
  index_rule <IxRule>(x1:Sort1, ..., xn:SortN) : <IxExpr> -> <IxExpr> @<ModeName>;
  type <TypeName> (<param> [, ...]) @<ModeName>;
  gen  <GenName>  (<param> [, ...]) [ { f1:S1, ..., fk:Sk } ] : <InputShapes> -> <Ctx> @<ModeName>;
  rule <class> <RuleName> <orient> (<param> [, ...]) : <Ctx> -> <Ctx> @<ModeName> =
    <DiagExpr> == <DiagExpr>;
}
```

- Parameters are mixed:
  - type param: `a` or `a@Mode`,
  - index param: `n : Sort`.
- Binder lists may be empty or omitted when no parameters are needed.
- `index_mode` marks which modes are valid index modes.
- `index_fun`/`index_rule` must be mode-consistent with their result sort mode.
- `structure` can only upgrade discipline according to the partial order
  `linear <= affine <= cartesian` and `linear <= relevant <= cartesian`.
- For modes requiring structural operators, `dup`/`drop` are fixed generator names and
  must have plain port domains only (no binder slots).
- Modality expressions use:
  - `id@M` for identity on mode `M`.
  - `U.F` for composition (`U ∘ F`, rightmost applies first).
- `mod_eq` rules are oriented rewrites and must be strictly length-decreasing in modality-path length.
- `adjunction F dashv U` requires opposite directions and auto-generates
  `unit_F`/`counit_F` generators with the expected modality-typed boundaries.
- `attrsort S = int|string|bool;` declares a literal-admitting sort.
- `attrsort S;` declares a sort with no literal kind (literals are rejected at that sort).
- Generator attribute blocks `{ ... }` are optional; when present, each entry is `field:Sort`.
- Generator domains are input-shape lists:
  - plain ports: `A`,
  - binder slots: `binder { v1:T1, ..., vk:Tk } : [Cod...]`.
  Binder vars in the generator mode become `bsDom`; vars in index modes become `bsIxCtx`.

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
- `pushout` requires morphisms that are:
  - mode-preserving (the mode map is identity),
  - modality-preserving (the modality map is identity),
  - between doctrines with identical mode theories (same modes, modalities, `mod_eq`, and adjunction declarations).
- Pushout does not currently merge mode theories.
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
  check all | structural | none;
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
- Generator mapping boundaries are checked at morphism definition time by unifying the
  elaborated image boundary against the mapped source generator domain/codomain.
- In morphism `gen` RHS diagrams, binder holes `?b0..?b(k-1)` refer to the source generator’s
  binder slots in declaration order.
- These holes may be used both as binder arguments (`g[?b0]`) and in `splice(?b0)`.
- Generator mappings may mention both mapped source type binders and mapped source index binders.
- Generator mappings may use target generator attribute arguments; attribute terms are
  identifiers or literals (`int`, `string`, `bool`) under the target field sorts.
- Attrsort mappings must preserve literal kinds (`int`, `string`, `bool`) when the source
  sort declares one.
- `coercion;` marks the morphism as eligible for implicit coercion paths (no change to morphism
  checking). Morphisms generated by `extends`, `pushout`, and `coproduct` are marked coercions.

### 6.3 Types and contexts

- A context is a bracketed list: `[A, B, ...]` or `[]`.
- Types and index terms share one raw expression grammar; elaboration is kind-directed.
- Bare names are not classified by lowercase/uppercase syntax.
  Resolution is by scope/signature:
  - type variable in scope,
  - type constructor (possibly qualified),
  - index variable in scope,
  - index function in expected index mode.
- Type expressions support:
  - constructors with mixed args: `T(arg1, arg2, ...)`,
  - modality application: `mu(T)` and `id@Mode(T)`,
  - bound index references in index positions: `^0`, `^1`, ...
- Index terms support:
  - variables (`n`),
  - bound indices (`^i`),
  - function applications (`add(S(n), m)`).
- Index definitional equality is normalization by `index_rule` (leftmost-outermost, declaration order, fuel-bounded).
- Unqualified constructors must be unique across modes; otherwise they require `Mode.Type(...)`.

### 6.4 Diagram expressions

```
id[<Ctx>]
<GenName>{<Arg>,...}(<AttrArgs>)[<BinderArgs>]  -- all argument groups optional
@<TermName>           -- splice a named term
splice(?X)            -- RHS-only binder splice (rule RHS / morphism gen RHS)
?x                    -- wire metavariable (fresh identity wire, inferred type)
box <Name> { <d> }    -- boxed subdiagram
loop { <d> }          -- feedback: connects the single output of <d> to its single input
<d1> ; <d2>           -- composition (first d1 then d2)
<d1> * <d2>           -- tensor
```

Generator calls:

- Constructor/index arguments `{...}` are optional (elaborated as type args then index args by declaration binder class).
- Attribute arguments `(...)` are optional syntactically, but required when the generator
  declares attributes, and disallowed when it declares none.
- Binder arguments `[...]` are optional syntactically, but required exactly when the generator
  declares binder slots.
- Each binder argument is either:
  - a concrete diagram expression,
  - or binder meta `?X` (allowed in rewrite rules and morphism `gen` RHS; morphism holes are `?b0..?b(k-1)`).
- Wire metavariables (`?x`) are linear per diagram expression: the same name may appear
  at most once in a single diagram expression.
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
`(n−1)` outputs. Elaboration encodes this as a `PFeedback` edge in the core diagram AST.

`splice(?X)` is allowed in rewrite-rule RHS and morphism `gen` RHS. In rules it requires `?X` captured in LHS binder args; in morphisms it must reference a declared hole (`?b0..?b(k-1)`).

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

Surfaces define a surface language with direct template actions and explicit binders.

```
surface <Name> where {
  doctrine <SurfaceDoctrine>;
  base <BaseDoctrine>;   -- optional; defaults to doctrine
  mode <Mode>;
  lexer { ... }
  expr  { ... }
}
```

Surface variable-use behavior is derived from the doctrine mode structure only:

- `linear`: no drop/no duplication.
- `affine`: drop allowed (requires generator `drop` in the surface mode).
- `relevant`: duplication allowed (requires generator `dup` in the surface mode).
- `cartesian`: both allowed (requires both `dup` and `drop`).

Required structural generator names are fixed: `dup` and `drop`.
Required structural generators `dup`/`drop` must declare no attributes (`gdAttrs = []`).
Required structural generators `dup`/`drop` must have no binder slots in their domain
(`gdDom` must contain only `InPort` entries).

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
ident(x)      -- identifier capture (name optional)
int(n)        -- integer literal capture (name optional)
string(s)     -- string literal capture (name optional)
bool(b)       -- bool literal capture (name optional)
<expr>        -- expression capture (positional)
<type>(ty)    -- type capture (name optional)
"literal"     -- exact token match
```

Actions are templates:

- `=> <expr>` means the first expression capture (equivalent to `$1`; exactly one `<expr>` capture required).
- otherwise the right-hand side is a diagram template.

Templates use the diagram-expression language (`id`, `box`, `loop`, `;`, `*`,
generators) plus **placeholders**:

- `$1`, `$2`, ... refer to expression captures (positional).
- `$x` uses the identifier captured by `ident(x)` as an SSA variable reference (or zero-arg generator fallback).
- `@TermName` splices a previously-defined term diagram into the template.
- `#f` in generator position means dynamic generator lookup from `ident(f)`.
- Template generator calls may include attribute arguments (named or positional), e.g.
  `Gen{...}(n=#hole, ...)` or `Gen{...}(...)`.
- Template generator calls may include binder arguments: `Gen(...)[arg1, ?meta, ...]`.

Template `@TermName` splicing is strict: the referenced term must exist and have the
same doctrine and mode as the current surface elaboration.

Template attribute terms are:

- literals (`42`, `"x"`, `true`, `false`),
- variables (`x`, interpreted as an attribute variable at the field’s expected sort),
- holes (`#name`), filled from captures:
  - literal capture -> same literal,
  - identifier capture -> string literal of the identifier text.

#### Explicit binders

Productions may declare binders explicitly:

```
bind in(varCap, typeCap, bodyHole)
bind let(varCap, valueHole, bodyHole)
```

- `bind in` introduces a fresh input wire typed by `<type>(typeCap)` and binds it to `ident(varCap)` in `bodyHole`.
- `bind let` binds `ident(varCap)` to the output of `valueHole` and makes it available in `bodyHole`.
- Hole indices are 1-based over expression captures in that production.

Elaboration semantics:

- Input binders introduce a fresh input port of the annotated type.
- Variable occurrences elaborate to wire references to that port.
- Variable uses are checked against the discipline:
  - **linear**: exactly once (0 or >1 uses is an error).
  - **affine**: at most once; 0 uses insert `drop`.
  - **relevant**: at least once; multiple uses insert a **left‑associated** `dup`
    chain: for 3 uses the inserted shape is `dup ; (dup * id[a])` (i.e. the
    second `dup` consumes the **left** output of the first `dup`).
  - **cartesian**: any number of uses; 0 uses insert `drop`,
    multiple uses insert a **left‑associated** `dup` chain: for 3 uses the
    inserted shape is `dup ; (dup * id[a])` (i.e. the second `dup` consumes
    the **left** output of the first `dup`).

#### Elaboration to base doctrine

Surface parsing elaborates to a diagram in the surface doctrine `S`. If `base D` is set
and `D != S`, elaboration runs elimination-only normalization:

1. `Σ = Gen(S, mode) \\ Gen(D, mode)` (surface-only generators).
2. `μ(diag)` = number of occurrences of generators in `Σ`
   (counting inside boxes and binder arguments).
3. Candidate rewrite rules come from `S` in the selected mode.
4. Keep only rules with strict decrease: `μ(lhs) > μ(rhs)`.
5. Normalize using only those rules with fuel `μ(initialDiag)`.
6. Require `μ(result) = 0`; otherwise elaboration fails.
7. Defensively require every generator in `result` is in `Gen(D, mode)`.

The elaboration API returns `(outputDoctrine, diagram)` where `outputDoctrine` is `S`
when no base doctrine is requested, otherwise `D` after successful elimination.

### 6.7 Models

```
model <Name> : <Doctrine> [using <BaseModel>] where {
  backend = algebra;
  backend = fold;
  fold { ... };
  default = symbolic;
  op <GenName>(args...) = <expr>;
}
```

`backend` is optional; default is `algebra`.
`backend = fold_ssa` is accepted as a deprecated alias for `backend = fold`.

Models use the same expression language for generator clauses.

#### Algebra backend (`backend = algebra`)

This is the existing evaluator:

- SCC-based value evaluation (acyclic concrete; cyclic symbolic `letrec`),
- generator arguments are `[attrs..., wireInputs...]`,
- `show value` requires no boundary inputs (`dIn = []`), but outputs may exist.

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

#### Fold backend (`backend = fold`)

`fold` renders the whole diagram to a single string (`[VString ...]`) using a
user-specified `fold { ... }` block.

Required hooks and signatures:

- `prologue_closed()`
- `epilogue_closed()`
- `prologue_open(params, paramDecls)`
- `epilogue_open()`
- `bind0(stmt)`
- `bind1(out, ty, expr)`
- `bindN(outs, decls, expr)`
- `return0()`
- `return1(out, ty)`
- `returnN(outs, decls)`

All hooks must evaluate to string values.

Optional fold settings:

- `indent = "<text>";` (default `"  "`)
- `reserved = ["..."];` (default `[]`)

Naming is deterministic and target-agnostic:

- base name comes from `dPortLabel` when present, else `pN`,
- sanitize by replacing non-`[A-Za-z0-9_]` with `_`,
- empty -> `pN`,
- leading digit gets `_` prefix,
- reserved names get `_` prefix,
- global uniqueness is enforced on final names (including prefixes), with fixed
  boundary names pre-reserved.

Evaluation uses deterministic topological edge order and rejects cycles.

Box behavior:

- boundary input/output names are fixed to outer names,
- non-boundary inner names are prefixed with deterministic `__b<edgeId>_`,
- inner code is inlined directly (no hard-coded alias statements).

Emission behavior:

- closed diagrams use `prologue_closed`/`epilogue_closed`,
- open diagrams use `prologue_open(params, paramDecls)`/`epilogue_open`,
- codomain 0 uses `bind0(stmt)`,
- codomain 1 uses `bind1(out, ty, expr)`,
- codomain >1 uses `bindN(outs, decls, expr)`,
- returns use `return0/1/N` (`""` means no emitted return line),
- expressions for codomain >0 must be single-line.

#### Model inheritance

`model Child : D using Base where { ... }` merges local overrides with `Base`.

- Base model must already be in scope.
- Base and child doctrine names must match exactly.
- Backend/default:
  - child setting overrides if present,
  - otherwise inherit base setting.
- Fold spec:
  - `indent`: child override if present; otherwise inherit base; else `"  "`,
  - `reserved`: set union,
  - hooks: inherited from base; child hook with same name overrides.
- `op` clauses:
  - inherited from base,
  - child clause with same generator name overrides,
  - otherwise child clause is appended.

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
2. Determine source doctrine/mode for elaboration:
   - If `surface` is present:
     - source doctrine is `surface.doctrine`,
     - source mode is `surface.mode`,
     - a run `mode` clause is allowed only if it is exactly `surface.mode` (otherwise error).
   - If `surface` is absent:
     - source doctrine is the run doctrine,
     - source mode is run `mode` (or inferred if the doctrine has exactly one mode).
3. Elaborate in the source doctrine/mode (surface elaboration when `surface` is set, diagram elaboration otherwise).
4. Apply `uses` morphisms and then `apply` morphisms in order.
5. If needed, coerce to the run’s target doctrine along a unique shortest coercion path.
6. Normalize (policy default: `UseStructuralAsBidirectional`).
7. Optionally evaluate via the selected model:
   - `backend = algebra`: requires closedness on inputs (`dIn = []`),
   - `backend = fold`: open diagrams are allowed.
8. Optionally check coherence and render its report.
9. Print requested outputs.

`show cat` is currently not supported.

`show value` rendering prints a singleton string value directly (no `VString` wrapper).

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
