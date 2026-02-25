# llang Specification (Current)

This document describes the current kernel and DSL surface used by this repository.

## 1. Core Model

A doctrine is the kernel object:

- modes and modalities (`mode`, `modality`, `mod_eq`, `mod_transform`)
- objects and generators
- rewrite cells (`computational` and `structural`)
- modality actions (`action`)
- schema obligations (`obligation`)

There is no `structure` keyword and no `adjunction` keyword.

## 2. Classification and Universes

### 2.1 Classification Edges

A doctrine SHALL determine a classification graph over modes.
The classification graph MAY be empty.

A classification edge is written:

- `mode M classifiedBy K via U;`

This SHALL mean:

- objects of mode `M` are represented by code terms in mode `K`,
- the classifier object is `U` (an object of mode `K`),
- a code for an object of `M` SHALL be well-formed as a term of `K` with classifier `U`,
- definitional equality of objects in `M` SHALL be definitional equality of their codes in `K`.
- the edge is a directed dependency `M ▷ K`.

Current kernel restriction:

- each mode has at most one `classifiedBy` edge.
- `cdTag` is parsed and stored but has no kernel semantics in the current implementation (reserved for a later phase).

### 2.2 Objects and Codes

Kernel notion:

- an object of mode `M` in context `Γ` is represented by a code term `c` in classifier mode `K` such that `Γ ⊢ c : U` in `K` for the edge `M classifiedBy K via U`.

Implementation-facing mode split:

- every object stores an **owner mode** (`objOwnerMode`) and a **code term** (`objCode`),
- owner mode is the mode checked at diagram boundaries and term-sort boundaries,
- classifier/code mode is used to resolve constructors and choose code-side normalization/equality behavior.

Surface notion:

- the surface language may continue to use the word "type", but kernel checks MUST distinguish object identity from code representation.
- a surface "type variable" elaborates to a code metavariable (`CTMeta`) whose sort is derived from the classifier universe object `U` for the owner mode.
- the stored sort of that metavariable is exactly `U` (in classifier mode); owner mode is carried by the enclosing `Obj`, not by rewriting `U`'s owner.
- Strategy A is enforced: there is no implicit fallback universe/object sort for code metavariables.

If a mode has no explicit classification edge, object well-formedness is determined by that mode's declared object formers and object-parameter rules.

Universe well-formedness (minimum kernel check):

- for `mode M classifiedBy K via U;`, the universe object MUST satisfy `objOwnerMode(U) = K`.

### 2.3 Object Definitional Equality

For a fixed declared definitional fragment `Def(K)` of classifier mode `K`:

- `A ≡ B : Obj(M)` iff `NF_K(code(A)) = NF_K(code(B))`.

`NF_K` SHALL denote the normalization engine selected by `Def(K)`.

Algorithmic rule:

- to check `A ≡ B` in mode `M`, normalize `code(A)` and `code(B)` in classifier mode `K`, then compare normalized syntax.

### 2.4 Allowed Classification Graphs

- self-classification edges (`K classifiedBy K via U`) are permitted;
- layered classification is permitted (for example `Tm classifiedBy Ty` and `Ty classifiedBy Kd`);
- classification graphs MUST NOT contain cycles of length greater than 1;
- longer cycles are rejected unless explicit universe levels are provided.

### 2.5 Constructor Source

An object former for mode `M` SHALL be any term former in classifier mode `K` whose result is a code of `U` (up to definitional equality in `K`).

Current elaboration rule:

- when elaborating an object expression with expected owner mode `M`, unqualified constructors are resolved only in classifier mode `K = classifier(M)`,
- a qualified constructor `Q.C` is accepted only when `Q = K`; other qualifiers are rejected as wrong-classifier references.
- in the current kernel cut, constructor-eligible generators must have:
  - no attrs,
  - no diagram-domain inputs,
  - exactly one codomain object, definitionally equal to `U`.
- if `U` normalizes to a nullary classifier constructor `K.C`, `C` is also included as an implicit zero-argument constructor.
- constructor signatures are derived from the generator parameter telescope order (`gdParams`), not from split ty/tm lists.
- constructor term-parameter sorts are currently required to be closed with respect to the generator's type parameters.
- in surface type annotations, constructor parameters of kind `TPS_Tm` are currently not supported; term-indexed arguments must be expressed through core/kernel paths (not direct surface syntax).
- legacy `dTypes`/`TypeSig` tables have been removed from kernel and tests; constructor resolution/typechecking is fully driven by derived constructor tables from classifier generators.

### 2.6 Worked Examples

Two-layer example (`Ty` classifies `Tm`):

- codes in `Ty`: `Unit : U`, `Arr : U × U -> U`,
- objects of `Tm` include codes such as `Arr(Unit, Unit)`,
- `Tm`-object equality is checked by normalizing those `Ty` codes and comparing normal forms.

Three-layer example (`Kd` classifies `Ty`, `Ty` classifies `Tm`):

- `mode Kd classifiedBy Kd via Kd.U_Kd;`
- `mode Ty classifiedBy Kd via Kd.Star;`
- `mode Tm classifiedBy Ty via Kd.U_Ty;`
- classifier dependency order is `Kd` before `Ty` before `Tm`;
- constructor lookup for `Tm` resolves in classifier mode `Ty`,
- constructor lookup for `Ty` resolves in classifier mode `Kd`.

Allowed patterns include:

- `Ty classifiedBy Ty via Ty.U;`
- `Tm classifiedBy Ty via Ty.U;`
- layered chains such as `Kd -> Ty -> Tm` (acyclic except self edges).

Rejected:

- `A classifiedBy B via B.U;` with `B classifiedBy A via A.U;` (non-self cycle).

### 2.7 Classifier Dependency Order

For doctrine validation and later normalization/unification environment construction, the kernel SHALL compute a classifier dependency order `order : [ModeName]` such that:

- if `M classifiedBy K` and `M != K`, then `K` appears before `M` in `order`.

### 2.8 Pending Universe Resolution (Current)

During elaboration, a `classifiedBy ... via ...` universe expression can be temporarily unresolved.

Current behavior:

- if the raw universe is not immediately classifiable as a simple name/nullary constructor, elaboration stores a temporary pending universe marker;
- pending universes are resolved after initial mode/generator collection, using object elaboration with constructor tables from `deriveCtorTablesForElab`;
- this elaboration-time constructor-table path derives tables for resolvable classifier dependencies first, tolerates forward references to not-yet-declared classifier modes, then adds provisional tables for owner modes whose universes are still pending;
- after pending resolution, normal doctrine validation still uses full constructor-table derivation and rejects unresolved or inconsistent universes.

This means complex universe expressions (including constructor applications with arguments) are supported in the current elaboration pipeline; they are not restricted to names/nullary constructors.

### 2.9 Comprehension Declarations (Current Cut)

The DSL supports:

- `comprehension M where { ctx_ext = g1; var = g2; reindex = g3; };`

Current kernel checks:

- `M` must already have `classifiedBy`.
- each referenced generator must exist in mode `M`.
- referenced generators must be term generators (not constructor-like declarations).
- each referenced generator must have:
  - no attrs,
  - exactly one plain input port (no binder input),
  - exactly one output.

Current generated-obligation behavior:

- generated comprehension obligations are installed only when a `comprehension` declaration is present.
- in the current cut, obligations are generated for:
  - binder slots on generators with binder inputs (including mixed plain+binder domains) generate full law families (`id_dom`, `id_cod`, `comp_dom`, `comp_cod`, `nat`),
  - constructor term-argument slots only when:
    - the slot's term sort owner mode equals the classified mode,
    - and the generated law side follows the slot boundary side:
      - dom-side slots generate dom laws (`id_dom`, `comp_dom`) only,
      - cod-side slots generate cod laws (`id_cod`, `comp_cod`) only.
- generated obligation names use the `__comp/<mode>/<gen>/<slotpath>/...` scheme.
- generated law families in the current cut are:
  - `id_dom`
  - `id_cod`
  - `comp_dom`
  - `comp_cod`
  - `nat`

Current policy note:

- every classified mode must provide a `comprehension` declaration.

## 3. Definitional Fragment

Every mode SHALL declare a definitional fragment used for kernel definitional equality.

Current required fragment:

- first-order TRS normalization compiled from admissible computational rules and eligible generators.

Admissibility requirements:

- rewrite compilation must remain in the first-order term fragment,
- termination MUST be proven (SCT),
- critical pairs MUST be joinable by normalization.

A doctrine MUST either:

- declare the fragment explicitly per mode, or
- satisfy kernel derivation rules (computational rules + eligible generators) and pass admissibility checks.

Future fragments (for example NbE) are permitted by this spec but are not required in the current implementation.

### 3.1 Kernel DefEq API (Current)

Current implementation centralizes normalization/equality entrypoints in `Strat.Poly.DefEq`:

- `normalizeTermDiagram`
- `normalizeObjDeep` / `normalizeObjDeepWithCtx`
- `normalizeCodeTermDeepWithCtx`
- `defEqObj`
- `defEqTermDiagram`

Per-mode definitional data is represented by `DefFragment`:

- `dfMode`: mode name
- `dfFuns`: admissible term symbols in that mode
- `dfRules`: admissible computational rules in that mode
- `dfTRS`: compiled TRS used by normalization/equality

`normalizeCodeTermDeepWithCtx` and `normalizeTermDiagram` are the shared normalization services used by object equality (`defEqObj`) and term equality (`defEqTermDiagram`).

## 4. Doctrine Layer

Key records:

- object signatures are parameterized by mode and object parameters (`TPS_Ty`, `TPS_Tm`)
- `GenDecl` supports metavariables with two roles:
  - code metavariables (type-level) represented in object codes as `CTMeta`
  - term metavariables represented on term edges as `PTmMeta`
  Surface syntax may still call code metavariables "type variables".
- `Cell2` rewrites diagrams
- `ModAction` stores per-modality generator images
- `ObligationDecl` stores named equations checked on `implements`

Validation checks:

- mode/modality well-formedness
- object/generator/rule well-formedness
- action coverage and mode correctness
- obligation diagrams are valid and boundary-compatible

## 5. Diagram Layer

A `Diagram` is a typed port graph with edge payloads:

- `PGen`
- `PBox`
- `PFeedback`
- `PSplice`
- `PTmMeta`
- `PInternalDrop` (kernel-internal, non-surface payload)

Matching and rewriting are structural and mode-aware.

### 5.1 Isomorphism

Structural diagram isomorphism (`diagramIsoEq`) uses:

- fixed boundary positions (`dIn` index-to-index, `dOut` index-to-index)
- syntactic port-type equality
- ordered incidence lists (`eIns`, `eOuts`) preserved positionally
- payload-structural equality:
  - `PGen`: generator name, attrs, binder args
  - `PBox`: inner diagram only (box name is annotation)
  - `PFeedback`: inner diagram
  - `PSplice`: binder metavariable
  - `PTmMeta`: metavariable identity by `(name, scope, sort)`
  - `PInternalDrop`: exact constructor match

### 5.3 Meta Substitution

Kernel substitution is a single metavariable substitution environment.

- code metavariables map to object/code terms
- term metavariables map to term diagrams

Well-formedness invariant:

- a metavariable is only instantiated in the syntactic category where it occurs; kind mismatches are rejected as kernel errors.
- code-metavariable scope checks are performed against the classifier-mode slice of the telescope (`modeClassifierMode owner`), not the owner-mode slice.

### 5.2 Canonical Form

Canonicalization reduces a diagram to a colored graph encoding:

- vertices for boundary positions, ports, edges, and ordered input/output slots
- edges for boundary attachments and slot incidence
- colors enforcing boundary index, slot index/direction, port type, and edge payload shape

Canonical labeling picks a deterministic representative and rebuilds the diagram with canonical `PortId`/`EdgeId` assignment. Canonization is recursive through payload-contained diagrams (`PBox`, `PFeedback`, `BAConcrete`).

Port labels are currently treated as metadata for structural isomorphism/canonization by default (ignored as equality keys), while still being stored on diagrams.

## 6. Modalities

`mod_eq` gives oriented modality-expression equations.

`mod_transform t : mu => nu [witness g];` adds a directed 2-cell witness between modality
expressions. It does not contribute to definitional equality and does not rewrite `ModExpr`.

Current witness constraints:

- if `witness` is omitted, it defaults to the transform name
- witness generator mode must be the target mode of `mu`/`nu`
- witness generator must have exactly one object variable `A` in the source mode of `mu`/`nu`
- witness generator must have no term variables and no attributes
- witness generator boundary must be exactly one input and one output with type
  `mu(A) -> nu(A)` after normalization

`action <ModName> where { gen g -> <diag> }` defines the functorial map on generator edges.

`map[<ModExpr>](<DiagExpr>)` elaborates by applying declared actions along the composed modality expression.

### 6.1 Classified Modalities (Current Cut)

Classifier lift requirement:

- for every modality `mu : M -> N` where both `M` and `N` are classified modes, a classifier lift must be available from `classifier(M)` to `classifier(N)`;
- an explicit `lift_classifier mu = <modexpr>;` declaration is required unless both modes are self-classified along `mu` (in that case the same modality path is used implicitly).

Universe compatibility rule:

- let `U_M` be the universe of `M`, `U_N` the universe of `N`, and `lift(mu)` the classifier lift for `mu`;
- doctrine validation requires `lift(mu)(U_M) ≡ U_N` by classifier-mode definitional equality.

## 7. Schemas and Obligations

A schema is an ordinary doctrine used as an interface.

`implements IFace for Target using m` checks source/target compatibility and then checks each obligation from `IFace` after translating both sides through morphism `m`.

Obligation success is proof-carrying:

- a checker accepts an equality when it has a `JoinProof` and replay/verification succeeds
- automated search (`auto`) may try to synthesize a `JoinProof` within a tooling budget
- if automation fails to find a proof, result is `undecided` (not “false”)

## 7.1 Proof-Carrying Equality Checking

For morphism law checking, action semantics, obligation discharge, and coherence obligations:

- automation can search for join proofs
- kernel/checker code validates proofs by replaying certified rewrite steps and checking join endpoints
- “unknown within budget” is reported as undecided, not as a semantic counterexample

Budgets are tooling-level search parameters (`SearchBudget`), not doctrine/morphism/obligation data.
`sbTimeoutMs` is interpreted as a real wall-clock timeout for auto-proof search.

## 7.2 Generated Beck-Chevalley Obligations (Current Cut)

Generated Beck-Chevalley obligations are installed for modalities that satisfy all of:

- source/target modes are classified and both have comprehension declarations,
- a classifier lift exists for the modality,
- an action is declared for the modality.

For each relevant slot on each source-mode generator (using the same slot-profile gating as comprehension obligations), the kernel generates:

- dom-side equation:
  - `map[mu](lift_dom(reindex_src) ; @gen) == lift_dom(reindex_tgt) ; map[mu](@gen)`
- cod-side equation:
  - `map[mu](@gen ; lift_cod(reindex_src)) == map[mu](@gen) ; lift_cod(reindex_tgt)`

Current naming scheme:

- generated names are `__bc/<mod>/<srcMode>/<gen>/<slotpath>/dom` or `.../cod`.

## 8. DSL Summary

Doctrine items:

- `mode`, `modality`, `mod_eq`, `mod_transform`
- `action`, `obligation`
- `attrsort`, `data`, `gen`, `rule`

Top-level functor/apply items:

- `doctrine_functor F(A : SA, B : SB, ...) where { ... }`
- `doctrine New = apply F to Target using { A = implA; B = implB; ... };`

Functor namespace/use rules:

- parameter-provided names must be referenced as `Param::Name` inside functor bodies
- parameter mapping keys in `using { ... }` must exactly match the functor parameter set
- parameter schemas are signature-only: modes/modalities/`mod_eq`, attrsort/gen/data declarations only

Removed legacy items:

- `index_mode`, `index_fun`, `index_rule`
- `structure ... = ...`
- `adjunction F dashv U`

## 9. Morphisms and Pushouts

Morphisms map modes/modalities/types/generators and transport diagrams.
Pushout/coproduct construction remains available and merges doctrine content with compatibility checks.
`apply` computes a right-biased pushout where target names are preserved and colliding
functor-body declarations are prefixed/freshened.
The collision prefix is derived from the functor name (for example `F_...`).

Collision renaming during `apply` covers:

- modes
- modalities
- attr sorts
- types
- generators
- cells
- obligations (by `obName`)
- `mod_transform` names

Mode-theory compatibility is checked via morphism law preservation:

- each source `mod_eq` must remain equal after morphism mapping/normalization in the target mode theory

Classification-preserving morphism checks are strict:

- for each source classified mode `M`, if `M' = morModeMap(M)`, target classification must exist for `M'` and satisfy classifier-edge commutation:
  `classifier(M') = morModeMap(classifier(M))`
- mapped universes must be definitionally equal in the target classifier theory
- comprehension witness generators (`ctx_ext`, `var`, `reindex`) must be preserved exactly under `morGenMap`
- classifier-lift coherence must hold for each mapped modality:
  mapped source lift and target-computed lift of the mapped modality expression must normalize to the same `ModExpr`

Pushout classification reconciliation is strict:

- if both branches classify the same merged mode, classifiers must agree after renaming
- comprehension declarations must match (or both be absent)
- universes must be definitionally equal in the merged classifier theory
- otherwise pushout/apply fails with an explicit classification-conflict error (no silent overwrite path)

`apply` also inserts coercion morphisms:

- `New.inl : Body -> New`
- `New.inr : Target -> New`
- `New.glue_<Param> : SchemaParam -> New`

Morphism equation checking uses proof search over join proofs with tooling budgets.
DSL morphism blocks may set optional:

- `max_depth`
- `max_states`
- `timeout_ms`

If search cannot produce a proof within budget, the result is reported as `undecided`
with a concrete limit reason.

## 10. Surface Elaboration

Surface elaboration is capability-driven:

- duplication requires a resolved unary copy capability (`[a] -> [a, a]`) from default `implements` instances for the target doctrine
- dropping requires a resolved unary discard capability (`[a] -> []`) from default `implements` instances for the target doctrine

No discipline lattice is consulted.

## 11. Temporary Restrictions

See `RESTRICTIONS.md`.
