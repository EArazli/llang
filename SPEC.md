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
- legacy `dTypes`/`TypeSig` tables have been removed from kernel and tests; constructor resolution/typechecking is fully driven by derived constructor tables from classifier generators.

### Surface elaboration of object expressions

Object expressions are the concrete syntax for *codes* in a universe object `U_m` associated to an owner mode `m`. Categorically, this corresponds to the internal language of a category-with-families / contextual category: types are elements of a universe (codes), and dependent type formers are operations on those codes parameterized by terms.

The implementation uses a single object-expression elaborator for both:
- doctrine/kernel elaboration (strict name resolution), and
- surface type annotations (implicit holes).

Elaboration is guided by the constructor’s parameter signature `TypeParamSig`:
- For a parameter `TPS_Ty`, the argument elaborates to an object expression in the classifier and is stored as an object argument (`CAObj`).
- For a parameter `TPS_Tm s`, the argument elaborates as a term of sort `s` (in the owner mode of `s`) and is stored as a term argument (`CATm`) as a `TermDiagram`.

Surface type annotations additionally adopt the following convention:
- If an identifier in type position is neither an in-scope explicit type metavariable nor a nullary type constructor in the classifier of the expected owner mode, it elaborates to an *implicit type metavariable* (a hole) of sort `U_m`.

References (standard): Dybjer, “Internal Type Theory” (categories with families); Cartmell (contextual categories / generalized algebraic theories); and the literature relating CwFs, comprehension categories, and dependent type theory.

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

Traceability note:

- canonical doctrine coverage claims are intentionally scoped to the named artifacts in `docs/CANONICAL_COVERAGE.md`.

### 2.7 Data declarations and catamorphisms

llang’s `data` declaration presents an inductive type in an owner mode (`M`) by giving its constructors. Categorically, such a presentation corresponds to an **initial algebra** for a (strictly) **polynomial endofunctor**, and the associated elimination principle is the **catamorphism** ("fold") out of that initial algebra.

#### Expansion of `data`

A declaration:

- `data T(α₁,…,αₙ) @M where { C₁ : Γ₁; …; C_k : Γ_k; }`

expands into:

1. A **type constructor** generator `T` in the **classifier mode** (`Class(M)`) returning the universe `U_M` (as already specified by the classification/universe mechanism).

2. For each constructor `C_i`, a generator in owner mode `M`:

- `C_i(α₁,…,αₙ) : Γ_i -> [T(α₁,…,αₙ)] @M`

#### Generated catamorphism `fold_T`

In addition, `data` generates a **non-dependent catamorphism** generator in owner mode `M`:

- Name: `fold_T`
- Parameters: the original type parameters `(α₁,…,αₙ)` plus an additional result type parameter `(ρ@M)`
- Plain input: one scrutinee of type `T(α₁,…,αₙ)`
- One binder input per constructor, in constructor declaration order

Formally:

- `fold_T(α₁,…,αₙ, ρ) : [ T(α₁,…,αₙ), binder{…} : [ρ] (for C₁), …, binder{…} : [ρ] (for C_k) ] -> [ρ] @M`

Each constructor binder domain is derived from the constructor’s argument context `Γ_i` by replacing each **direct recursive occurrence** of the scrutinee type `T(α₁,…,αₙ)` with the result type `ρ`. That is, if:

- `Γ_i = [A_{i1}, …, A_{im}]`

then the corresponding binder domain is:

- `Γ'_i = [A'_{i1}, …, A'_{im}]`

where:

- `A'_{ij} = ρ` if `A_{ij}` is syntactically `T(α₁,…,αₙ)`
- otherwise `A'_{ij} = A_{ij}`

No attempt is made (in this macro) to detect nested recursive occurrences under other type formers, nor to enforce strict positivity.

#### β-computation rules for `fold_T`

For each constructor `C_i`, `data` generates a **computational** (left-to-right) β-rule expressing fold-on-constructor reduction. Intuitively, this states that folding a constructor value applies the corresponding algebra branch, after recursively folding each recursive field.

Let the binder metavariables be `?case_C1, …, ?case_Ck` in constructor order. Then for each constructor `C_i : Γ_i -> T`, the macro generates a rule of the form:

- `C_i{α} ; fold_T{α,ρ}[?case_C1,…,?case_Ck] == mapArgs_i ; splice(?case_Ci)`

where `mapArgs_i : Γ_i -> Γ'_i` is the tensor product (in argument order) of:

- identity on non-recursive arguments, and
- the recursive call `fold_T{α,ρ}[?case_C1,…,?case_Ck]` on each recursive argument.

Because these β-rules use `splice` and (for recursive constructors) mention `fold_T` recursively, they are **operational** computation rules and are not part of the admissible first-order TRS fragment used for definitional equality/termination checking.

This subsection documents the mathematical meaning (initial algebra + catamorphism) and the exact kernel-level artifacts (a generated generator plus generated computational rules) introduced by the `data` macro extension.

### 2.8 Classifier Dependency Order

For doctrine validation and later normalization/unification environment construction, the kernel SHALL compute a classifier dependency order `order : [ModeName]` such that:

- if `M classifiedBy K` and `M != K`, then `K` appears before `M` in `order`.

### 2.9 Pending Universe Resolution (Current)

During elaboration, a `classifiedBy ... via ...` universe expression can be temporarily unresolved.

Current behavior:

- if the raw universe is not immediately classifiable as a simple name/nullary constructor, elaboration stores a temporary pending universe marker;
- pending universes are resolved after initial mode/generator collection, using object elaboration with constructor tables from `deriveCtorTablesForElab`;
- this elaboration-time constructor-table path derives tables for resolvable classifier dependencies first, tolerates forward references to not-yet-declared classifier modes, then adds provisional tables for owner modes whose universes are still pending;
- after pending resolution, normal doctrine validation still uses full constructor-table derivation and rejects unresolved or inconsistent universes.

This means complex universe expressions (including constructor applications with arguments) are supported in the current elaboration pipeline; they are not restricted to names/nullary constructors.

### 2.10 Comprehension Declarations (Current Cut)

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
- generated comprehension obligations SHALL be discharged during doctrine elaboration (against the generated-obligation subset); if proof search returns `undecided` for any generated obligation, doctrine elaboration SHALL reject the doctrine.

Current policy note:

- every classified mode must provide a `comprehension` declaration.

## 3. Definitional Fragment

Every mode has a definitional-equality engine used by kernel normalization/equality.

Mode declaration supports:

- `mode M ... defeq trs ...;`
- `mode M ... defeq nbe ...;`

If `defeq` is omitted, the mode defaults to `trs`.

Implemented fragments:

- `TRS` fragment:
  - first-order TRS normalization compiled from admissible computational rules and eligible generators.
  - term symbols are generator names: the TRS signature is a *subset* of the mode’s generators determined by the term-fragment eligibility checks.
  - admissibility requirements:
    - rewrite compilation remains in the first-order term fragment,
    - termination MUST be proven (SCT),
    - critical pairs MUST be joinable by normalization.
- `NbE` fragment:
  - binder-aware normalization for a lambda fragment in term diagrams.
  - normalization is beta-normal and eta-long at function sorts (`Arr`), with eta enabled by default.
  - required primitives per NbE mode are inferred structurally by typing shape (not by fixed names):
    - a lambda generator in owner mode `M` with one binder input of shape `[A] -> [B]`, zero plain inputs, and one output sort `Arr(A,B)`,
    - an application generator in owner mode `M` with boundary shape `[Arr(A,B), A] -> [B]`,
    - an arrow type constructor `Arr` in the classifier mode of `M` used by both shapes above.
  - primitive inference requires a unique `(lambda, app, Arr)` triple per NbE mode; zero matches or multiple matches are rejected.
  - additional `Arr` checks:
    - `Arr` must be declared constructor-like in `classifier(M)` (no inputs, no attrs),
    - `Arr` must have exactly two type parameters,
    - `Arr` must be eligible for owner mode `M` (present in derived constructor tables).
  - unsupported constructs are rejected during definitional normalization in NbE modes:
    - box/feedback/splice payloads,
    - generator attrs,
    - binder metavariables,
    - generators other than the inferred lambda primitive carrying binder args.

  Conceptually, this matches CCC/STLC structure: `Arr` as exponential type former with lambda/application as intro/elim operations (Lambek–Scott; Berger–Schwichtenberg NbE perspective).

Termination/confluence checks apply to `TRS` fragments only; `NbE` fragments skip TRS compilation checks.

This matches the standard TRS presentation over a signature (\Sigma) (Terese, *Term Rewriting Systems*, 2003), where in llang the signature (\Sigma) is the eligible subset of generator 1-cells of the mode (cf. Burroni’s polygraphs as presentations, 1993).

### 3.1 Kernel DefEq API (Current)

Current implementation centralizes normalization/equality entrypoints in `Strat.Poly.DefEq`:

- `normalizeTermDiagram`
- `normalizeObjDeep` / `normalizeObjDeepWithCtx`
- `normalizeCodeTermDeepWithCtx`
- `defEqObj`
- `defEqTermDiagram`

Per-mode definitional data is represented by `DefFragment`:

- `DefFragmentTRS`:
  - `dfMode`: mode name
  - `dfFuns`: admissible term symbols in that mode, keyed by generator names (`GenName`); there is no separate “term function name” namespace—TRS term symbols are exactly the eligible generator symbols of the mode.
  - `dfRules`: admissible computational rules in that mode
  - `dfTRS`: compiled TRS used by normalization/equality
- `DefFragmentNBE`:
  - `dfMode`: mode name
  - `dfFuns`: admissible term symbols in that mode, keyed by generator names (`GenName`); there is no separate “term function name” namespace—TRS term symbols are exactly the eligible generator symbols of the mode.
  - `dfRules`: admissible computational rules in that mode
  - `dfNBE`: NbE configuration

`normalizeCodeTermDeepWithCtx` and `normalizeTermDiagram` are the shared normalization services used by object equality (`defEqObj`) and term equality (`defEqTermDiagram`). `normalizeTermDiagram` dispatches by mode fragment (`TRS` vs `NbE`).

## 4. Doctrine Layer

Key records:

- object signatures are parameterized by mode and object parameters (`TPS_Ty`, `TPS_Tm`)
- `GenDecl` supports metavariables with two roles:
  - code metavariables (type-level) represented in object codes as `CTMeta`
  - term metavariables represented on term edges as `PTmMeta`
  Surface syntax may still call code metavariables "type variables".
- `GenDecl` parameters form a single ordered **telescope** (`gdParams : [GenParam]`), i.e. a context in the sense of generalized algebraic theories/contextual categories.
  - The “type-parameter list” and “term-parameter list” are *derived projections* of the telescope, not separately stored kernel data.
  - **Kernel invariant (telescope-only storage):** all mixed contexts Γ of kinded parameters are stored *only* as a single telescope `[GenParam]`. Split views (type parameters vs term parameters) are derived *only* by filtering/projection.
  - This invariant applies at:
    - `GenDecl.gdParams :: [GenParam]`
    - `Cell2.c2Params :: [GenParam]` (rules)
    - `ObligationDecl.obParams :: [GenParam]` (obligations)
    - `TypeTemplate.ttParams :: [GenParam]` (morphism type maps / templates)
  - There is no separate “template parameter” datatype; type templates reuse `GenParam`.
  - This eliminates a coherence obligation (“metadata mismatch”) that arises if a telescope and its projections are stored independently.
- `Cell2` rewrites diagrams
- `ModAction` stores per-modality generator images
- `ObligationDecl` stores named equations checked on `implements`

Validation checks:

- mode/modality well-formedness
- object/generator/rule well-formedness
- action coverage and mode correctness
- obligation diagrams are valid and boundary-compatible

Reference note: Telescopes/contexts as the primitive representation of parameters follow the standard presentation of generalized algebraic theories and contextual categories. John Cartmell, *Generalised algebraic theories and contextual categories*, Annals of Pure and Applied Logic 32 (1986), 209–243. Marcelo Fiore, Gordon Plotkin, Daniele Turi, *Abstract Syntax and Variable Binding*, Proceedings of LICS 1999.

## 5. Diagram Layer

A `Diagram` is a typed port graph with edge payloads:

- `PGen`
- `PBox`
- `PFeedback` (traced feedback node; see “Feedback as trace” below)
- `PSplice`
- `PTmMeta`
- `PInternalDrop` (kernel-internal, non-surface payload)

### Feedback as trace

`PFeedback inner` represents the trace (feedback) operator in string-diagram form.

An outer diagram contains an edge `e` with payload `PFeedback inner`. Let:

- `A` be the list of objects on outer input ports `eIns`.
- `B` be the list of objects on outer output ports `eOuts`.
- `dom(inner)` / `cod(inner)` be the boundary object lists of `inner`.

The edge is well-typed iff there exists a non-empty feedback list `X = [X1, ..., Xk]` with `k > 0` such that:

- `dom(inner) = A ++ X`
- `cod(inner) = B ++ X`

Equivalently, with `m = |A|` and `n = |B|`:

- `k = |dom(inner)| - m` and `k > 0`
- `|cod(inner)| = n + k`
- `drop m (dom(inner))` and `drop n (cod(inner))` match pointwise

This is the standard traced-monoidal operator:

    Tr^X : Hom(A ⊗ X, B ⊗ X) -> Hom(A, B)

Suffix convention: the feedback wires are the suffix wires of `inner` (last `k` inputs and last `k` outputs).

Syntactic sugar:

- `trace k { d }` traces the last `k` boundary wires of `d`.
- `loop { d }` traces all inputs of `d`: if `d : X -> (B ++ X)` with `|X| > 0`, then `loop { d } : [] -> B`.

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
  - `PTmMeta`: term metavariables.

    A `PTmMeta` edge carries a typed metavariable `X` (implementation: a `TmVar` record) and has an explicit spine given by the ordered list of its input boundary ports. Intuitively, a `PTmMeta` edge represents an occurrence of a metavariable applied to a list of in-scope boundary variables; the spine records exactly which boundary inputs are supplied (and in which order).

    Metavariable identity is `(name, scope)`; the sort is carried as part of typing data and must coincide with the output port type in any well-formed term diagram.
  - `PInternalDrop`: exact constructor match

#### Contextual metavariables and spines

A metavariable occurrence is understood in the standard “metavariable applied to bound variables” form: it is a metavariable together with an explicit spine selecting boundary variables.

This is the common presentation in contextual type theory (metavariables/holes are decorated with a context and instantiated by providing an explicit substitution/spine), and in the higher-order pattern fragment where metavariables only occur applied to a list of distinct bound variables.

Well-formed term metavariable occurrences satisfy `length(spine) = scope(X)`.

Implementation note: the internal term-expression AST uses a single constructor for metavariables, `TMMeta X spine`. The earlier special case “implicit metavariable with canonical-prefix arguments” is not a separate constructor; it is represented by `TMMeta X defaultSpine`, where `defaultSpine` is the mode-local prefix of length `scope` in the ambient term context.

### Support contexts and context-inferred normalization

In the categorical semantics of dependent type theory (e.g. categories with attributes / categories with families), types and terms are inherently **indexed by a context** and substitution is reindexing along context morphisms. In particular, the kernel’s object expressions (`Obj`) should be treated as *types-in-context*, even when their only dependence on the context is mediated through embedded term arguments.

In llang, an `Obj` can contain embedded term arguments as `CATm TermDiagram` inside constructor applications. Each such `TermDiagram` carries an explicit term-context `dTmCtx`. Define the **support context** of an object expression `T`, written `supp(T)`, to be the least context `Γ` (least upper bound under the prefix order) such that for every embedded term argument `t` occurring anywhere inside `T`, the stored context `dTmCtx(t)` is a prefix of `Γ`.

Deep normalization of objects is defined relative to this support context:

* `normalizeObjDeep(T)  ≔  normalizeObjDeepWithCtx(tt, supp(T), T)`.

Operationally, `supp(T)` is computed by collecting all `dTmCtx` lists from embedded `CATm` term arguments in `T` and merging them via prefix-compatible context join. If two embedded term arguments demand incompatible contexts (not prefix-compatible), then `T` is ill-formed as a type-in-context and deep normalization fails.

This removes the previous implementation artifact where substitution/normalization of objects avoided deep normalization whenever an object contained open term arguments.

(References: contextual categories/categories with attributes (Cartmell) and categories with families (Dybjer); contextual type theory for metavariables with explicit contexts and context-merging operations.)

### 5.3 Meta Substitution

Kernel substitution is a single metavariable substitution environment.

- code metavariables map to object/code terms
- term metavariables map to term diagrams

Well-formedness invariant:

- a metavariable is only instantiated in the syntactic category where it occurs; kind mismatches are rejected as kernel errors.
- code-metavariable scope checks are performed against the classifier-mode slice of the telescope (`modeClassifierMode owner`), not the owner-mode slice.
- term metavariable solutions are stored in canonical form and instantiated at each occurrence spine during substitution.
- pattern-fragment solving for term metavariables requires:
  - correct spine arity (`length(spine) = scope(X)`),
  - injective solving spines,
  - RHS bound indices contained in the solving spine.
- non-injective spines are not solvable by unification (rigid for solving), but existing solutions are still instantiated at such spines during substitution.

Kernel implementation note: metavariable `Eq`/`Ord` is intentionally id-based (`name`, `scope`), so `Map`/`Set` keys remain stable under sort normalization/substitution. Sort agreement is enforced by typing/diagram validation, not by metavariable identity keys.

### 5.2 Canonical Form

Canonicalization reduces a diagram to a colored graph encoding:

- vertices for boundary positions, ports, edges, and ordered input/output slots
- edges for boundary attachments and slot incidence
- colors enforcing boundary index, slot index/direction, port type, and edge payload shape

Canonical labeling picks a deterministic representative and rebuilds the diagram with canonical `PortId`/`EdgeId` assignment. Canonization is recursive through payload-contained diagrams (`PBox`, `PFeedback`, `BAConcrete`).

Port labels are treated as metadata for structural isomorphism/canonization by default (ignored as equality keys), while still being stored on diagrams.

## 6. Modalities

`mod_eq` contributes to definitional equality of modality expressions by normalization.

Semantically, modalities generate the free category on the mode graph: a modality expression is a path, and each `mod_eq` declaration is a generating 2-cell (relation) between parallel paths. The kernel treats the set of `mod_eq` declarations as an *oriented rewriting system* on paths and requires this system to be *convergent* (terminating and confluent). Under convergence, every modality expression has a unique normal form, and definitional equality of modality expressions is equality of their normal forms.

Implementation (used for checking and normalization): encode a path `m1.m2...mk` as a unary term spine `m1(m2(...(mk(__mod_id))...))`, where each modality name is a unary symbol and `__mod_id` is a nullary constant for the empty path. A declared equation `lhs -> rhs` is compiled to the TRS rule `enc(lhs, X) -> enc(rhs, X)`, where `X` is a single variable representing the suffix context.

Kernel checks for `mod_eq`:
- **Termination:** must be proven by the same size-change termination (SCT) check used for computational TRSs.
- **Confluence:** all critical pairs must be joinable (checked by normalizing both sides); together with termination, this yields confluence and strategy-independent normal forms.

References (rewriting/convergent presentations): Baader–Nipkow *Term Rewriting and All That*; Book–Otto *String-Rewriting Systems*; Guiraud (polygraphs/convergent presentations of categories); Burroni (polygraphs).

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

`map[<ModExpr>](<DiagExpr>)` elaborates by applying modality actions along the composed modality expression, using:

- explicit declared generator images when present, and
- canonical same-name target-generator images as fallback when explicit images are absent.

If neither exists for a needed generator image, elaboration fails.

**Diagram interpretation principle.** Both modality actions and doctrine morphisms use the same universal construction: specifying the image of each generating edge (together with how boundary/object-types are transported) determines a unique extension to all diagrams by structural recursion on diagram shape (boxes/feedback/subdiagrams) and by *splicing* the chosen image at each generator-edge. This is the string-diagram/PROP analogue of how a polygraph/computad presentation freely generates a categorical structure, and an “interpretation of generators” extends uniquely to an interpretation of all composites/tensors.

Reference: explicit action semantics are described in [[https://arxiv.org/abs/2305.05958](https://arxiv.org/abs/2305.05958)]. Background on string diagrams as an internal language for (strict) monoidal categories: Joyal & Street, *The Geometry of Tensor Calculus I* (1991). Background on polygraphs/computads as presentations: Burroni (1993) and Ara–Maltsiniotis et al., *Polygraphs* (PolyBook).

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

Elaboration-time strictness for generated checks:

- doctrine elaboration SHALL reject `undecided` results for:
  - action semantics checking on declared actions,
  - generated comprehension obligations,
  - generated Beck-Chevalley obligations.
- equivalently: these generated checks must be proved during doctrine elaboration for the doctrine to be accepted.

Action-semantics proof scope (current cut):

- rule/mod_eq preservation checks are enforced over the explicitly declared action-image fragment;
- fallback-only generator behavior is operationally available to `map[...]` but is not yet proof-checked as part of action-semantics validation.

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

Current slot-profile scope:

- binder-only generator domains participate;
- mixed-domain binder generators (plain ports plus binder slots) are currently excluded;
- constructor term-argument slots participate on dom/cod sides according to slot position.

Admission policy (current cut):

- generated Beck-Chevalley obligations are discharged during doctrine elaboration;
- if any generated Beck-Chevalley obligation result is `undecided`, doctrine elaboration rejects the doctrine.

## 8. DSL Summary

Doctrine items:

- `mode`, `modality`, `mod_eq`, `mod_transform`
- `action`, `obligation`
- `attrsort`, `data`, `gen`, `rule`

Mode declaration supports optional engine selection:

- `mode M [acyclic] [defeq trs|nbe] [classifiedBy K via U [as tag]];`

Top-level functor/apply items:

- `doctrine_functor F(A : SA, B : SB, ...) where { ... }`
- `doctrine New = apply F to Target using { A = implA; B = implB; ... };`

Diagram-level trace/feedback constructs:

- `trace k { d }` traces the suffix of size `k` (requires `k > 0`).
- `loop { d }` is sugar for tracing all inputs of `d` (suffix convention).

Functor namespace/use rules:

- parameter-provided names must be referenced as `Param::Name` inside functor bodies
- parameter mapping keys in `using { ... }` must exactly match the functor parameter set
- functor parameter schemas are full doctrines (they may include rules, actions, obligations, and `mod_transform`)
- `apply` checks schema rules and obligations before pushout instantiation

Removed legacy items:

- `index_mode`, `index_fun`, `index_rule`
- `structure ... = ...`
- `adjunction F dashv U`

## 9. Morphisms and Pushouts

Morphisms map modes/modalities/types/generators and transport diagrams.
This replacement is the same “diagram interpretation principle” as for modality actions: the morphism’s generator images extend uniquely to all diagrams by recursion and generator-edge splicing.
Pushout/coproduct construction remains available and merges doctrine content with compatibility checks.
`apply` computes a right-biased pushout where target names are preserved and colliding
functor-body declarations are prefixed/freshened.
The collision prefix is derived from the functor name (for example `F_...`).

### 9.1 Doctrine Functors

`doctrine_functor` parameters are full doctrine schemas, not signature-only fragments.
For each parameter `(P : S)`, interface construction imports the entire schema doctrine `S`
under the `P::` namespace.

Namespacing renames all schema content:

- modes
- modalities
- mode transforms
- object constructors/types
- generators
- rewrite cells/rules
- modality actions
- obligations
- attribute sorts

`apply` builds one interface morphism `implIface : iface -> target` by:

- taking each provided parameter morphism,
- lifting its domain names to the corresponding `P::...` names,
- merging the lifted maps into a single morphism.

Before pushout, `apply` must check:

1. `implIface` passes full morphism checking (`CheckAll`) against interface rules/cells.
2. all interface obligations are discharged under `implIface`.

If either check fails, or any obligation remains undecided under the active search budget,
`apply` fails and no pushout is computed.
If both checks succeed, pushout construction proceeds as before.

References:

- Diaconescu, *Structuring of Specification Modules*, 2015 (pushout technique for parameterized module instantiation).
- Goguen and Burstall, *Institutions: Abstract Model Theory for Specification and Programming*, 1984 (colimits for combining theories).

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

## 11. Foliation as SSA and term-graph reification

For derived doctrines declared as `derived doctrine D_SSA = foliated D mode M`, foliation is only available for modes declared acyclic in `D`.

`D_SSA` is a generated doctrine that reifies SSA steps as typed constructors and supports ordinary morphism-based compilation.

1. **Signature of `D_SSA`:**

- `PortRef`, `PortList`, `Step`, `StepList`, `SSA` as nullary object constructors in mode `M`.
- `portRef { name : __ssa_str } : [] -> [PortRef]`
- `portsNil : [] -> [PortList]`, `portsCons : [PortRef, PortList] -> [PortList]`
- `stepsNil : [] -> [StepList]`, `stepsCons : [Step, StepList] -> [StepList]`
- `ssaProgram : [PortList(in), PortList(out), StepList] -> [SSA]`
- `stepBox { name : __ssa_str } : [PortList(out), PortList(in), SSA] -> [Step]`
- `stepFeedback : [PortList(out), PortList(in), SSA] -> [Step]`
- For each generator `g` of `D` in mode `M`, a generated constructor `step_g`.

2. **Generated step constructors:**

- If `g : Γ -> Δ` has `m = |Δ|` outputs, `n` non-binder inputs, and `k` binder arguments, then:
- `step_g : [PortRef]^m ⊗ [PortRef]^n ⊗ [SSA]^k -> [Step]`
- `step_g` carries exactly the attribute list of `g`.

3. **Reification function (pipeline semantics):**

- `extract foliate into D_SSA` computes SSA (ports, ordered steps, naming) from a diagram in `(D, M)`.
- Applying a morphism whose source is `D_SSA` reifies SSA through the constructors above (`encodeSSAArtifact`), including generator attributes, binder SSA subprograms, and inner SSA for box/feedback steps.
- This is the explicit term-graph/SSA boundary: steps are ordered and named in the reified object.

4. **Mathematical note:**

- This corresponds to representing acyclic computations as labeled DAGs (term graphs), i.e. the free gs-monoidal/term-graph style encoding of sharing.

The sort `__ssa_str` is reserved for SSA-introduced names (for example port/box names) and must denote string literals.

## 12. Restrictions

See `RESTRICTIONS.md`.

## References

- Cartmell, *Generalised Algebraic Theories and Contextual Categories* (1986).
- Dybjer, *Internal Type Theory* (1996).
- Boespflug & Pientka, *Multi-Level Contextual Type Theory* (2011).
- Andrea Corradini and Fabio Gadducci. *An Algebraic Presentation of Term Graphs, via GS-Monoidal Categories.* Applied Categorical Structures 7(3), 1999.
- Jad Ghalayini and Neel Krishnaswami. *The Denotational Semantics of SSA.* arXiv:2411.09347, 2024.
