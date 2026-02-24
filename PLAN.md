## Guiding choices and invariants

This plan assumes the following non-negotiables (they are what make the foundation “never replace”):

1. **Classification is universes-of-codes, not “Ty-objects are literally Tm-objects”.**
   `mode Tm classifiedBy Ty via U` means: objects/types in `Tm` are represented by **code terms** in `Ty` of (classifier) object `U`, and definitional equality of `Tm`-types is definitional equality of those `Ty`-codes. This is the standard universe/El pattern from categorical semantics (CwF/comprehension categories), adapted to your multi-mode setting. ([arXiv][1])

2. **No separate “type constructor namespace”.**
   What counts as a type constructor for `Tm` is determined by which **term-formers in `Ty` produce codes of `U`**, plus `Ty`’s computation theory. (This is exactly your payoff; the kernel just enforces the pipeline.)

3. **Definitional equality stays algorithmic for a declared “definitional fragment”.**
   Initially: first-order TRS normalization (your current approach). Later: optional NbE (and proofs via gluing) for binder-aware definitional computation in selected modes, without changing the rest of the kernel. Gluing is the right meta-theory tool for showing modularity/interaction with modalities. ([drops.dagstuhl.de][2])

4. **Binding soundness is not assumed. It is structure + laws.**
   Declaring a classification edge (and/or using binder-shaped generators) requires providing explicit comprehension/substitution structure and proving the presheaf/CwF-style laws (or, semantically, the CwR/MCwR-style stability conditions). ([arXiv][3])

5. **Beck–Chevalley is generated whenever it is meaningful.**
   When a modality crosses classified modes, it must come with enough lifted/translated structure on the classifiers to *state* and then *check* BC squares. ([arXiv][4])

---

## High-level architecture outcome (what exists when we’re done)

After the foundational work, the kernel will have:

* A **classification graph** between modes with explicit **universe objects** (`via U`) per edge.
* A single internal notion of “object/type of a port” that is *represented by code terms* (not by a dedicated `TypeExpr` AST).
* A uniform mechanism to:

  * derive a mode’s “type constructors” from the classifying mode’s term generators,
  * normalize/equate types by normalizing/equating code terms in the classifier,
  * reject doctrines that do not provide the required comprehension/substitution structure.
* Support for:

  * **self-classification** (Type : Type style) when desired,
  * **layered classification** (kinds/types/terms),
  * **BC coherence** between modalities and classification.

This is enough to *express* the λ-cube axes compositionally; getting β/η computation at higher layers in definitional equality is addressed in later phases (NbE). ([arXiv][1])

---

## Ordered implementation plan (phases)

### Phase 0 — Write the kernel-level spec for classification and equality

**Goal:** lock down semantics before code changes.

**Define precisely:**

* `classifiedBy` edges as **codes-in-universe**: `Tm ▷ Ty via U`.
* The meaning of “`Tm`-type equality”:

  * `A ≡ B` iff `NF_Ty(quote(A)) == NF_Ty(quote(B))` for the selected definitional fragment.
* What “type constructors for `Tm`” means:

  * a type constructor is a `Ty` term former whose result is `U` (up to definitional equality in `Ty`).
* The conditions under which self-classification is allowed:

  * `Ty ▷ Ty via U` is allowed; logical consistency is not a kernel concern (programming languages accept it).
* What counts as “definitional fragment”:

  * initially: first-order TRS fragment (like your current `derivedTmFuns` eligibility),
  * later: NbE-enabled fragment.

**Deliverable:** a new SPEC section “Classification and Universes”, plus a “Definitional Fragment” section that states exactly what normalization engine is used where.

**Exit criterion:** you can take *just the spec* and answer: “what is a `Tm` type?” and “how do I compute whether two `Tm` types are definitionally equal?” without referring to implementation details. ([arXiv][3])

---

### Phase 1 — Delete `TypeExpr` and replace it with “object codes”

**Goal:** remove the legacy type AST entirely and unify types with the same “term-ish” representation used for computation.

**Key design choice:** port objects are represented as **code terms**, not as a bespoke `TypeExpr`. Concretely:

* Introduce a core datatype `Obj` (or `PortObj`) used everywhere a port “type” currently appears.
* `Obj` is not “a term diagram”; it is a **code term** living in some classifier mode and typed by that classifier’s universe object.
* Keep a minimal notion of primitive objects only where needed to type the classifiers themselves (e.g. `U`, `Star`, etc.). Everything “type-like” for a classified mode is a code.

**What gets refactored:**

* Diagram representation:

  * `dPortTy :: IntMap TypeExpr` becomes `dPortObj :: IntMap Obj`.
  * `dTmCtx :: [TypeExpr]` becomes `dTmCtx :: [Obj]` (multi-mode telescope remains).
* Generator declarations:

  * `gdDom`, `gdCod`, binder signatures move from `TypeExpr` to `Obj`.
  * Remove `TyVar`-based type polymorphism as a separate mechanism; schematic variables in object codes become **term metavariables in the classifier** (see Phase 4).
* All type-utility code:

  * remove `TypeExpr.hs`, `TypeNormalize.hs`, `TypePretty.hs`, `UnifyTy.hs` (or replace them with the new object-code equivalents).

**Deliverable:** the codebase compiles with **no `TypeExpr`** and no parallel “legacy” paths.

**Exit criterion:** a diagram can be constructed, validated, matched, rewritten, and pretty-printed with object labels represented by the new `Obj` system.

---

### Phase 2 — Extend mode theory with classification edges (and check graph well-formedness)

**Goal:** make classification a first-class kernel structure, not a convention.

Add to mode theory:

* `classifiedBy` edges: `mode M classifiedBy K via U`.
* Per edge, store:

  * classifier mode `K`,
  * universe object `U` (an object of `K`),
  * optional “layer name” or tag (useful for diagnostics and later syntax).

Static checks:

* referenced modes exist,
* universe object `U` is a valid object in `K`,
* classification graph is **stratifiable**:

  * allow self-loops (`M ▷ M`),
  * reject longer cycles unless/until you add explicit universe levels.

**Deliverable:** mode theory validation now includes classification validation.

**Exit criterion:** you can compute a stable order of “classifier dependencies” for building normalization/unification environments.

(Conceptual grounding: this is the split/comprehension discipline that underlies CwF/CwR-style semantics. ([arXiv][3]))

---

### Phase 3 — Define “code term” infrastructure and make it the universal object representation

**Goal:** make “types are terms in a classifier” operational.

Introduce:

* A representation `CodeTerm` used by `Obj`:

  * initially: a first-order term AST with metavariables and bound variables (your existing `TermExpr` model is close),
  * with explicit mode and expected sort/universe info attached.

Define core operations:

* `normalizeObj(tt, obj)`:

  * if `obj` is a code in classifier `K`, normalize the underlying code term using `K`’s definitional engine (Phase 5).
* `objEq(tt, obj1, obj2)`:

  * normalize both and compare canonical forms (or decide joinability in a later proof-relevant variant).

Define embedding of the multi-mode telescope:

* an `Obj` may mention bound variables from `dTmCtx` entries that live in the classifier mode.

**Deliverable:** a module that replaces “type normalization” and “type mode” queries with “object normalization” and “object classifier” queries.

**Exit criterion:** existing term-index normalization (“`TATm` normalization”) is re-expressed in terms of `Obj` sorts and still works.

(You are now structurally aligned with “types as codes in a universe”, i.e. CwF’s `Ty(Γ)` as terms into a universe. ([arXiv][3]))

---

### Phase 4 — Unify variable mechanisms: eliminate `TyVar` as a special category

**Goal:** enforce your payoff: no separate type namespace; type variables are just variables in a mode.

Replace:

* “type variables in object expressions” with **metavariables in the classifier mode’s code terms**.

Concretely:

* Schematic object variables become `MetaVar` nodes in `CodeTerm` (like your term metavariables).
* Their sort is the classifier universe `U`.
* Their scope is governed by the classifier’s portion of the telescope (same discipline you already use for `tmvScope`).

Implementation note (current):

* Scope checks for code metavariable bindings are performed against the classifier-mode slice `modeClassifierMode(owner)` of `dTmCtx`.

Update matching/unification:

* Port-object unification becomes **code-term unification** in the classifier:

  * flexible vars = code metavars (and possibly term metavars) designated by the rule/generator environment,
  * rigid vars = everything else.

**Deliverable:** there is only *one* metavariable/unification story, parameterized by “which mode am I unifying terms in?”.

**Exit criterion:** rewrite rule matching that previously used `(TyVar-subst, TmVar-subst)` becomes a single substitution environment over mode-indexed metavariables.

---

### Phase 5 — Rebuild the definitional equality engine around “per-mode definitional fragments”

**Goal:** make normalization/equality of codes the basis of type equality.

Implement a uniform pipeline:

1. From doctrine rules, identify each mode’s admissible **definitional TRS fragment** (same idea as current `derivedTmFuns` + computational `Cell2` rules).
2. Compile admissible rules to TRSs per mode; check termination + confluence in the same way you do now.
3. Provide `normalizeCodeTerm(mode, term)` as fuel-free normalization.

Current concrete kernel API/structures:

* `Strat.Poly.TypeTheory.DefFragment` and `ttDefFragments :: Map ModeName DefFragment`.
* `Strat.Poly.DefEq` as the single entrypoint for normalization/equality:
  * `normalizeTermDiagram`
  * `normalizeObjDeep` / `normalizeObjDeepWithCtx`
  * `normalizeCodeTermDeepWithCtx`
  * `defEqObj`
  * `defEqTermDiagram`

Then:

* `normalizeObj` normalizes the classifier-side code term for classified objects.
* Term-index normalization continues to normalize term arguments in their own modes, but sorts are now `Obj`.

**Deliverable:** a single “definitional normalization service” used by:

* object equality,
* term normalization (for term arguments and other definitional uses),
* unification.

**Exit criterion:** definitional equality no longer depends on any “type-specific” machinery; it is just “normalize in the appropriate mode’s definitional fragment”.

(This clean separation is the same move used when proving normalization/canonicity via gluing/NbE: there is a chosen computational interpretation and a reification. ([drops.dagstuhl.de][2]))

---

### Phase 6 — Derive “type constructors” automatically from the classifier mode (your item 1)

**Goal:** implement “`TCon` vocabulary comes from classifying mode generators”.

For each classification edge `Tm ▷ Ty via U`:

* Compute the set of **eligible code constructors**:

  * generators (or derived term functions) in `Ty` whose result object is `U` (up to definitional equality in `Ty`),
  * optionally restricted to those in the definitional fragment at first.
* These constructors become the *only* way to form `Tm` objects (types), aside from variables in the classifier.

This replaces:

* `dTypes` / `TypeSig` / `ttTypeParams` / `TCon`.

**Deliverable:** the kernel can answer: “what are the type formers for `Tm`?” purely from `Ty`’s generator environment and `U`.

**Exit criterion:** adding/removing a generator in `Ty` changes the type language of `Tm` with no kernel changes.

This is the doctrinal-control lever you want.

Current implementation status:

* classified modes use derived constructor tables from classifier generators (ordered parameter telescopes),
* generator-call elaboration follows explicit parameter order metadata,
* legacy `dTypes`/`TypeSig` constructor tables are removed; constructor resolution/typechecking is driven by derived classifier constructor tables.

---

### Phase 7 — Make binding/comprehension a required structure with generated obligations (your item 2)

**Goal:** whenever classification exists (and/or binders are used), the kernel demands and checks the presheaf/comprehension laws instead of assuming them.

#### 7A. Decide the semantic target and its checkable presentation

Use:

* **CwF-like split presentation** as the *checkable interface*, because you want explicit witnesses and equations you can mechanize.
* **CwR/MCwR** as the *semantic spec* for why this interface is the right notion of “type theory in categories”, especially in the multi-mode setting. ([pure.uva.nl][5])

#### 7B. Introduce a “comprehension structure declaration” for a classified mode

For each `Tm ▷ Ty via U`, require a declaration of witness operations (names of generators/derived operations) providing:

* **context extension** / comprehension: how to form `Γ.A` and projections,
* **variable**: the distinguished term of type `A` in `Γ.A`,
* **reindexing/substitution action on codes**: how a `Ty`-code over `Γ` is transported along a `Tm` substitution,
* **(optional) structural rules**: weakening/contraction/exchange maps if the mode claims them.

These witnesses must be expressed using your existing doctrine vocabulary: generators + equations.

#### 7C. Auto-generate obligations (finite basis)

Generate a finite list of laws corresponding to:

* substitution functoriality (identity, composition),
* comprehension stability and typing of projections/variables,
* coherence with weakening/contraction (only if the mode exposes those structural maps).

Mechanically:

* generate them as internal obligations and check them by definitional equality (preferred) or by join-proof search when necessary.

**Deliverable:** binder-taking generators are admitted only if the mode’s comprehension structure passes these checks.

**Exit criterion:** a doctrine that lacks the needed structure cannot declare classification (or cannot declare binder signatures) without being rejected.

(CwF reference point: substitution/context formation laws. ([arXiv][3])
CwR/MCwR reference point: representable maps + stability under pullback as the semantic core. ([pure.uva.nl][5]))

---

### Phase 8 — Implement self-classification and layered classification (your items 3 and 4)

**Goal:** make these just instances of the same mechanism, not special cases.

#### 8A. Self-classification

Allow `Ty ▷ Ty via U`.

* Require the same comprehension witnesses and obligations, now internal to `Ty`.
* Permit a code constant `Type : U` with a rule/axiom that it decodes to `U` (if you include decoding explicitly), or just treat it as another code that denotes an object in the mode.

No kernel special-casing; only graph validation + definitional equality checks.

#### 8B. Layered classification

Allow chains:

* `Tm ▷ Ty via U_Tm`
* `Ty ▷ Kd via U_Ty`
* etc.

Ensure:

* classifier dependency order is well-founded (except self-loops),
* normalization/equality is built in dependency order.

**Deliverable:** you can define:

* `Kd` with codes for kinds,
* `Ty` as a mode whose objects are codes in `Kd`,
* `Tm` whose objects are codes in `Ty`.

**Exit criterion:** you can represent higher-kinded type constructors as variables/codes in `Ty` classified by kind codes in `Kd`.

(Conceptual alignment: this is the same structure that gluing-based proofs for multimodal dependent type theories treat parametrically over “modal situations”, i.e. over the base classification/modality structure. ([arXiv][4]))

---

### Phase 9 — Beck–Chevalley coherence generation for modalities (your item 5)

**Goal:** “bugs at the seams” become failed BC obligations.

For each modality `μ : M → N` where both modes are classified:

* `M ▷ TyM via U_M`
* `N ▷ TyN via U_N`

require one of:

* a lifted modality on classifier modes `μ^Ty : TyM → TyN` plus compatibility on universes, or
* an explicit “code translation” morphism from `TyM` codes to `TyN` codes.

Then generate BC obligations stating that:

* transporting a typed term along `μ` commutes with transporting its **type code** along `μ^Ty`,
* and (if dependent typing is present) that reindexing/pullback on codes commutes with `μ`’s transport.

Check these obligations by definitional equality or join proofs.

**Deliverable:** BC obligations are generated automatically whenever the required structure exists.

**Exit criterion:** if a modality connects classified modes but the classifier translation is missing or incoherent, the doctrine is rejected (or marked as requiring proof, depending on policy).

(Gratzer’s MTT normalization result is relevant because it shows conversion/typechecking can be reduced to deciding modality equalities in a general multimodal setting; BC coherence is exactly the extra condition you need when adding typed transport. ([arXiv][4])
Uemura’s MCwR framing is relevant because it treats multimode type theories with representable maps as the semantic substrate where BC-style stability is natural. ([Taichi Uemura][6]))

---

### Phase 10 — Update morphisms, pushouts, and doctrine functors to be classification-aware

**Goal:** the composition story remains the same, but now type systems compose as part of mode/classification data.

Update:

* morphisms must map:

  * modes/modalities,
  * generators/rules,
  * **classification edges and universe objects**,
  * comprehension witness data (if declared),
  * lifted classifier translations for modalities (for BC).
* pushouts must reconcile classification:

  * merging two fragments that both classify `Tm` must either agree (up to definitional equality in the classifier) or force a naming/structural pushout at the classifier level.

**Deliverable:** you can implement “add polymorphism” and “add higher kinds” as doctrine functors that add classification edges and/or classifier generators, and the pushout checks the interaction.

**Exit criterion:** the “λ-cube by composing features” story works at the doctrine level without kernel changes.

---

### Phase 11 — Rebuild the standard library + regression suite around classification

**Goal:** validate generality by instances (your stated invariant).

Provide canonical doctrines (or doctrine functors) that realize:

* STLC: `Tm ▷ Ty via U`, where `Ty` has code constructors for arrow/product/unit, etc.
* System F: add type quantification via structure in the classifier (initially may require explicit encodings unless NbE phase is done).
* Fω: add kind layer `Ty ▷ Kd via U_Ty`, plus kind-level computation rules.
* Modal examples: at least one modality across classified modes, exercising BC checks.

**Deliverable:** examples/tests that fail if:

* classification-derived type constructors are wrong,
* type equality isn’t “rewrite in classifier”,
* comprehension obligations aren’t generated/checked,
* BC obligations aren’t generated/checked.

**Exit criterion:** changes to kernel semantics produce immediate, local test failures in the intended area.

(Use CwF/CwR literature as the semantic yardstick for what “comprehension exists + substitution functorial” means. ([arXiv][3]))

---

## Advanced but planned extensions (do after the foundation is stable)

### Phase 12 — Add NbE (just for selected modes) with gluing as the correctness story

**Goal:** allow binder-aware definitional computation in classifiers (needed for direct λ-cube-style Π/∀ computation at the type level).

* Extend the “definitional fragment” framework:

  * a mode may declare “definitional equality is TRS” or “definitional equality is NbE”.
* For NbE modes, implement:

  * semantic evaluation into a Kripke/presheaf model over contexts,
  * reify/reflect for normal forms.

Use **normalization by gluing** as the meta-theory that explains why this is modular and why modalities interact correctly (synthetic Tait computability is an internalized gluing method). ([drops.dagstuhl.de][2])

**Exit criterion:** a classifier mode can express and normalize β/η-style computation with binders in definitional equality without breaking the rest of the kernel.

### Phase 13 — Optional deepest unification: “types are full diagrams” with extrinsic typing

**Goal:** if you want to go all the way and make port objects themselves represented by general diagrams (not just code-term ASTs), you will almost certainly move to:

* **untyped/raw diagram syntax** + typing judgments (extrinsic typing),
* conversion checks that are either:

  * algorithmic only for declared normalizing fragments, or
  * proof-relevant elsewhere (explicit coercions).

This is a big step; it is compatible with the foundation above because classification, comprehension, and BC obligations already push you toward a CwR/MCwR semantics where “typing is structure, not a datatype”. ([pure.uva.nl][5])

---

## Summary of the plan in one sentence

1. eliminate `TypeExpr` by representing port objects as classifier-mode code terms; 2) make `classifiedBy` a universe-of-codes edge in mode theory; 3) define type equality as code equality via per-mode definitional normalization; 4) require and check comprehension/substitution structure (CwF-presented, CwR-specified); 5) generate and check Beck–Chevalley coherence for modalities; 6) keep the normalization engine extensible (TRS now, NbE/gluing later). ([arXiv][3])

[1]: https://arxiv.org/abs/1904.00827?utm_source=chatgpt.com "[1904.00827] Categories with Families: Unityped, Simply ..."
[2]: https://drops.dagstuhl.de/storage/00lipics/lipics-vol131-fscd2019/LIPIcs.FSCD.2019.25/LIPIcs.FSCD.2019.25.pdf?utm_source=chatgpt.com "Gluing for Type Theory - DROPS"
[3]: https://arxiv.org/pdf/1904.00827?utm_source=chatgpt.com "Unityped, Simply Typed, and Dependently Typed"
[4]: https://arxiv.org/pdf/2301.11842?utm_source=chatgpt.com "Normalization for Multimodal Type Theory"
[5]: https://pure.uva.nl/ws/files/62028111/Thesis.pdf?utm_source=chatgpt.com "Abstract and Concrete Type Theories - Research Explorer"
[6]: https://uemurax.github.io/pdfs/wg6-2023-04-slides.pdf?utm_source=chatgpt.com "Towards modular proof of normalization for type theories"
