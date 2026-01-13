# INSTRUCTIONS.md (REPLACEMENT)

This project is being refocused around a single unifying idea:

> **A “doctrine” is a typed, modular, equational presentation of compositional structure (no CCC/SMC special-casing), together with optional rewrite orientation and coherence data.**
>
> Surface languages are *defined by elaboration into doctrines*.
> Backends are *models/interpretations of doctrines*, with semantics swappable (à la compiling-to-categories / `concat`).

The current repository already contains a useful untyped first-order rewrite kernel and a modular doctrine expression language. The new plan keeps the spirit (generic, modular, rewrite/coherence-capable) but upgrades the kernel to **typed (many-sorted, GAT-style dependent sorting)**, which is required to support realistic categorical doctrines without ill-typed rewriting or meaningless critical pairs.

---

## Quick summary of the refactor

### What stays conceptually
- Generic rewriting (not tied to CCC/SMC/STLC).
- Modular composition of theories/doctrines via “imports + renaming + sharing”.
- Coherence obligations + joiners (proof objects) as *first-class*.

### What changes
- Replace the untyped FO `Term` kernel with a **typed core term language**:
  - **Sort constructors** like `Obj`, `Hom(A,B)`, `Ty`, etc.
  - **Operations** with **dependent telescopes** (arguments may determine the result sort).
  - Equations/rules are between **well-typed terms** in an explicit telescope/context.
- Extend doctrine modularity to cover **sort constructors + operations**, not just symbols.
- Keep completion/coherence optional and scalable: the system must be usable even when confluence/termination are not decidable globally.

---

# Implementation stages (ACTIONABLE)

Each stage ends with: **(a) build passes**, **(b) tests pass**, and **(c) at least one example doctrine works end-to-end**.

The coding agent should implement stages in order. Do not try to implement all future extensions in one pass.

---

## Stage 0 — Preparation (minimal disruption)
**Goal:** Keep the current code building while introducing new modules in parallel.

1. Create a new namespace for the new kernel:
   - `src/Strat/Kernel/...` (preferred) or `src/Strat/Meta2/...`.
   - Do **not** delete `src/Strat/Meta/...` yet.

2. Add a top-level “migration test” that ensures both kernels compile:
   - Existing tests continue to run (`test/Spec.hs`).
   - Add a new test group `Strat.Kernel` with placeholder tests.

3. Add a `CHANGELOG.md` entry describing the shift to typed doctrines.

---

## Stage 1 — Typed doctrine kernel: signatures + typed terms + substitution
**Goal:** Introduce the *new* core representation of doctrines and terms. No modular doctrine composition yet.

### 1.1 Add signatures (sort constructors + operations)
Create `Strat.Kernel.Signature`:

- Names:
  - `newtype SortName = SortName Text`
  - `newtype OpName   = OpName Text`

- **Sort constructors**: a sort is a constructor applied to **index terms**:
  - Example sort expressions: `Obj`, `Hom(A,B)`, `Ty`, `Ctx`, …
  - Representation:
    ```hs
    data Sort = Sort SortName [Term]    -- "Hom" [A,B], "Obj" []
    ```
  - Each sort constructor has an arity and expects index terms of particular sorts:
    ```hs
    data SortCtor = SortCtor
      { scName      :: SortName
      , scParamSort :: [Sort]          -- sorts of each index term
      }
    ```
  - (This is already “dependent enough” for `Hom(A,B)` because the dependency is via the *term indices*.)

- **Operations** with dependent telescopes:
  - Operations have argument binders; later argument sorts may mention earlier binders.
  - Output sort may mention binders.
  - Representation:
    ```hs
    data Binder = Binder { bVar :: Var, bSort :: Sort }
    data OpDecl = OpDecl { opName :: OpName, opTele :: [Binder], opResult :: Sort }
    ```
  - `Var` is scoped to avoid capture/collisions across rules/ops:
    ```hs
    newtype ScopeId = ScopeId Text
    data Var = Var { vScope :: ScopeId, vLocal :: Int } deriving (...)
    ```
  - Convention: binders for an `OpDecl` live in scope `ScopeId ("op:" <> opName)`.

- Signature container:
  ```hs
  data Signature = Signature
    { sigSortCtors :: Map SortName SortCtor
    , sigOps       :: Map OpName OpDecl
    }
  ```


### 1.2 Typed core terms

Create `Strat.Kernel.Term`:

* Terms are **always annotated** with their sort (cache the sort; do not recompute repeatedly):

  ```hs
  data TermNode
    = TVar Var
    | TOp  OpName [Term]

  data Term = Term
    { termSort :: Sort
    , termNode :: TermNode
    }
  ```

* Provide smart constructors:

  * `mkVar :: Sort -> Var -> Term`
  * `mkOp  :: Signature -> OpName -> [Term] -> Either TypeError Term`

    * Checks arity and telescope sorts *sequentially*, instantiating binders as it goes.
    * Computes result sort by substituting binders in `opResult`.

* Implement **substitution** over terms **and** within sorts:

  * `type Subst = Map Var Term`
  * `applySubstTerm :: Subst -> Term -> Term`
  * `applySubstSort :: Subst -> Sort -> Sort`
  * (Substitution must traverse into the index terms inside `Sort`.)

* Occurs check is needed (avoid cyclic substitutions). Keep the “seen set” approach from `Strat.Meta.Term.FO.applySubst` as a safety net.

### 1.3 Matching and unification (typed)

Create `Strat.Kernel.Unify`:

* `match :: Term -> Term -> Maybe Subst` (pattern vars occur only on LHS; typical rewrite matching)
* `unify :: Term -> Term -> Maybe Subst` (MGU-ish; used for critical branchings)

Both must be **type-aware**:

* When attempting to bind `Var v` to term `t`, ensure:

  * `termSort (Var v)` and `termSort t` are compatible.
  * Compatibility is not mere equality: it must recursively unify sorts:

    * Sorts unify only if `SortName` matches and their index terms unify.

Implementation approach:

* Write `unifySort :: Sort -> Sort -> Maybe Subst` which unifies index terms.
* `unifyTerm` first unifies sorts (accumulating substitution), then unifies structure.

Do not try to solve general dependent higher-order unification: this is **first-order** unification over a mutually recursive (Term, Sort) syntax.

### 1.4 First example doctrine in the new kernel

Create `Strat.Kernel.Examples.Monoid` (ported from `Strat.Meta.Examples.Monoid`), but now typed:

* Define a single sort ctor:

  * `Obj : Sort` (no indices)
* Define ops:

  * `e : Obj`
  * `m : Obj -> Obj -> Obj`
* Define equations/rules in a telescope `(x:Obj) (y:Obj) (z:Obj)`.

At the end of Stage 1, you should be able to build typed terms like `m(e,x)` and rewrite them.

---

## Stage 2 — Typed rewriting, critical branchings, and joiners

**Goal:** Port the current rewrite kernel to the typed term representation.

### 2.1 Rewrite rules and presentations (typed)

Create `Strat.Kernel.Rule` and `Strat.Kernel.Presentation`:

* Rules keep the existing metadata:

  ```hs
  data RuleClass = Structural | Computational
  data Orientation = LR | RL | Bidirectional | Unoriented
  ```

* Equations now include a telescope/context:

  ```hs
  data Equation = Equation
    { eqName   :: Text
    , eqClass  :: RuleClass
    , eqOrient :: Orientation
    , eqTele   :: [Binder]     -- variables + sorts (well-scoped)
    , eqLHS    :: Term
    , eqRHS    :: Term
    }
  ```

* A presentation contains a signature + equations:

  ```hs
  data Presentation = Presentation
    { presName :: Text
    , presSig  :: Signature
    , presEqs  :: [Equation]
    }
  ```

**Invariant:** every equation must be well-typed:

* `eqLHS` and `eqRHS` have identical `termSort`.
* all vars in LHS/RHS are from `eqTele`’s scope (by `vScope` + `vLocal`).

### 2.2 Rewrite system compilation (policies remain)

Port `Strat.Meta.RewriteSystem` to `Strat.Kernel.RewriteSystem`:

* Keep `RuleId`, `RuleDir`, `RewritePolicy` patterns from the old kernel.
* Compilation now produces oriented `Rule`s with typed terms.

### 2.3 Rewriting engine (typed)

Port `Strat.Meta.Rewrite` to `Strat.Kernel.Rewrite`:

* Rewriting is the same shape:

  * enumerate redexes by term positions
  * pattern-match rule LHS against subterm
  * replace with RHS instantiated by the match substitution

But now:

* `match` must be the typed match from Stage 1.
* `applySubstTerm` updates sorts inside the rewritten term; no re-typecheck should be needed if match is correct.

### 2.4 Critical branchings (typed)

Port `Strat.Meta.CriticalPairs` to `Strat.Kernel.CriticalPairs`:

* Keep `CPMode` (All / OnlyStructural / Mixed).

* Freshening: replace old `Ns` logic with **scopes**:

  * For overlap of `r1` and `r2`, rename all vars in each rule telescope to fresh `ScopeId`s:

    * `ScopeId ("cp:" <> ridEq r1 <> ":0")`
    * `ScopeId ("cp:" <> ridEq r2 <> ":1")`
  * Implement `renameScope :: ScopeId -> ScopeId -> Term/Sort/Equation -> ...`

* Unification uses `unify` from Stage 1 (typed).

### 2.5 Coherence obligations + joiners (typed)

Port `Strat.Meta.Coherence` to `Strat.Kernel.Coherence`:

* Keep:

  * `Obligation = CriticalPair + kind`
  * `Joiner = joinTerm + leftDerivation + rightDerivation`
  * `validateJoiner` replays derivations using `applyStep`.

At end of Stage 2:

* The monoid example should produce critical pairs and obligations.

---

## Stage 3 — Typed modular doctrine composition (module/colimit layer)

**Goal:** Replace/upgrade `Strat.Meta.DoctrineExpr` so doctrine libraries work with typed signatures.

### 3.1 Replace DoctrineExpr with typed version

Create `Strat.Kernel.DoctrineExpr`:

Current `DocExpr` supports `And`, `RenameEqs`, `RenameSyms`, `ShareSyms`.
Replace it with:

```hs
data DocExpr
  = Atom Text Presentation
  | And DocExpr DocExpr
  | RenameEqs  (Map Text Text) DocExpr
  | RenameOps  (Map OpName OpName) DocExpr
  | RenameSorts (Map SortName SortName) DocExpr
  | ShareOps   [(OpName, OpName)] DocExpr
  | ShareSorts [(SortName, SortName)] DocExpr
```

**Qualifying/importing:**

* Retain the old “namespace qualification” behavior from `Strat.Meta.DoctrineExpr`:

  * When importing `Atom ns pres`, qualify:

    * sort ctor names
    * op names
    * equation names
  * by prefixing them with `ns <> "."`.
* This ensures `A & B` is disjoint by default.

**Validation for sharing:**

* When sharing operations (`ShareOps`), require definitional equality of:

  * telescope length
  * binder sorts (alpha-equivalent up to binder renaming)
  * result sort
* When sharing sorts (`ShareSorts`), require definitional equality of their param sorts.

### 3.2 Presentation merging (signatures + equations)

* `And` merges:

  * sort ctors (disjoint union)
  * op decls (disjoint union)
  * equations (concatenation)
* After merges, reject duplicates (unless they are explicitly shared).

### 3.3 Port DSL or temporarily drop it

You have two acceptable routes:

**Route A (preferred): extend the existing DSL**

* Update `Strat.Meta.DSL.AST/Parse/Elab` into `Strat.Kernel.DSL.*`
* Add syntax for sort ctor and op declarations inside `where { ... }`.
* Example DSL sketch:

  ```
  doctrine Monoid where {
    sort Obj;
    op e : Obj;
    op m : (a:Obj) (b:Obj) -> Obj;          -- telescope form
    computational assoc : (x:Obj) (y:Obj) (z:Obj) |- m(m(x,y),z) -> m(x,m(y,z));
  }
  ```
* Keep doctrine expressions (`&`, `@`, `rename`, `share`) mostly the same, but expanded to `ops` and `sorts`.

**Route B (short-term): remove DSL from the critical path**

* Keep DSL tests but mark them skipped, and reintroduce once the kernel stabilizes.
* Use Haskell constructors for doctrines meanwhile.

At end of Stage 3:

* Port the existing DoctrineExpr tests (currently in `test/Spec.hs` under `DoctrineExpr`) to the typed layer.
* Ensure the “disjoint by default, shared when asked” story still works.

---

## Stage 4 — Relative rewriting and coherence “modulo structural”

**Goal:** Make “structural vs computational” operational, not just metadata.

This is a *targeted* implementation: do not attempt fully general rewriting modulo an arbitrary theory.

### 4.1 Introduce a two-phase normalization interface

Add `Strat.Kernel.Relative`:

* Let `W` be the set of **structural** rules (often invertible).
* Let `R` be the set of **computational** rules (often oriented toward evaluation).

Provide:

* `normalizeW :: Fuel -> Term -> Term` (apply only structural rules, using a deterministic strategy)
* `stepR      :: Term -> [Redex]`     (one-step computational)
* `normalizeR_mod_W :: Fuel -> Term -> Term`

  * alternates: normalizeW, one R-step, normalizeW, …

This is not fully general, but it gives a practical “rewrite modulo structure” mechanism that scales.

### 4.2 Critical branchings for relative coherence

Adjust `CPMode` / obligation generation to target the branchings that matter:

* structural/structural → commutation obligations
* structural/computational → “evaluation respects structure” obligations
* computational/computational → optional (often not coherence; sometimes evaluation confluence)

End of Stage 4:

* Add at least one doctrine where structural rules exist and are used in the relative normalizer.

---

## Stage 5 — Surface syntax layer (elaboration into doctrines)

**Goal:** Implement the missing “S layer” in a way that does not bake CCC/SMC into the core.

### 5.1 Define the surface language interface

Create `Strat.Surface`:

A surface syntax is:

* an AST (possibly with binding),
* plus an elaborator that outputs **kernel terms** in a selected doctrine.

Minimal interface:

```hs
class SurfaceLang ast where
  elaborate :: DoctrineInstance -> ast -> Either ElabError Term
```

Where `DoctrineInstance` contains:

* the chosen doctrine presentation
* name-resolution hooks
* optional “context kit” for surface variables

### 5.2 Start with one demonstration surface language

Implement a tiny example surface language that elaborates to a doctrine without assuming CCC/SMC in the kernel:

* e.g. a “combinator surface syntax” where syntax directly names doctrine ops and supplies explicit arguments.
* This avoids binders and lets you validate the architecture quickly.

### 5.3 Binding/presheaf story (deferred to Stage 6+)

Do not implement full presheaf/second-order binding yet. See [SPEC] sections below for the intended endpoint.

---

## Stage 6 — Backend semantics and `concat` integration

**Goal:** Interpret doctrine terms into swappable semantics.

### 6.1 Define the backend API as “models of a presentation”

Create `Strat.Backend`:

* A backend provides interpretations of:

  * sort constructors (as host-side sets/types/objects)
  * operation symbols (as host-side functions/morphisms)
* Equations must be respected:

  * either by construction (proof objects),
  * or by testing/quickcheck, or
  * by rewriting normalization equivalence (if convergence holds).

Minimal interface:

```hs
data Model = Model
  { interpOp   :: OpName -> [Value] -> Either RuntimeError Value
  , interpSort :: Sort -> Either RuntimeError SortValue
  }
```

### 6.2 `concat`-style compilation hook

Provide a separate module that compiles kernel `Term` into a Conal-style categorical expression AST, which then:

* either runs via interpreter
* or becomes the target of a compiler/plugin

No special casing of CCC/SMC is allowed in the *kernel*; CCC/SMC conveniences live in doctrine libraries and compilation passes.

---

## Stage 7 — Performance work (only after correctness)

**Goal:** Make the system usable.

Implement in this order:

1. **Rule indexing** for rewriting:

   * index rules by root operator symbol (and possibly by sort)
   * avoid scanning all rules at all positions
2. **Hash-consing / sharing** of terms (optional):

   * reduces memory and speeds equality checks
3. **Critical pair bounding**:

   * allow size/depth limits
   * allow user-selected subsets of rules
4. **Incremental obligation generation**:

   * don’t generate all CPs eagerly; generate on demand per doctrine module

---

# Architecture specification (NON-ACTIONABLE)

This section is a rigorous spec of the intended endpoint. It is **not** a checklist for immediate coding.

The coding agent should treat it as a reference document for design decisions.

---

## [SPEC] Core mathematical objects

### [SPEC] Doctrine presentations

A doctrine presentation is a triple `(Σ, E, O)`:

* `Σ` (signature):

  * sort constructors `C : (s1,...,sn) -> Sort` where each argument `si` is itself a sort (but may be applied to term indices).
  * operations `op : (x1:S1) ... (xn:Sn) -> R`
    where the telescope may be dependent, and result sort `R` may mention `xi`.

* `E` (equations):

  * each equation is in a telescope/context `Γ = (x1:S1,...,xn:Sn)`:
    `Γ ⊢ lhs = rhs : S`
  * equations carry metadata:

    * class: Structural vs Computational
    * orientation: LR / RL / Bidirectional / Unoriented

* `O` (optional coherence/completion data):

  * critical branching schema selection
  * joiners (proof objects) for selected branchings
  * termination orders / completion hints (optional)

No categorical structure is hardcoded: category/monoidal/CCC/etc. are just *libraries* expressed as presentations.

---

## [SPEC] Kernel computation: rewriting and coherence

### [SPEC] Typed rewriting

Rewriting is defined only for well-typed terms. A rewrite rule is an oriented equation:
`Γ ⊢ l -> r : S`

A rewrite step on a closed term `t` consists of:

* a position `p` in `t`
* a match substitution `σ` such that `σ(l)` equals the subterm at `p`
* replacement of that subterm by `σ(r)`

Typing is preserved by construction if `match` is type-respecting.

### [SPEC] Critical branchings and obligations

Critical branchings come from overlaps of left sides of oriented rules (or selected pairs), producing:

* a peak term `u`
* two diverging reducts `u -> v` and `u -> w`

Obligations are generated depending on policy:

* structural/structural overlaps often demand commutation/coherence
* structural/computational overlaps demand “evaluation respects structure”
* computational/computational overlaps demand confluence only if desired

Joiners are explicit confluence witnesses:
`v ->* j <-* w`

The system never assumes global convergence; instead it:

* computes obligations when it can,
* stores joiners when provided,
* and can validate joiners by replaying rewrite steps.

---

## [SPEC] Modularity and “doctrine libraries”

### [SPEC] Module composition as presentation colimits

Doctrine composition is governed by colimits in the category of presentations:

* disjoint union + qualification (default import)
* renaming (presentation morphisms)
* sharing/identification (pushouts / coequalizers on names)

Operationally:

* `A & B` = disjoint union after qualification
* `share ops {A.f = B.f} in (...)` introduces identification constraints (validated by type equality)

This scales to:

* multi-file doctrine libraries
* parameterized doctrines (future)
* derived doctrines (future)

---

## [SPEC] Surface syntax via elaboration

### [SPEC] Surface syntax is not the kernel

The kernel is not meant to directly expose user-friendly syntax. Instead:

A surface language consists of:

1. a syntax (AST, possibly with binding)
2. an elaboration map into the kernel terms of a doctrine

Elaboration is a homomorphism/translation:

* surface constructs map to kernel op symbols + terms
* binding in the surface is eliminated by elaboration into doctrine structure (e.g., CCC closure operators, linear combinators, etc.)

### [SPEC] Presheaves / second-order approach (future)

The long-term endpoint for binding and contexts is:

* define surface syntax as an initial model in a presheaf category of contexts,
* or via second-order generalized algebraic theories,
* with elaboration as a morphism of such presentations.

This is compatible with dependent upgrades (e.g. representable-map categories), but not required initially.

---

## [SPEC] Backend semantics and semantics swapping

A backend is a model of a presentation:

* interprets sort constructors and operation symbols in a target semantic universe (categories, profunctors, circuits, Haskell embeddings, etc.)
* validates equations either:

  * by proof,
  * by rewriting normalization equivalence (if convergent),
  * or by testing.

**Semantics swapping**:

* the same kernel term can be interpreted in different models
* hence different semantics without changing surface code, provided elaboration targets the same doctrine interface.

---

## [SPEC] Future extensions (do not implement now)

### [SPEC] Polygraphs / diagrammatic rewriting

If/when needed for performance/coherence on monoidal-style theories:

* add an alternative internal representation for terms as string diagrams
* implement overlaps/rewriting as graph rewriting with boundaries
* keep the doctrine interface unchanged; only the internal computation changes

### [SPEC] Representable-map categories / abstract type theories

If/when dependent type theories become first-class in the surface layer:

* enrich the “context kit” to a comprehension/CwF/representable-map structure
* treat doctrines as presentations that generate such structures
* this primarily upgrades the **surface/binding/context** story, not the kernel rewrite core

### [SPEC] Framed bicategories / monoidal fibrations

If/when semantics targets include base-change-heavy bicategorical settings:

* use a framed bicategory/equipment as the semantic metatheory
* treat doctrine operations as living in such a structure
* kernel remains unchanged; backends become richer

---

# Migration notes from current code (ACTIONABLE)

The current repository has:

* `Strat.Meta.*` implementing untyped FO rewriting + DoctrineExpr + a DSL.
  Use it as scaffolding, but plan to retire it after Stage 3.

Concrete mapping:

* `Strat.Meta.Term.FO`        → `Strat.Kernel.Term`
* `Strat.Meta.Term.Class`     → **delete** (after kernel is stable); replace with concrete typed operations
* `Strat.Meta.Rewrite*`       → `Strat.Kernel.Rewrite*`
* `Strat.Meta.CriticalPairs`  → `Strat.Kernel.CriticalPairs` (typed)
* `Strat.Meta.Coherence`      → `Strat.Kernel.Coherence` (typed)
* `Strat.Meta.DoctrineExpr`   → `Strat.Kernel.DoctrineExpr` (typed, with sorts+ops)
* `Strat.Meta.DSL.*`          → `Strat.Kernel.DSL.*` (extended) or temporarily sidelined

Testing strategy:

* Keep old tests passing until the new kernel reproduces:

  * matching/unification sanity
  * deterministic rewrite ordering
  * monoid critical pairs non-empty
* Then port tests to the new kernel one group at a time and delete old kernel tests.

---

# Definition of done (high-level)

This project’s “v1 architecture” is complete when:

1. Users can define a doctrine library with sorts/ops/equations modularly.
2. Users can define at least one surface syntax that elaborates into a chosen doctrine.
3. Users can define at least two distinct backends/models interpreting the same doctrine (semantics swapping).
4. The kernel can optionally generate/validate coherence obligations (even if not total/automatic).
5. Performance is acceptable on small-to-medium examples due to rule indexing and bounded CP generation.

```
::contentReference[oaicite:0]{index=0}
```
