## Issue remedy instructions (fix these before starting Phase 3)

These are the things I would correct now because Phase 3 will lean on them and it’s cheaper to tighten them before the big refactor.

### 1) Detect conflicts when merging `mtClassifiedBy` (don’t use left-biased `Map.union` silently)

**Where:** `src/Strat/Poly/DSL/Elab.hs`, function `mergeIface`
Currently:

```hs
mtClassifiedBy = M.union (mtClassifiedBy (dModes doc0)) (mtClassifiedBy (dModes doc1))
```

`M.union` is left-biased: conflicting declarations for the same mode name are silently dropped. This is risky once classification starts influencing type/object meaning (Phase 3+).

**Remedy:**

* Replace with a merge that:

  * accepts identical `ClassificationDecl`s, and
  * errors on conflicts (different classifier or different universe).
* Use `M.unionWithKey` and compare `cdClassifier` and `cdUniverse` structurally (after normalizing mod spines on universes if you already have a normalization function for object expressions).

**Expected behavior:** if an interface is imported twice identically it merges; if two imports disagree, you get a clear “conflicting classifiedBy for mode …” error.

### 2) Remove duplicated well-formedness checks in `classificationOrder`

**Where:** `src/Strat/Poly/ModeTheory.hs`

`checkWellFormed` already calls `checkClassificationWellFormed`, and `classificationOrder` calls it again.

**Remedy:**

* Make `classificationOrder` assume the mode theory is already well-formed (or have a private helper `classificationOrderUnchecked`).
* Keep `checkWellFormed` as the “public entrypoint” that calls checks in the right order.

This is not a correctness bug, but it will matter once this is called more often (Phase 3 will likely query classification info repeatedly).

### 3) In `renameModeTheory`, avoid “overwrite on collision” for classifiedBy renaming

**Where:** `src/Strat/DSL/Elab.hs`, `renameModeTheory`

You fold `M.insert` into a new map. If renaming ever becomes non-injective (or a future refactor accidentally causes collisions), you silently overwrite.

**Remedy:**

* Replace local `addClassification` helper with:

  * “insert unless key absent; if present, require equality else error”.
* (Even if you believe renamings are injective today, this is cheap protection.)

### 4) Decide what `cdTag` is for and enforce invariants (or remove until Phase 7)

**Where:** `src/Strat/Poly/ModeTheory.hs`, `ClassificationDecl`
`cdTag` is parsed and stored but unused. That’s fine, but Phase 3 will need a stable story about how tags affect name resolution or universe selection.

**Remedy options:**

* If tags are for future ergonomics only: explicitly document “cdTag unused until Phase 7” in `SPEC.md` and do nothing else.
* If tags are meant to be semantic: start enforcing uniqueness of tags per classified mode now, or forbid them until Phase 7.

I recommend the first option (document and postpone) to reduce Phase 3 scope.

---

## Phase 3 implementation instructions (CodeTerm infrastructure + object classifier queries)

This is written to match `PLAN.md` Phase 3: introduce a CodeTerm representation and make “objects are codes in a classifier universe” structurally real in the kernel, without yet implementing the Phase 5 definitional fragment rewrite engine.

### Phase 3 target invariants

After Phase 3:

1. You can ask, for any “object of mode M”:

* whether it is *classified*, and if so:

  * its classifier mode `K`
  * its universe object `U` in `K`.

2. Normalization/equality hooks exist in the right place:

* `normalizeObj(tt, obj)` normalizes the *code* in the classifier (Phase 5 will strengthen the notion of normalization).
* `objEq(tt, obj1, obj2)` compares via normalized codes.

3. Term-index normalization still works:

* If an object contains term indices (your current `OATm` payload), those indices are still normalized correctly with respect to their expected sorts, contexts, and mode theory.

### Design choice you need to commit to now

Phase 3 should stop treating an object’s *mode* as “the mode of the syntax node’s head constructor”. That assumption breaks under classification.

You need two notions:

* **Owner mode**: the mode whose *objects* these are (e.g., “this is a Tm-object/type”).
* **Code mode**: the mode in which the code for the owner object lives (its classifier mode).

In the existing codebase, `objMode` currently plays both roles. Phase 3 must split them.

### Step 1 — Introduce `CodeTerm` and make `Obj` carry owner-mode separately

**Files to edit:**

* `src/Strat/Poly/Syntax.hs`
* `src/Strat/Poly/Obj.hs`
* Any module pattern-matching on `OVar`/`OCon`/`OMod`

**Mechanical refactor:**

1. Rename the existing `Obj` AST into a new type `CodeTerm` (or `ObjExpr`), and rename constructors to avoid confusion.

Current:

```hs
data Obj = OVar ObjVar | OCon ObjRef [ObjArg] | OMod ModExpr Obj
```

Phase 3 shape:

```hs
data Obj = Obj
  { objOwnerMode :: ModeName
  , objCode      :: CodeTerm
  }

data CodeTerm
  = CTVar ObjVar
  | CTCon ObjRef [CodeArg]
  | CTMod ModExpr CodeTerm

data CodeArg
  = CAObj Obj
  | CATm TermDiagram  -- keep TermDiagram for now (Phase 3 exit criterion is term-index normalization)
```

2. Provide helpers:

* `codeMode0 :: CodeTerm -> ModeName` (structural head-mode: from `ObjRef` or `ObjVar` or `CTMod` target).
* `objMode :: Obj -> ModeName` becomes `objOwnerMode` (keep `objMode` name if you want, but it must now mean owner-mode).

3. Update `ObjVar`:

* Keep `ovMode` for now as the **owner mode** of the object variable (so unification/matching in `UnifyObj` doesn’t need to change yet).
* In Phase 4 you will eliminate `ObjVar` anyway.

**Why this ordering:** it minimizes immediate blast radius: you can keep `UnifyObj` and other object-level operations mostly structural, but now objects explicitly carry the mode they belong to.

### Step 2 — Add classifier queries (the “Phase 3 deliverable module”)

**Add a new module:** `src/Strat/Poly/ObjClassifier.hs` (or similar).

Provide a minimal API:

```hs
-- Returns classifier info for an *owner mode*.
classifierOfMode :: ModeTheory -> ModeName -> Maybe ClassificationDecl

-- Helper accessors.
modeClassifierMode :: ModeTheory -> ModeName -> ModeName
modeUniverseObj    :: ModeTheory -> ModeName -> Maybe Obj

-- Code mode of an Obj (depends on classification and/or code head mode).
objCodeMode :: ModeTheory -> Obj -> ModeName
```

Recommended semantics:

* If `classifierOfMode mt m = Just (ClassificationDecl k u …)`:

  * `modeClassifierMode mt m = k`
  * `modeUniverseObj mt m = Just u`
* If no classification edge exists:

  * `modeClassifierMode mt m = m`
  * `modeUniverseObj mt m = Nothing` (explicitly “unclassified”)

**Important:** Do *not* fabricate an implicit universe for unclassified modes in Phase 3. You don’t have infrastructure for that yet; it will create false invariants.

### Step 3 — Rebase object normalization around owner-mode + code-mode

**Files to edit:**

* `src/Strat/Poly/ObjNormalize.hs`
* `src/Strat/Poly/Obj.hs`

Target changes:

1. Replace any logic that assumes `objMode obj == …` with owner-mode checks, and use `objCodeMode` when you need classifier/code mode.

2. Keep the current “deep normalization” behavior for term indices:

* Traverse `objCode` recursively:

  * `CAObj subObj` → normalizeObjDeep subObj
  * `CATm tm` → normalize term diagram with the expected sort (same behavior you already have)

3. Add/rename entrypoints:

* `normalizeObjDeepWithCtx :: TypeTheory -> [Obj] -> Obj -> Either Text Obj`
* `normalizeCodeTermDeepWithCtx :: … -> CodeTerm -> Either Text CodeTerm`

4. Phase 3 `normalizeObj` should:

* normalize term indices (existing behavior)
* normalize modality expressions (`normalizeObjExpr`-like behavior, but for `CodeTerm`)
* **do not** attempt Phase 5 “definitional fragment” reductions yet.

### Step 4 — Update unification/matching to use the wrapper shape

**Files to edit:**

* `src/Strat/Poly/UnifyObj.hs`
* `src/Strat/Poly/Match.hs` (and anywhere else that calls `unifyObjFlex`)

Work items:

1. Update `unifyObj` to unify `Obj` values by:

* checking `objOwnerMode` matches (or allowing mismatch only where you explicitly want it; default is “must match”)
* unifying the underlying `CodeTerm`.

2. Update all pattern matches from `OVar/OCon/OMod` to `CTVar/CTCon/CTMod` on the code.

3. Update occurs checks and free-variable computation to traverse:

* `Obj.objCode`
* `CodeArg.CAObj` recursively
* ignore `CATm` for object metavariable occurrences (term metas are separate)

4. Update diagnostics:

* `renderObj` should show both:

  * owner mode, and
  * rendered code term (with its own head mode visible via `ObjRef` as before).
    This will be critical when Phase 3 starts producing “wrong classifier” errors.

### Step 5 — Make elaboration classification-aware

This is the biggest Phase 3 change.

**File to edit:**

* `src/Strat/Poly/DSL/Elab.hs`

#### 5.1 Change object elaboration signature to accept an *expected owner mode*

Right now `elabObjExpr` infers/decides too much from the syntax (including using global lookup in `resolveTypeRef`).

New shape:

```hs
elabObjExpr
  :: Doctrine
  -> [ObjVar]              -- type vars (owner modes)
  -> [TmVar]               -- term vars
  -> Map ModName (ModeName, ModeName) -- sig params (existing)
  -> ModeName              -- expected owner mode
  -> RawPolyObjExpr
  -> Either Text Obj
```

Return `Obj { objOwnerMode = expectedOwnerMode, objCode = … }`.

#### 5.2 Resolve constructors in the classifier mode, not the owner mode

Compute:

* `k = modeClassifierMode (dModes doc) expectedOwnerMode`

Then update resolution logic:

* For unqualified constructors/vars that are used as constructors:

  * resolve them **in mode `k` only** (not global scan).
* For qualified references `M.X`:

  * interpret the qualifier as a **code-mode qualifier**, and require `M == k`.
  * if mismatch, error: “object of mode expectedOwnerMode is classified by k; constructor qualifier M is not allowed here”.

This gives you a clean invariant: “the code for an object of mode M is written using the vocabulary of its classifier mode”.

This is what makes classification operational in Phase 3 without yet redesigning the surface language.

#### 5.3 Keep parameter-checking semantics exactly as before

When you elaborate `CTCon ref args` in classifier mode `k`, you still:

* look up `TypeSig` / `TypeParamSig` for `ref`
* for each `TPS_Ty mArgOwner`:

  * recursively call `elabObjExpr … mArgOwner rawArg`
  * wrap as `CAObj`
* for each `TPS_Tm sortObj`:

  * elaborate as term argument (existing `elabTmTerm`)
  * wrap as `CATm`

The only difference is: the `ObjRef` being applied now lives in `k` (classifier vocabulary), not in `expectedOwnerMode`.

This preserves existing dependent/indexed type syntax and keeps Phase 3 contained.

#### 5.4 Universe elaboration for classification decls

In `applyPendingClassifications` you already elaborate the universe `U` as an `Obj`. After Phase 3’s wrapper change, you must elaborate it as:

* expected owner mode = classifier mode `K`
* so its `objOwnerMode = K` and its `objCode` is built in classifierOf(K) (or K itself if unclassified).

Then `ModeTheory.addClassification`’s universe-mode check must use `objOwnerMode` (not “code head mode”).

### Step 6 — Update kernel validation where `objMode` was used as “head mode”

**Files to audit and update:**

* `src/Strat/Poly/Graph.hs`
* `src/Strat/Poly/Doctrine.hs`
* `src/Strat/Poly/TermExpr.hs` and term conversion modules
* `src/Strat/Poly/Actions.hs`

Rule of thumb for Phase 3:

* If the check is about “what mode does this object belong to as a *port label*?” → use **owner mode**.
* If the check is about “what mode is this code written in / which mode theory should normalize it?” → use **classifier/code mode**.

Concretely:

* `validateDiagram` port label check should remain owner-mode equality:

  * `objOwnerMode portObj == dMode diag`.
* Any place that previously did `objMode sortTy` to decide which term TRS to use:

  * keep it as owner-mode (because term sorts are still objects of the term’s mode).
  * Phase 3 does **not** change term typing semantics.

### Step 7 — Tests and example programs to add for Phase 3

You need tests that demonstrate classification affects object elaboration and normalization behavior.

#### 7.1 Unit tests (Haskell)

Add a new test module e.g. `test/Test/Poly/ClassificationPhase3.hs`:

1. **Classifier-based constructor resolution**

* Build a doctrine with:

  * `mode Ty; type U @Ty;`
  * `mode Tm classifiedBy Ty via Ty.U;`
  * Code constructors in `Ty`, e.g. `type Unit @Ty; type Arr(a@Tm, b@Tm) @Ty;`
* Elaborate an object expression in owner mode `Tm`:

  * `Arr(Unit, Unit)` should succeed and produce `Obj{owner=Tm, code=CTCon (Ty.Arr) …}`
  * `Tm.Arr(Unit, Unit)` should fail with “constructor qualifier Tm not allowed; expected Ty”.

2. **Term-index normalization still works under wrapper**

* Extend doctrine:

  * `type Nat @Ty; gen Z : [] -> [Nat] @Ty; gen S : [Nat] -> [Nat] @Ty;`
  * `type Vec(n : Nat, a@Tm) @Ty;`
* Form an object in owner mode `Tm`: `Vec(S(Z), Unit)`
* Ensure `normalizeObjDeepWithCtx` still normalizes the `CATm` payload correctly (even if no rewrite happens, it should at least round-trip and preserve well-formedness).

#### 7.2 Example runner additions

Add a new passing run example, e.g. `examples/run/classification_phase3.ok.run.llang`:

* Define `Ty`, `U`, `Tm classifiedBy Ty via U`.
* Define code constructors in Ty (`Unit`, `Arr`).
* Define a `Tm` generator whose boundary uses `Arr(Unit, Unit)` (without `Ty.` qualifier if you want to test unqualified lookup in classifier; with qualifier if you want to test stricter behavior).

Add a new xfail example, e.g. `examples/run/xfail/classification_wrong_classifier.fail.run.llang`:

* Same setup, but use a constructor from the wrong mode in a `Tm` boundary (e.g., `Tm.Unit` or `Other.Unit`).
* Expect the new Phase 3 error message.

### Step 8 — SPEC updates required for Phase 3

`SPEC.md` already has the conceptual classification story. For Phase 3, add implementation-facing clarifications:

* A short subsection describing the two-mode notion:

  * owner mode (port label mode),
  * classifier/code mode (where its code is written),
  * and that Phase 3 attaches both explicitly.

* State Phase 3’s elaboration resolution rule explicitly:

  * “When elaborating an object for owner mode M, unqualified constructors are resolved in the classifier mode of M; qualified constructors must match that classifier mode.”

This is crucial to prevent future ambiguity.

---

## Phase 3 completion checklist

Use this as the “done” gate:

1. **Core refactor compiles**:

* All uses of `OVar/OCon/OMod` updated to `Obj{…}` + `CTVar/CTCon/CTMod`.

2. **Classifier query works**:

* A helper exists to compute classifier mode + universe for an owner mode, and it is used in elaboration (not just stored).

3. **Classification affects elaboration**:

* In a doctrine with `Tm classifiedBy Ty`, an object written in `Tm` must resolve constructors from `Ty` (or error clearly).

4. **Term-index normalization still works**:

* Existing normalization of embedded term indices still passes tests.

5. **No silent merges**:

* `mtClassifiedBy` merge now errors on conflicts (or requires equality).

6. **New tests/examples added**:

* At least one positive + one xfail demonstrating Phase 3 behavior.
