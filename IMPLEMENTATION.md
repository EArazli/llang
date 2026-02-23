# Phase 4 review (last 2 commits): issues, incomplete pieces, and fix instructions

## 1) Surface type elaboration treats **all bare identifiers** as fresh type metavariables

### Where

`src/Strat/Poly/Surface/Elab.hs`

Function: `elabSurfaceObjExpr`

Current behavior:

```hs
RPTVar name -> do
  mv <- mkTypeMetaVar doc mode name
  return $ mkObj mode $ CTMeta mv
```

### Why this is a problem

* It prevents surface programs from referring to **nullary type constructors** by name (e.g. `Unit`, `A`) unless written as `Unit()` (which the surface examples/tests do not do).
* It contradicts the intended “classified constructor resolution” behavior tested in `testSurfaceClassifiedTypeResolution` (expects `Unit` to resolve to `CTCon (ObjRef Ty Unit) []` when used as a `Tm`-mode type).
* It makes surface type annotations silently “hole-like”: typos become unconstrained metas instead of errors or constructor references.

### Minimal correct behavior

For `RPTVar name` in surface type positions:

1. Try to resolve `name` as a **nullary type constructor** in the appropriate classifier mode for `mode`.
2. If found and arity is 0 → elaborate to `CTCon ref []` (owner stays `mode`).
3. If not found → either:

   * (recommended) error (to catch typos), **or**
   * treat as a meta (backwards-compat “hole types”).

Given the repository already has surface programs like `in x:A;`, and doctrine declares `type A @M;`, the most consistent behavior is: **prefer constructor if it exists; else meta**.

### Agent instructions (implementation)

1. Edit `src/Strat/Poly/Surface/Elab.hs`, inside `elabSurfaceObjExpr`:

   * Replace the `RPTVar` branch with logic:

     * Compute classifier mode `cls <- modeClassifierMode (dModes doc) mode` (error if missing).
     * Look up type signature table in `dTypes doc` at `cls`.
     * If `(ObjName name)` exists and has 0 params:

       * Return `mkObj mode (CTCon (ObjRef cls (ObjName name)) [])`.
     * If exists but arity > 0:

       * Return error telling user to supply arguments (or use constructor syntax).
     * If not found:

       * Fallback to current meta behavior (or error; pick one policy and document).
2. Update/extend error messages to mention **classifier mode** when resolution fails, since that’s now how types are resolved.

### Agent instructions (tests)

Add/strengthen tests to ensure this is locked in:

* In `test/Test/Poly/Surface.hs`:

  * Extend `testSurfaceInOut` (or add a new test) to assert that the `A` in `in x:A;` elaborates to a `CTCon` (not `CTMeta`).
  * Keep `testSurfaceClassifiedTypeResolution` as the regression for classified modes.
* Ensure at least one surface test checks:

  * Unqualified `Unit` resolves to `CTCon` in the presence of classification `Tm ▷ Ty`.

---

## 2) Surface type constructor arguments are elaborated in the **wrong owner mode**

### Where

`src/Strat/Poly/Surface/Elab.hs`

Function: `elabSurfaceObjExpr`, branch `RPTCon rawRef args`

Current behavior:

```hs
args' <- mapM (elabSurfaceObjExpr doc mode) args
...
checkParam (PS_Ty m, argTy) =
  if objOwnerMode argTy == m then Right () else Left ...
```

### Why this is a problem

* Every argument is elaborated using the *outer* `mode`, even when the constructor’s parameter signature says the argument is an object in some other owner mode `m`.
* This makes any type constructor with cross-mode object parameters unusable in surface type annotations (it will fail the mode check even when the user wrote a correct expression).

### Agent instructions (implementation)

1. In `RPTCon rawRef args` branch:

   * After you obtain `sig <- lookupTypeSig doc ref`, do **signature-directed elaboration**:

     * Zip the raw `args` with `sigParams sig`.
     * For each `(paramSig, argRaw)`:

       * If `paramSig` is `PS_Ty m` → call `elabSurfaceObjExpr doc m argRaw`.
       * If `paramSig` is `PS_Tm sortTy` → keep current “surface: term arguments not supported” behavior (or implement term args later), but the error should mention the constructor and parameter index.
2. Remove the current `args' <- mapM (elabSurfaceObjExpr doc mode) args` since it is structurally wrong.

### Agent instructions (tests)

* Add a focused surface test:

  * Doctrine: two modes `M` and `N` (self-classified), declare a type constructor in `M` that takes an object parameter in `N`.
  * Surface type annotation uses that constructor and passes an `N`-mode object.
  * Expect surface elaboration succeeds and the argument’s owner mode matches `N`.

---

## 3) `expandModSpine` in unification recurses through `CTMod` with the wrong “inner owner” (latent correctness bug)

### Where

`src/Strat/Poly/UnifyObj.hs`

Function: `expandModSpine`

Current behavior:

```hs
CTMod me innerCode -> do
  inner' <- expandModSpine (mkObj (objOwnerMode ty) innerCode)
  code' <- expandPath me (objCode inner')
  return ty { objCode = code' }
```

### Why this is a problem

* Conceptually, the inner code of `CTMod me _` is an object in `meSrc me`, not `objOwnerMode ty` (which corresponds to `meTgt me` for well-typed terms).
* Today this is mostly “latent” because `expandModSpine` doesn’t enforce owner-mode consistency, but it will become a real bug the moment you:

  * add mode-sensitive normalization/validation inside expansion, or
  * reuse this helper elsewhere expecting well-typed recursion.

### Agent instructions (implementation)

1. Change the recursive call to:

   * `inner' <- expandModSpine (mkObj (meSrc me) innerCode)`
2. Add a defensive check (recommended):

   * If `objOwnerMode ty /= meTgt me`, error with a clear message (this catches malformed objects early).

### Agent instructions (tests)

* Add a small unit test in `test/Test/Poly/UnifyObj.hs` (or a new file) that:

  * Builds an object with `CTMod` and nested `CTMod` inside it.
  * Calls `unifyObjFlex` on two equivalent objects where expansion is required.
  * This should remain stable as future refactors add checks.

---

## 4) PLAN.md vs implementation: scope discipline for code metas uses **owner mode**, plan mentions **classifier portion**

### Where

`src/Strat/Poly/UnifyObj.hs`, function `bindTyVar`

Current behavior:

* Computes `allowed` indices by filtering `tmCtx'` entries with `objOwnerMode == ownerV`.

PLAN.md (Phase 4) says:

* “scope governed by the classifier’s portion of the telescope”.

### Why this matters

* If future phases expect “code terms live in classifier mode, so their allowable bound indices come from the classifier slice”, the current check is enforcing a different rule.
* This is the kind of mismatch that will explode later when you attempt more dependent pattern matching and code-level definitional equality (Phase 5+).

### Agent instructions (resolution path)

Do **one** of the following, explicitly and consistently:

**Option A (update implementation to match PLAN):**

1. Decide “classifier portion” precisely:

   * Likely: use `modeClassifierMode ownerV` as the mode whose tmCtx slice is in scope.
2. Change `allowed` computation to filter by that classifier mode rather than ownerV.
3. Update `boundTmIndicesObj` / `boundTmIndicesTerm` invariants if needed so that indices are taken from classifier slice.
4. Add tests that demonstrate code metavars can depend on classifier-slice variables, and cannot escape them.

**Option B (update PLAN/SPEC to match implementation):**

1. Keep the current owner-slice scope rule.
2. Update `PLAN.md` Phase 4 text and add a short note in `SPEC.md` (or a dedicated invariants section) explaining why owner-slice is the intended rule.

Given Phase 5 is about definitional equality of codes “as terms in classifier”, Option A is more coherent long-term, but pick based on intended semantics.

---

## 5) Known limitation (not a Phase 4 regression, but now more visible): surface types still disallow term arguments

### Where

`src/Strat/Poly/Surface/Elab.hs` in `checkParam`:

```hs
PS_Tm _ -> Left "surface: term arguments are not supported in surface type annotations"
```

### Impact

Surface programs cannot write term-indexed types (e.g., `Vec(n, A)`), even though the core object language supports term arguments.

### Agent instructions

* Document as a limitation in `SPEC.md` surface section, **or**
* Treat as a Phase 5/6 prerequisite depending on whether Phase 5 needs dependent surfaces.

---

# Phase 5 implementation plan: “Definitional equality engine via per-mode definitional fragments”

This plan is structured as actionable agent tasks, including concrete file touch-points and tests.

## Phase 5 goals (acceptance criteria)

1. **Single normalization/equality service** is used everywhere:

   * term diagram normalization,
   * object/code normalization,
   * unification comparisons.
2. For each mode `M`, compute its **definitional fragment**:

   * admissible definitional symbols (term functions),
   * admissible computational rules (from `Cell2` marked computational),
   * compiled per-mode TRS with termination + confluence checks.
3. Provide a fuel-free `normalizeCodeTerm` entrypoint that is the basis of **type equality**:

   * Normalization of object equality becomes “normalize code in appropriate mode fragment + compare”.
4. Existing tests continue to pass, and new tests lock in the new centralization behavior.

## Non-goals (explicitly defer)

* Full code-level rewriting of `CTCon` using classifier-mode gens (this likely overlaps Phase 6).
* Adding surface support for term-indexed type annotations unless required by downstream tests.

---

## Work breakdown

## 1) Introduce a first-class “definitional engine” API

### Files

* New: `src/Strat/Poly/DefEq.hs` (or `Definitional.hs`)
* Touch: `src/Strat/Poly/TypeTheory.hs`
* Touch: `src/Strat/Poly/Doctrine.hs`
* Touch: `src/Strat/Poly/ObjNormalize.hs`
* Touch: `src/Strat/Poly/UnifyObj.hs`

### Agent instructions

1. Create a new module that owns **all** normalization and definitional equality entrypoints:

   * `normalizeTermDiagram` (wrap existing logic)
   * `normalizeObjDeepWithCtx` / `normalizeObj` (wrap existing logic)
   * `normalizeCodeTerm` (new, see below)
   * `defEqTermDiagram` and `defEqObj` (new; just “normalize then structural compare”)
2. Update call sites:

   * `ObjNormalize` becomes the implementation (or is folded into the new module).
   * `UnifyObj` should call `DefEq.normalizeTermDiagram` and `DefEq.normalizeObj…` instead of importing `ObjNormalize` directly (or re-exporting from there).
3. Keep the implementation minimal at first:

   * Build a thin façade over existing normalization functions; the goal is to have a single authority module for defeq.

### Tests

* No new behavior yet; compile+tests should pass unchanged.

---

## 2) Make “per-mode definitional fragments” explicit in `TypeTheory`

### Current state (what exists)

* `doctrineTypeTheory` already computes:

  * `ttTmFuns :: Map ModeName (Map TmFunName TmFunSig)`
  * `ttTmRules :: Map ModeName [TmRule]`
  * `ttTmTRS :: Map ModeName TRS`
* Termination and confluence checks already happen in `Doctrine.doctrineTypeTheory`.

### Agent instructions

1. Introduce a new record:

   ```hs
   data DefFragment = DefFragment
     { dfMode  :: ModeName
     , dfFuns  :: Map TmFunName TmFunSig
     , dfRules :: [TmRule]
     , dfTRS   :: TRS
     }
   ```
2. In `TypeTheory`, replace (or supplement) the three parallel maps with:

   ```hs
   ttDefFragments :: Map ModeName DefFragment
   ```

   Keep compatibility helpers:

   * `termTRSForMode` becomes `dfTRS . lookup`.
3. Refactor `Doctrine.doctrineTypeTheory`:

   * Build `DefFragment` per mode in one place.
   * Perform termination + confluence checks per fragment.
4. Keep all rule filtering logic identical initially; Phase 5 is primarily architecture.

### Tests

* Add a unit test that asserts `ttDefFragments` contains entries for all modes that have any derived definitional content (or for all modes in doctrine, depending on design choice).

---

## 3) Implement `normalizeCodeTerm` as a stable API

### Key design constraint in current codebase

`CodeTerm` is not a `TermDiagram`. It contains:

* `CTCon ObjRef [CodeArg]`
* `CTMeta TmVar`
* `CTMod ModExpr CodeTerm`

And `CodeArg` is either:

* `CAObj Obj` (which contains its own code term),
* `CATm TermDiagram` (term in its own mode)

Therefore, “normalize code term in mode K’s fragment” must at least:

* normalize modality spines (mode equations),
* normalize CAObj subobjects recursively,
* normalize CATm term diagrams using the correct per-mode fragment,
* then produce a canonical `CodeTerm` tree.

### Agent instructions

1. Add a new function (in the new DefEq module or in ObjNormalize, but exported via DefEq):

   ```hs
   normalizeCodeTermDeepWithCtx
     :: TypeTheory
     -> [Obj]        -- tmCtx
     -> ModeName     -- owner mode of the *object whose code this is*
     -> CodeTerm
     -> Either Text CodeTerm
   ```

   Notes:

   * You need the *owner* mode to type-check/normalize `CTMod` application boundaries (`meTgt` must match owner at that node).
2. Implement as:

   * For `CTMeta`: return as-is.
   * For `CTCon ref args`:

     * Normalize each `args[i]`:

       * `CAObj t`: normalize `t` via `normalizeObjDeepWithCtx` and rewrap.
       * `CATm d`: normalize via `normalizeTermDiagram` using the expected sort (see below).
     * Return rebuilt `CTCon`.
   * For `CTMod me inner`:

     * Normalize `me` using `normalizeModExpr`.
     * Normalize `inner` recursively using inner-owner `meSrc me`.
     * Rebuild, and then **fuse/normalize** modality spines the same way `normalizeObjExpr` currently does (either:

       * call `normalizeObjExpr` on a temporary `Obj owner (CTMod ...)` and then extract code, or
       * reimplement the fusion logic for code terms).
3. Sorting of `CATm`:

   * If you have access to the type signature of `ref` in `CTCon ref args`, you can compute the expected term argument sort from `PS_Tm sortTy`.
   * If you don’t (or for robustness), normalize term diagrams using:

     * `normalizeTermDiagram tt tmCtx expectedSort diag`
   * This requires that you thread expected sorts when you have them; so prefer signature-driven recursion at code-level too (similar to object-level normalization).
4. Replace the existing “code term normalization logic” in `normalizeObjDeepWithCtx` with a call to this new function so there is exactly one implementation.

### Tests

Add tests that directly exercise `normalizeCodeTermDeepWithCtx` via object normalization:

* Construct a doctrine with a dependent type constructor whose term argument reduces (e.g. the existing dependent Vec examples).
* Assert:

  * `normalizeObjDeepWithCtx` makes two objects equal whose only difference is a reducible term argument inside the code term.
  * This should be tested at the object level (ports/types), not just term level.

---

## 4) Centralize definitional equality checks (“normalize then compare”)

### Agent instructions

1. Add:

   ```hs
   defEqObj :: TypeTheory -> [Obj] -> Obj -> Obj -> Either Text Bool
   defEqObj tt tmCtx a b = do
     aN <- normalizeObjDeepWithCtx tt tmCtx a
     bN <- normalizeObjDeepWithCtx tt tmCtx b
     pure (aN == bN)
   ```
2. Add:

   ```hs
   defEqTermDiagram :: TypeTheory -> [Obj] -> Obj -> TermDiagram -> TermDiagram -> Either Text Bool
   ```

   where `Obj` is the expected sort; normalize both via `normalizeTermDiagram` and compare.
3. Replace ad-hoc equality checks in:

   * `Strat/Poly/DiagramIso.hs` (where sorts are compared after substitutions),
   * any matching code that does raw equality on objects/terms that should be definitional.

This step is what makes “codes the basis of type equality” mechanically true.

### Tests

* Add a DiagramIso regression where isomorphism depends on definitional equality of port types (e.g., types differ only in reducible term index).

---

## 5) Update unification to rely on the definitional engine consistently

### Agent instructions

1. Audit all normalization in `src/Strat/Poly/UnifyObj.hs`:

   * Ensure term normalization uses the centralized API.
   * Ensure object normalization used before comparisons is consistent (particularly for modality normalization and term-index normalization).
2. Eliminate duplicate normalization paths:

   * If `unifyTm` does its own “normalize-to-term-expr and back” steps, ensure it calls the shared `normalizeTermDiagram` and only does the extra conversion steps where strictly required.
3. Add one invariant:

   * Whenever you compare `Obj` or `TermDiagram` for equality in unification, compare **normalized** forms unless the comparison is strictly syntactic-by-design (e.g., occurs checks).

### Tests

* Add a unification test where the success depends on term-index reduction inside object codes (if not already covered by Vec-dependent tests).

---

## 6) Termination + confluence: tighten surfacing and diagnostics

Even though these checks exist, Phase 5 is a good time to make failures actionable, because the engine becomes “the” source of definitional equality.

### Agent instructions

1. When SCT termination check fails, include:

   * mode name,
   * the root symbols involved (TmFunName),
   * the offending rules pretty-printed.
2. When confluence check fails, include:

   * the critical pair and overlap position details if available.

### Tests

* Add a negative test doctrine that intentionally creates a non-terminating definitional fragment in some mode; assert the error message includes the mode and root symbol.

---

## 7) Documentation updates

### Agent instructions

1. Update `SPEC.md`:

   * Add/extend a section describing:

     * “definitional fragment per mode”,
     * how `normalizeTermDiagram` and `normalizeCodeTerm` interact,
     * how definitional equality is used for type equality (objects).
2. Update `PLAN.md` Phase 5:

   * Reflect the concrete API names and the new `DefFragment` structure.
   * Resolve the “scope by classifier vs owner” mismatch explicitly (see Phase 4 issue #4).

---

# Implementation checklist (agent-facing)

## Phase 4 fixes checklist

* [ ] Surface: `RPTVar` resolves nullary constructors when available.
* [ ] Surface: `RPTCon` elaborates args in signature-directed owner modes (`PS_Ty m` ⇒ recurse with `m`).
* [ ] UnifyObj: fix `expandModSpine` inner owner to `meSrc`.
* [ ] Decide and document scope rule (owner-slice vs classifier-slice).
* [ ] Add regression tests for surface constructor resolution (including classified case).

## Phase 5 checklist

* [ ] Add `DefEq` module (or equivalent) as the single entrypoint.
* [ ] Replace parallel `ttTmFuns/ttTmRules/ttTmTRS` with `ttDefFragments`.
* [ ] Implement and export `normalizeCodeTermDeepWithCtx`.
* [ ] Refactor object normalization to call the new code-normalizer.
* [ ] Add `defEqObj` / `defEqTermDiagram` (“normalize then compare”).
* [ ] Route unification and iso checks through the defeq API.
* [ ] Improve termination/confluence diagnostics + negative tests.
* [ ] Update SPEC + PLAN text to match implementation reality.
