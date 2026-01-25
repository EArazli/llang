## Ground rules for the coding agent

* Work phase-by-phase exactly as in the migration plan; do **not** refactor old kernel modules while bringing up the new core.
* Keep `stack test` green after every phase commit.
* New code goes under a new namespace (proposed below) so that old kernel remains intact until Phase 3 switch.
* Treat `SPEC.md` as authoritative. After each phase, update it to reflect the actual state of the repo (even if the phase is “new modules exist but not yet wired in”).

I’m going to give you a concrete, no-choice implementation plan for **Phases 0–3** (enough to start executing the migration immediately and safely), including exact module shapes, function signatures, and test additions.

---

# Phase 0 — Freeze current behavior as regression baseline

### Goal

Before adding any new kernel, ensure we can detect behavior drift in:

* normalization results,
* joinability behavior,
* run outputs for canonical examples.

### Implementation tasks

1. **Add golden/expect tests for existing examples** (if not already exhaustive):

   * Create `test/Test/CLI/Golden.hs` that runs `llang` on a handful of files in `examples/` and compares stdout to checked-in golden strings.
   * Include at least:

     * `examples/monoid.llang`
     * `examples/ccc.llang`
     * `examples/stlc.llang` (if it exists/works)
   * Use the same mechanism already used in `Test.CLI` if it exists; just add stricter coverage.

2. **Add a kernel-level regression suite**:

   * New test module: `test/Test/Kernel/Regression.hs`
   * Pick 10–20 representative terms in a couple of fixtures (monoid + ccc/core category).
   * Assert:

     * `normalize fuel rs t` equals expected term
     * `joinableWithin` expected true/false in a couple of cases

### Acceptance criteria

* `stack test` passes.
* If you intentionally change a rewrite strategy or equation orientation, these tests fail.

### `SPEC.md` update

* Add a short paragraph near the top: “Regression tests exist for example outputs and kernel normalization/joinability; these are treated as semantic reference during migration.”

---

# Phase 1 — Introduce new core data model in parallel (polygraph kernel)

## 1.1 New module namespace and file layout

Create a new directory:

* `src/Strat/Poly/`

and these modules (exact filenames):

* `src/Strat/Poly/ModeTheory.hs`
* `src/Strat/Poly/TypeExpr.hs`
* `src/Strat/Poly/Diagram.hs`
* `src/Strat/Poly/Cell2.hs`
* `src/Strat/Poly/Doctrine.hs`

No integration with frontend yet. Just data types + validators.

---

## 1.2 ModeTheory (minimal but future-proof)

### File: `Strat.Poly.ModeTheory`

Implement these types:

```haskell
{-# LANGUAGE OverloadedStrings #-}

module Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModName(..)
  , ModExpr(..)
  , ModDecl(..)
  , ModeTheory(..)
  , emptyModeTheory
  , addMode
  , addModDecl
  , composeMod
  , checkWellFormed
  ) where
```

Data:

```haskell
newtype ModeName = ModeName Text deriving (Eq, Ord, Show)
newtype ModName  = ModName  Text deriving (Eq, Ord, Show)

data ModDecl = ModDecl
  { mdName :: ModName
  , mdSrc  :: ModeName
  , mdTgt  :: ModeName
  } deriving (Eq, Show)

-- Keep it extremely simple for now: a modality expression is a path of generators.
data ModExpr = ModExpr
  { meSrc  :: ModeName
  , meTgt  :: ModeName
  , mePath :: [ModName]      -- identity = []
  } deriving (Eq, Ord, Show)

data ModeTheory = ModeTheory
  { mtModes :: Set ModeName
  , mtDecls :: Map ModName ModDecl
  -- For now store 2-cell equations but do not use them for normalization yet.
  , mtEqns  :: [(ModExpr, ModExpr)]
  } deriving (Eq, Show)
```

Operations:

* `composeMod :: ModeTheory -> ModExpr -> ModExpr -> Either Text ModExpr`

  * Requires `meTgt f == meSrc g`, returns concatenation.
* `checkWellFormed :: ModeTheory -> Either Text ()`

  * Every ModDecl’s src/tgt in mtModes.

**No modality equality “up to equations” in Phase 1.** Keep API surface ready, but do not implement normalization yet.

---

## 1.3 TypeExpr (minimal)

### File: `Strat.Poly.TypeExpr`

This migration needs to embed old `Sort` for compatibility, so implement:

```haskell
module Strat.Poly.TypeExpr
  ( TypeExpr(..)
  , Context
  , asSort
  ) where

import Strat.Kernel.Syntax (Sort)

data TypeExpr
  = TySort Sort                -- compatibility embedding
  | TyCon  Text [TypeExpr]     -- future-proof
  deriving (Eq, Ord, Show)

type Context = [TypeExpr]

asSort :: TypeExpr -> Maybe Sort
asSort (TySort s) = Just s
asSort _ = Nothing
```

---

## 1.4 Diagram (strict planar monoidal term)

### File: `Strat.Poly.Diagram`

This Phase 1 representation must support:

* ordered boundary contexts,
* identity / composition / tensor,
* generator nodes (including cartesian structural ones as “labels”).

Implement:

```haskell
module Strat.Poly.Diagram
  ( GenLabel(..)
  , Diagram(..)
  , idD
  , genD
  , compD
  , tensorD
  , diagramDom
  , diagramCod
  ) where
```

Core types:

```haskell
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr (Context, TypeExpr)

data GenLabel
  = GLUser OpName            -- user generator (old ops)
  | GLDup  TypeExpr
  | GLDrop TypeExpr
  | GLSwap TypeExpr TypeExpr
  deriving (Eq, Ord, Show)

data Diagram
  = DId     ModeName Context
  | DGen    ModeName Context Context GenLabel
  | DComp   Diagram Diagram
  | DTensor Diagram Diagram
  deriving (Eq, Show)

diagramDom :: Diagram -> Context
diagramCod :: Diagram -> Context
```

Smart constructors:

* `idD mode Γ = DId mode Γ`
* `genD mode dom cod label = DGen mode dom cod label`
* `compD g f` checks:

  * `diagramCod f == diagramDom g`
  * same mode on both
* `tensorD f g` checks same mode and defines dom/cod as concatenations

**Make the “mode mismatch” and “boundary mismatch” errors explicit `Text`.**

---

## 1.5 Cell2 and Doctrine2

### File: `Strat.Poly.Cell2`

```haskell
module Strat.Poly.Cell2
  ( Cell2(..)
  ) where

import Strat.Kernel.Types (RuleClass, Orientation)
import Strat.Poly.Diagram (Diagram)

data Cell2 = Cell2
  { c2Name   :: Text
  , c2Class  :: RuleClass
  , c2Orient :: Orientation
  , c2LHS    :: Diagram
  , c2RHS    :: Diagram
  } deriving (Eq, Show)
```

### File: `Strat.Poly.Doctrine`

This is the compiled doctrine object.

```haskell
module Strat.Poly.Doctrine
  ( StructuralLib(..)
  , Doctrine2(..)
  , cartMode
  ) where

import Strat.Kernel.Presentation (Presentation)
import Strat.Kernel.Signature (Signature)
import Strat.Poly.Cell2 (Cell2)
import Strat.Poly.ModeTheory (ModeTheory, ModeName(..))

data StructuralLib
  = StructPlanar
  | StructSymmetric
  | StructCartesian
  deriving (Eq, Ord, Show)

cartMode :: ModeName
cartMode = ModeName "Cart"

data Doctrine2 = Doctrine2
  { d2Name         :: Text
  , d2ModeTheory   :: ModeTheory
  , d2Sig          :: Signature
  , d2StructByMode :: Map ModeName StructuralLib
  , d2Cells2       :: [Cell2]
  } deriving (Eq, Show)
```

No rewriting yet.

---

## Phase 1 tests

Add `test/Test/Poly/Basic.hs`:

* Construct a couple of tiny diagrams and assert dom/cod checks.
* Ensure compD rejects mismatch.

Add to `test/Spec.hs`:

* import and include `Test.Poly.Basic.tests`.

### `SPEC.md` update for Phase 1

Add a new section near the kernel section:

* “Polygraph kernel (experimental, not yet wired into runs)” describing:

  * new data types: ModeTheory, TypeExpr, Diagram, Cell2, Doctrine2
  * note that rewriting is still old kernel.

---

# Phase 2 — Compile old presentations and terms into Doctrine2 + Diagrams (cartesian embedding)

This is the **compatibility bridge**. Implement it completely before touching the run pipeline.

## 2.1 New modules

Add:

* `src/Strat/Poly/Compat.hs` (compilers)
* `src/Strat/Poly/Eval.hs` (diagram → term interpreter)
* `src/Strat/Poly/CartLib.hs` (structural wiring constructors)

---

## 2.2 Cartesian structural library representation

You cannot finitely enumerate `dup_A/drop_A/swap_{A,B}` for all type expressions, so implement them as **schema via `GenLabel`**:

* `GLDup A`, `GLDrop A`, `GLSwap A B`

The doctrine records: `StructCartesian` for mode Cart, which is the gate that allows these.

No infinite enumeration of cells in doctrine. (You can add schema-level axioms later; for now, keep structural equations out of rewriting, since you’re deferring coherence/perf anyway.)

---

## 2.3 Compile Presentation → Doctrine2

### File: `Strat.Poly.Compat`

Export:

```haskell
compilePresentationToDoctrine2 :: Presentation -> Either Text Doctrine2
```

Implementation (fixed choices):

* Mode theory: one mode `Cart`, no modalities, no equations.
* `d2Sig = presSig pres`
* `d2StructByMode = { Cart ↦ StructCartesian }`
* For each old equation `eq`:

  * compile both sides to diagrams under telescope `eqTele eq`
  * store as a `Cell2` with same name/class/orientation

Diagram compilation depends on `compileTermToDiagram` below.

---

## 2.4 Term → Diagram compilation (explicit wiring)

### Signature

```haskell
compileTermToDiagram
  :: Signature
  -> ModeName
  -> [Binder]    -- telescope / context
  -> Term
  -> Either Text Diagram
```

**Hard requirement**: compilation must be deterministic and must not require global state. Use the exact strategy below.

### Helper constructors (CartLib)

Create in `Strat.Poly.CartLib`:

* `dropCtx :: ModeName -> Context -> Diagram`

  * from Γ to []
  * implement as tensor of `GLDrop` per wire:

    * `dropCtx mode [] = idD mode []`
    * `dropCtx mode (A:rest) = tensorD (genDrop A) (dropCtx mode rest)`
* `swapAdjacent :: ModeName -> Context -> Int -> Either Text Diagram`

  * swaps wires at positions `i` and `i+1` in a context
  * implements `id prefix ⊗ swap ⊗ id suffix`
* `bubbleLeftTo0 :: ModeName -> Context -> Int -> Either Text (Diagram, Context)`

  * repeatedly apply `swapAdjacent` to move wire at index `i` to index 0
  * returns (diagram, resulting context)
* `projWire :: ModeName -> Context -> Int -> Either Text Diagram`

  * uses `bubbleLeftTo0` then drops suffix:

    * bubble wire i to front
    * apply `(id [Ai] ⊗ dropCtx suffix)`
* `dupCtx :: ModeName -> Context -> Either Text Diagram`

  * duplicates entire context: Γ → Γ++Γ
  * implement by:

    1. tensor of per-wire `GLDup` (produces A,A,B,B,...)
    2. “shuffle” second copy into grouped form via repeated adjacent swaps:

       * for each wire, bubble its second duplicate rightwards across the remaining first-block wires
  * **Do not use a generic permutation engine yet.** Implement the specific shuffle; it’s much harder to get wrong.

Also add:

* `pairArgs :: ModeName -> Context -> [Diagram] -> Either Text Diagram`

  * All diagrams must have the same domain Γ.
  * Produces Γ → concat(cods)
  * Deterministic recursion:

    * `pairArgs Γ [] = dropCtx Γ`
    * `pairArgs Γ [d] = d`
    * `pairArgs Γ (d:ds) = (tensorD d (pairArgs Γ ds)) ∘ dupCtx Γ`

(That recursion is intentionally simple and deterministic, even if not optimal.)

### Actual term compilation rules

Given `tele :: [Binder]` with context types:
`Γ = map (TySort . bSort) tele`

1. Variable term `TVar v`:

   * find index `i` of binder `bVar == v` in `tele`
   * return `projWire mode Γ i`

2. Operation term `TOp op args`:

   * recursively compile each arg: `di : Γ -> [Ai]`
   * `argsDia = pairArgs mode Γ [d0..dn-1]` gives Γ → [A0..An-1]
   * `gen = DGen mode [A0..An-1] [B] (GLUser op)` where B is `TySort (termSort tm)`
   * return `compD gen argsDia`

3. Constants are handled automatically: if op has 0 args, `pairArgs Γ [] = dropCtx Γ` and composition works.

### Required invariants

* `diagramDom` of result is always `Γ`
* `diagramCod` of result is `[TySort (termSort term)]`
* Uses only `GLUser/GLDup/GLDrop/GLSwap` and `DId/DComp/DTensor`

---

## 2.5 Diagram → Term interpreter (for regression and Phase 3)

### File: `Strat.Poly.Eval`

Export:

```haskell
evalDiagram
  :: Signature
  -> [Binder]     -- input telescope providing Var identities
  -> Diagram
  -> Either Text [Term]

diagramToTerm1
  :: Signature
  -> [Binder]
  -> Diagram
  -> Either Text Term
```

Rules:

* Input environment terms are variables from `tele`:

  * `env = [ mkVar (bSort bi) (bVar bi) | bi <- tele ]`
* `DId` returns env unchanged.
* `DTensor f g`: split env by `length (diagramDom f)`; evaluate separately; concatenate outputs.
* `DComp g f`: evaluate `f` then feed into `g`.
* `DGen`:

  * `GLUser op`: apply `mkOp sig op inputs` (must return 1 term; if not, error)
  * `GLDup`: input [t] → [t,t]
  * `GLDrop`: input [t] → []
  * `GLSwap`: input [x,y] → [y,x]

`diagramToTerm1` requires codomain length = 1.

This evaluator is purely syntactic readback; it’s the key regression tool.

---

## Phase 2 test suite extensions

Add `test/Test/Poly/Compat.hs`:

### Tests to include (explicit)

1. **Roundtrip: term → diagram → term**

   * Use `Test.Kernel.Fixtures.sigBasic` plus a telescope:

     * tele0: `(x:Obj)`
     * tele2: `(x:Obj)(y:Obj)`
     * teleCat-ish: use `Hom(x,x)` style from `sigBasic` (`opId` exists and is dependent)
   * Terms to test:

     * variable: `?x`
     * constant: `a` (0-ary op)
     * duplicate: `m(?x, ?x)`
     * reorder: `m(?y, ?x)` under tele `(x,y)`
     * dependent: `id(?x)` (returns `Hom(x,x)`)
   * Assert exact syntactic equality `t == diagramToTerm1 sig tele (compileTermToDiagram ...)`

2. **Presentation → Doctrine2 preserves equations**

   * Build a tiny Presentation with 2 equations, compile to Doctrine2.
   * Assert:

     * number of cells2 == number of equations
     * each cell name matches equation name
     * each cell’s LHS/RHS read back to original equation terms (same telescope).

Add to `test/Spec.hs`.

### `SPEC.md` update for Phase 2

Update spec to include:

* A new subsection: “Compatibility embedding into Cart polygraph core”
* Describe:

  * Cart mode
  * structural schema (dup/drop/swap as parametric labels)
  * term→diagram compilation (high-level description, not all implementation details)
  * diagram→term readback exists for regression

---

# Phase 3 — Switch normalization/equality checking to go through diagrams (cartesian fragment only)

This phase is *the* integration switch, but you can implement it safely because you will still reuse the existing term rewrite engine internally.

## 3.1 New module: `Strat.Poly.Normalize`

Implement:

```haskell
normalizeDiagramStatus
  :: Int
  -> RewriteSystem
  -> Signature
  -> [Binder]
  -> Diagram
  -> Either Text (NormalizationStatus Diagram)

joinableWithinDiagram
  :: Int
  -> RewriteSystem
  -> Signature
  -> [Binder]
  -> Diagram
  -> Diagram
  -> Either Text Bool
```

Concrete, fixed behavior:

* Convert diagram → term using `diagramToTerm1`.
* Run existing kernel functions:

  * `normalizeStatus fuel rs term`
  * `joinableWithin fuel rs term1 term2`
* Convert resulting term back to diagram using `compileTermToDiagram sig cartMode tele`.
* Return status (Finished/OutOfFuel) but with Diagram.

This is not yet DPO rewriting, but it *does* route execution through the new core representation and keeps semantics identical.

## 3.2 Wire into frontend run pipeline

Modify:

* `Strat.Frontend.Run`

In both:

* `runComb` (after elaboration yields a core Term)
* `runSurface2`

Replace the direct call to `normalizeStatus` on the Term with:

1. `diag0 <- compileTermToDiagram (presSig pres) cartMode tele term`

   * Here tele is the context telescope for the term:

     * For `runComb`, you already have `ctx` as `[Binder]`
     * For `runSurface2`, you already have `ctxTele`
2. `statusDiag <- normalizeDiagramStatus fuel rs (presSig pres) ctxTele diag0`
3. `termNorm <- diagramToTerm1 (presSig pres) ctxTele (value statusDiag)`

   * (where `value` extracts the Diagram)
4. Continue with the rest of pipeline using `termNorm` exactly as today.

**Important**: do not change printing or model evaluation yet; keep them term-based. This prevents any output drift.

## 3.3 Morphism checking (minimal safe change)

Do **not** rewrite morphism checker yet. Keep `Strat.Kernel.Morphism` unchanged in this phase. The run pipeline is the integration surface; morphisms can follow later once diagram rewriting becomes real.

## Phase 3 tests

1. Extend `test/Test/Kernel/Rewrite.hs` with a “poly normalization agrees” version:

   * build RS from Presentation
   * for each sample term `t`:

     * `normalizeStatus fuel rs t` equals `diagramToTerm1 ... (normalizeDiagramStatus ... (compileTermToDiagram ... t))`

2. Ensure CLI tests still pass unchanged (they should, because you still print terms).

### `SPEC.md` update for Phase 3

You must update the “Rewriting” and “Runs” sections to say:

* Core execution path now uses:

  * term elaboration → diagram compilation → normalization (via diagram wrapper) → term readback → backend/model
* Clarify that diagram rewriting is not yet DPO; it’s a compatibility normalization wrapper for now.
* Explicitly list which phases are implemented and which are pending (boxes, real subdiagram rewriting, multi-output user generators).

---

# What not to do yet (to avoid forks)

* Do not implement full hypergraph/DPO rewriting in Phase 3.
* Do not change Surface2 internals; keep it elaborating to old core Term until Phase 5.
* Do not add user-facing syntax for multi-output ops or modes yet (Phase 4).

---

# Summary checklist (agent-facing)

### Phase 0 (tests)

* [ ] Add CLI golden tests for key examples
* [ ] Add kernel regression tests for normalize/joinableWithin
* [ ] Update `SPEC.md` regression note

### Phase 1 (new core data model)

* [ ] Implement `Strat.Poly.{ModeTheory,TypeExpr,Diagram,Cell2,Doctrine}`
* [ ] Add `Test.Poly.Basic`
* [ ] Update `SPEC.md` with “Polygraph kernel (experimental)”

### Phase 2 (compat compiler + eval)

* [ ] Implement `compilePresentationToDoctrine2`
* [ ] Implement `compileTermToDiagram` with deterministic wiring algorithm
* [ ] Implement `evalDiagram` + `diagramToTerm1`
* [ ] Add `Test.Poly.Compat` roundtrip tests (including dependent `id`)
* [ ] Update `SPEC.md` with compatibility embedding description

### Phase 3 (integration)

* [ ] Implement `Strat.Poly.Normalize` wrappers
* [ ] Modify `Strat.Frontend.Run` to normalize through diagrams
* [ ] Add “poly normalization agrees” tests
* [ ] Update `SPEC.md` rewriting + run pipeline sections

This is the minimal, unambiguous path that brings the new diagram core into the execution path early (Phase 3) without breaking semantics, and sets you up to replace the internal normalization engine with true diagram rewriting later.
