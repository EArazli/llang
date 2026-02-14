# llang rewrite plan: schemas + functorial modalities + dependent types (no index parallel universe)

This document is a standalone, implementation-oriented plan for refactoring the attached llang bundle into the “best end-state” design:
- **No separate index theory.** Dependent indices become ordinary computation in ordinary modes.
- **No hard-coded structural discipline or adjunction keywords.** All cross-mode structure is declared/checked via doctrines + morphisms (“schemas”).
- **Functorial modalities (morphism-level action).** Modalities can act on diagrams via user-declared “actions”, composable and coherent with `mod_eq`.
- **Schema obligations.** Schemas can attach reusable proof obligations (triangle identities, naturality, etc.) checked automatically when instantiating via `implements`.

Backward compatibility is explicitly not a goal; update or delete tests/examples freely.

---

## 0. Executive summary of the target end-state

### 0.1 Core concepts

1. **Doctrines remain the only “theory object”.**  
   A “schema” is just a doctrine used as an interface, plus optional `obligation` declarations (new metadata).

2. **Instances are morphisms.**  
   `implements IFace for Target using m` means “m : IFace → Target is an instance”. Any schema checks run here.

3. **Modalities are still declared in `ModeTheory`** as now (`modality`, `mod_eq`), but:
   - remove `structure … = cartesian|…`
   - remove `adjunction F dashv U`
   - add **modality actions**: `action <ModName> { … }` gives a functorial action on diagrams.

4. **Dependent type indices are terms, not a separate language.**
   - Remove `index_mode`, `index_fun`, `index_rule`.
   - Replace `PS_Ix` / `TAIndex IxTerm` with `PS_Tm sort` / `TATm TermDiagram`.
   - TermDiagram normalization uses the existing diagram rewrite engine (computational rules in that term mode).

---

## 1. General plan (phased, with “stop points”)

Each phase should end with `stack test` green and at least one `stack run` example green.

### Phase A — Delete the parallel index system; replace with term-diagram indices
- Remove `Strat.Poly.IndexTheory` and all `index_*` syntax.
- Introduce term parameters and term arguments (diagram-shaped) in types:
  - new `PS_Tm` and `TA_Tm`
  - new `TmVar` (metavariable) & `TermDiagram` representation
- Type definitional equality normalizes term arguments by calling the normalizer on these term diagrams.

**Stop point:** dependent examples compile and typecheck; old index features removed.

### Phase B — Remove hard-coded structure discipline
- Remove `VarDiscipline` from `ModeTheory` and `structure` declarations.
- Remove `checkStructuralByDiscipline` and all `dup/drop` name lookup.
- Surface elaborator must resolve structural operations via **schema instances** (`implements StructCartesian …`), not by name.

**Stop point:** surface tests rewritten; examples using `structure` rewritten.

### Phase C — Functorial modalities (actions) + `map[μ](…)`
- Add `action <ModName>` declarations to doctrines.
- Add `map[<ModExpr>](<DiagExpr>)` diagram syntax.
- Implement functorial mapping of diagrams using actions; composition uses modality expressions.

**Stop point:** tests for `map` and action coherence, plus staging/lnl examples updated.

### Phase D — Schema obligations (triangle identities, naturality, etc.)
- Add `obligation …` declarations to doctrines (schema metadata).
- When elaborating `implements`, run obligations from interface doctrine against the morphism instance.
- Provide stdlib schemas (Adjunction, Monad, Cartesian, Fibration) as doctrines + obligations.

**Stop point:** add at least one example where an incorrect instance fails with a clear error.

---

## 2. Detailed implementation instructions (by subsystem / file)

### 2.1 Remove IndexTheory completely (Phase A)

#### 2.1.1 Delete module and imports
- Delete: `src/Strat/Poly/IndexTheory.hs`
- Remove all imports of `Strat.Poly.IndexTheory` from:
  - `Strat/Poly/TypeTheory.hs`
  - `Strat/Poly/Doctrine.hs`
  - `Strat/Poly/UnifyTy.hs`
  - `Strat/Poly/Morphism.hs`
  - `Strat/Poly/Pushout.hs`
  - `Strat/Poly/DSL/Elab.hs`
  - anywhere else `grep -R "IndexTheory" -n src`

#### 2.1.2 Replace type-level “index args” with “term args”
Update these core datatypes:

**File: `src/Strat/Poly/TypeExpr.hs`**
- Remove:
  - `IxFunName`, `IxVar`, `IxTerm`, `TAIndex`
  - `freeIxVarsType`, `freeIxVarsIx`, `boundIxIndices*`, `mapIxTerm`, etc.

- Add:
  - `TmVarName` (newtype Text)
  - `TmVar` record:
    ```hs
    data TmVar = TmVar
      { tmvName  :: Text
      , tmvSort  :: TypeExpr     -- result sort
      , tmvScope :: Int          -- number of bound term vars it can mention (explicit-args trick)
      } deriving (...)
    ```
  - `TermDiagram` (recommended representation):
    ```hs
    -- Diagram in the term mode, with:
    --   * no boxes/feedback/splice (restricted fragment, see RESTRICTIONS.md)
    --   * boundary inputs correspond to the bound term vars in scope (per mode)
    --   * one boundary output (the term result)
    newtype TermDiagram = TermDiagram { unTerm :: Diagram }
    ```
    If you need to avoid recursive type/module knots, you can place `TermDiagram` in a new module `Strat.Poly.TermDiagram` that imports `Diagram` and `TypeExpr`, and re-export as needed.
  - Extend `TypeArg`:
    ```hs
    data TypeArg
      = TAType TypeExpr
      | TATm TermDiagram
    ```
  - Update `mapTypeExpr` and free-variable computation:
    - free type vars includes those in embedded term diagrams’ port types
    - free term vars (metas) includes those appearing in the embedded term diagrams (see below).

**IMPORTANT:** You need a way to represent **term metavariables** *inside* term diagrams without declaring fake generators.
Recommended approach: extend `EdgePayload` with a new constructor.

**File: `src/Strat/Poly/Graph.hs`**
- Extend `EdgePayload`:
  ```hs
  data EdgePayload
    = PGen GenName AttrMap [BinderArg]
    | PBox Text Diagram
    | PFeedback
    | PSplice BinderMetaVar
    | PTmMeta TmVar            -- NEW: term metavariable node
```

* Validation rules for `PTmMeta`:

  * It behaves like a node with some inputs and exactly 1 output.
  * It must have **no binder args** and **no attrs** (by construction).
  * Its output port type must match `tmvSort` (up to type definitional equality).
  * Its input ports are the explicit arguments: must be exactly the subset of bound-term variables allowed by `tmvScope` (see scoping below).

This is the key to eliminating `IXBound` and `ixvScope` checks:

* a term metavariable *occurrence* is a node wired to its allowed bound-term variables.
* no later “escape check” is needed because illegal wires cannot be constructed.

#### 2.1.3 Repurpose the existing “index context” (`dIxCtx`) into “bound term variable telescope”

Currently `Diagram` has:

* `dIxCtx :: [TypeExpr]` and `BinderSig.bsIxCtx :: [TypeExpr]`
  These already track a telescope of bound index sorts per diagram/binder slot.

**Keep the mechanism, but rename and reinterpret:**

* Rename (recommended; it’s a big mechanical change but clarifies everything):

  * `dIxCtx` → `dTmCtx`
  * `bsIxCtx` → `bsTmCtx`
  * Update all callers accordingly (`Diagram.hs`, `Graph.hs`, `Doctrine.hs`, `DSL/Elab.hs`, `Morphism.hs`, etc.)

**Semantics after the change:**

* `dTmCtx` is a telescope of **bound term variables** (indices) available in port types inside that diagram.
* For a term argument in a type, only the bound vars *of the term mode* are visible; the term diagram’s boundary inputs are those.

Define helper:

```hs
tmCtxForMode :: [TypeExpr] -> ModeName -> [TypeExpr]
tmCtxForMode tele m = [ ty | ty <- tele, typeMode ty == m ]
```

#### 2.1.4 Update signatures: `ParamSig` and `TypeSig`

**File: `src/Strat/Poly/Doctrine.hs`**

* Replace:

  ```hs
  data ParamSig = PS_Ty ModeName | PS_Ix TypeExpr
  ```

  with:

  ```hs
  data ParamSig = PS_Ty ModeName | PS_Tm TypeExpr
  ```
* Update `TypeSig` and all checks accordingly.

**File: `src/Strat/Poly/TypeTheory.hs`**

* Stop importing `IndexTheory`.
* Define `TypeTheory` locally (currently re-exported from IndexTheory):

  * include type constructor arities (`ttTypeParams`)
  * include `ttModes`
  * include normalization fuel for term arguments, e.g.:

    ```hs
    data TypeTheory = TypeTheory
      { ttModes      :: ModeTheory
      , ttTypeParams :: Map TypeRef [TypeParamSig]
      , ttCells2     :: [Cell2]        -- NEW: for term normalization inside types
      , ttTmFuel     :: Int
      , ttTmPolicy   :: RewritePolicy  -- e.g. UseOnlyComputationalLR
      }
    ```
* Replace `TPS_Ix` with `TPS_Tm`.

**File: `doctrineTypeTheory` in `src/Strat/Poly/Doctrine.hs`**

* Populate `ttCells2 = dCells2 doc`
* Populate `ttTmFuel` and `ttTmPolicy` with defaults (or allow doctrine-level override later).

#### 2.1.5 Type normalization: replace `normalizeTypeDeep` + `normalizeIx` with term-diagram normalization

**Create/modify in `TypeTheory.hs` (or a new module):**

* `normalizeTypeDeep :: TypeTheory -> TypeExpr -> Either Text TypeExpr`

  * As before, normalize nested modality composition (`normalizeTypeExpr`) on `TMod`.
  * For `TCon ref args`, consult `ttTypeParams`:

    * `TPS_Ty`: recurse on `TAType`
    * `TPS_Tm sort`: normalize the `TATm term` by:

      1. normalize the sort type
      2. validate the term diagram is in `typeMode sort`
      3. normalize the term diagram using `Normalize.normalize` with rules restricted to that term mode and policy `ttTmPolicy`
      4. ensure the output port type matches the sort after normalization

You need:

* `normalizeTermDiagram :: TypeTheory -> TypeExpr -> TermDiagram -> Either Text TermDiagram`

This is where the old index world is fully subsumed.

#### 2.1.6 Unification: replace `unifyIx` with `unifyTm` on term diagrams

**File: `src/Strat/Poly/UnifyTy.hs`**

* Replace `sIx :: Map IxVar IxTerm` with:

  ```hs
  sTm :: Map TmVar TermDiagram
  ```
* Replace `unifyIx` with:

  ```hs
  unifyTm
    :: TypeTheory
    -> [TypeExpr]            -- bound term telescope (dTmCtx)
    -> Set TmVar             -- flexible term metavars
    -> Subst
    -> TypeExpr              -- expected sort
    -> TermDiagram
    -> TermDiagram
    -> Either Text Subst
  ```
* Strategy for `unifyTm` (robust + implementable now):

  1. Apply current substitution to both terms (substitute both types and term metas).
  2. Normalize both term diagrams using `normalizeTermDiagram`.
  3. Perform **first-order graph unification** on the normalized term graphs with `PTmMeta` as flex nodes:

     * boundary inputs represent rigid bound vars
     * `PTmMeta v` is flexible iff `v ∈ tmFlex`
     * occurs check: v cannot appear in its own solution
     * scope enforcement: `PTmMeta v`’s incident inputs must be exactly the first `tmvScope v` bound vars (of the mode), so any constructed solution diagram must have the same boundary inputs (enforced by construction).

You’ll need term-substitution application:

* `applySubstTerm :: TypeTheory -> Subst -> TypeExpr(sort) -> TermDiagram -> Either Text TermDiagram`

  * substitute type vars in port types
  * substitute term metavars by splicing in their solutions (term diagrams)
  * ensure modes match

Also update:

* `applySubstTy` to traverse `TATm` and apply `applySubstTerm`.
* `free…` functions:

  * `freeTmVarsType :: TypeExpr -> Set TmVar` (instead of `freeIxVarsType`)
  * `freeTmVarsDiagram :: Diagram -> Set TmVar` for diagrams whose port types embed term diagrams.

#### 2.1.7 Remove all parsing/elaboration for `index_*`

**Files:**

* `src/Strat/DSL/Parse.hs`

  * remove `polyIndexMode`, `polyIndexFun`, `polyIndexRule` parsers
  * remove keywords from lexer list if any
* `src/Strat/Poly/DSL/AST.hs`

  * remove `RPIndexMode`, `RPIndexFun`, `RPIndexRule`
  * remove `RawIxFunDecl`, `RawIxRuleDecl`, `RawIxDeclVar`, etc.
  * remove `RPTBound` and parsing of `^<n>` (bound indices)
* `src/Strat/Poly/DSL/Elab.hs`

  * remove the `RPIndex*` cases
  * remove `elabIxTerm`, `elabIxDeclVar`, `inferIxSortRule`, etc.
  * update parameter elaboration:

    * type params: `a@M` (TyVar)
    * term params: `n : Nat` (TmVar), no `index_mode` required

---

### 2.2 Remove structural discipline hard-coding (Phase B)

#### 2.2.1 Delete VarDiscipline from mode theory

**File: `src/Strat/Poly/ModeTheory.hs`**

* Remove:

  * `VarDiscipline`
  * `miDiscipline` field in `ModeInfo`
  * `setModeDiscipline`, `modeDiscipline`, `allowsDup`, `allowsDrop`, upgrade lattice, etc.
* Remove `RPStructure` item and parsing:

  * `src/Strat/Poly/DSL/AST.hs`
  * `src/Strat/DSL/Parse.hs`
  * `src/Strat/Poly/DSL/Elab.hs` case `RPStructure`

#### 2.2.2 Delete doctrine validation that hard-codes dup/drop and laws

**File: `src/Strat/Poly/Doctrine.hs`**

* Remove:

  * `checkStructuralByDiscipline`
  * `cartMode`
* This also removes name-based enforcement (`dup`, `drop`) entirely.

#### 2.2.3 Surface elaborator: resolve structural ops via schema instance, not discipline

**File: `src/Strat/Poly/Surface/Elab.hs`**

* Remove `StructuralOps` dependency on `VarDiscipline`.
* Implement capability-based structural ops, using `implements`:

**Resolution mechanism**

* Surface elaboration already receives `ModuleEnv`, `Doctrine`, and `ModeName`.
* Add helper:

  ```hs
  resolveImplMorphisms
    :: ModuleEnv
    -> Text        -- iface doctrine name (e.g. "StructCartesian")
    -> Text        -- target doctrine name
    -> [Morphism]  -- all default instances for that iface/target
  ```
* From candidates, select those whose `morModeMap` maps the schema’s mode `M` to the surface mode.

  * Convention: structural schemas use a single mode named `M` (as today’s `StructCartesian` does).
  * This is not hard-coded to “cartesian”; it’s just the schema’s own mode name.

**Using the instance**

* Instead of looking up `dup`/`drop` by name:

  * Build schema diagrams in the interface doctrine:

    * `dupSchema(a)` as a diagram in `StructCartesian` mode `M`
    * `dropSchema(a)` similarly
  * Apply the instance morphism to get concrete diagrams in the target doctrine:

    * `dupAt :: TypeExpr -> Either Text Diagram`
      = `applyMorphismDiagram mor (dupSchema instantiated at that type)`
* Use these diagrams where the surface currently injects `dup` or `drop`.

**Resulting behavior**

* If no instance provides `dup`, duplication in surface is rejected.
* If no instance provides `drop`, dropping is rejected.
* Multiple independent structural families can be supported later by adding schema selection knobs to surfaces (optional).

---

### 2.3 Functorial modalities: actions + map (Phase C)

This phase adds morphism-level action, but **without** hard-coding adjunction or any other cross-mode structure.

#### 2.3.1 New doctrine items: `action <ModName> { gen … }`

Add in the poly doctrine item list:

**Files**

* `src/Strat/Poly/DSL/AST.hs`

  * Add `RPAction RawActionDecl`
  * Define:

    ```hs
    data RawActionDecl = RawActionDecl
      { raModName :: Text
      , raGenMap  :: [(Text, RawDiagExpr)]  -- gen g -> diag
      }
    ```

* `src/Strat/DSL/Parse.hs`

  * Parse:

    ```
    action <ModName> where {
      gen <GenName> -> <DiagExpr>;
      ...
    }
    ```
  * Keep it regular (no special cases for known schemas).

* `src/Strat/Poly/DSL/Elab.hs`

  * Elaborate `RPAction` after all generators are known in the doctrine.
  * Store in doctrine:

    ```hs
    dActions :: Map ModName ModAction
    data ModAction = ModAction
      { maMod   :: ModName
      , maGenMap :: Map (ModeName, GenName) GenImage
      , maPolicy :: RewritePolicy
      , maFuel   :: Int
      }
    ```
  * Reuse `GenImage` from `Strat.Poly.Morphism` (or factor it into a common module).
  * Action checking:

    * Ensure `maMod` exists in `dModes`.
    * Ensure every generator in `mdSrc` mode has an image.
    * Ensure each image has mode `mdTgt`.
    * Ensure images have no unresolved binder holes after instantiation.

#### 2.3.2 Implement `map[ModExpr](Diagram)` in the core library

**Files**

* Add a module (recommended): `src/Strat/Poly/ModAction.hs`

  * API:

    ```hs
    applyModExpr :: Doctrine -> ModExpr -> Diagram -> Either Text Diagram
    ```
  * Behavior:

    * if `mePath` is empty: identity (must have src=tgt)
    * if `mePath = [μ1, …, μk]`: apply actions sequentially:
      `applyAction μk ( … (applyAction μ1 d) … )`
  * `applyAction :: Doctrine -> ModName -> Diagram -> Either Text Diagram`

    * similar structure to `applyMorphismDiagram`:

      * map diagram boundary types by `TMod μ` (normalize)
      * for each generator edge:

        * look up image diagram template in `dActions[μ].maGenMap`
        * instantiate it using generator parameter substitution
        * recursively map any binder-arg diagrams using the same modality expression (functorial on morphisms)
        * splice it into the host diagram

**Note on rules / joinability**

* For correctness, validate each action:

  * for every `Cell2` in source mode `mdSrc μ`, check:
    `applyAction μ lhs` and `applyAction μ rhs` are joinable within fuel/policy.
  * This is exactly `checkMorphism` specialized to “same doctrine, only one mode mapping”.

This is the kernel-level guarantee that “map respects definitional equality”.

#### 2.3.3 Diagram syntax: `map[<ModExpr>](<DiagExpr>)`

**Files**

* `src/Strat/Poly/DSL/AST.hs`

  * Add `RMap RawModExpr RawDiagExpr` to the raw diagram AST.
* `src/Strat/Poly/DSL/Parse.hs`

  * Parse as a term in diagram expressions, e.g.:

    * `map[U.F](d)`
* `src/Strat/Poly/DSL/Elab.hs`

  * Elaborate to a concrete `Diagram` by:

    1. elaborate inner `RawDiagExpr` to `Diagram`
    2. elaborate modexpr to `ModExpr`
    3. call `applyModExpr doc modexpr inner`
* Disallow `map` in rule LHS if it complicates matching; it can be expanded at elaboration time anyway.

#### 2.3.4 Coherence with `mod_eq`

If you keep `mod_eq` (recommended), actions must be coherent with it:

* For each `ModEqn lhs rhs`, require:

  * `applyModExpr lhs` and `applyModExpr rhs` are equal as functors.
* Practical check (finite, strong):

  * For each generator `g` in `meSrc lhs`:

    * build the “generic” single-edge diagram for `g` using its declared boundary (with fresh type/term vars)
    * compare `applyModExpr lhs` vs `applyModExpr rhs` on that diagram via joinability/iso-equality.

Implement this in `validateDoctrine`.

---

### 2.4 Remove adjunction keyword; replace with schema doctrine + obligations (Phase D)

#### 2.4.1 Delete `adjunction` parsing and auto-generated unit/counit

**Files**

* `src/Strat/DSL/Parse.hs`: remove `polyAdjDecl`
* `src/Strat/Poly/DSL/AST.hs`: remove `RPAdjunction` and `RawAdjDecl`
* `src/Strat/Poly/DSL/Elab.hs`: remove `RPAdjunction` case and `addAdjGens`
* `src/Strat/Poly/ModeTheory.hs`: remove `AdjDecl` and all validation

From now on, unit/counit etc are normal generators defined by schemas or by users.

#### 2.4.2 Add schema obligations as doctrine metadata

**Goal:** allow interface doctrines to declare obligations checked at `implements` time.

**Files**

* `src/Strat/Poly/Doctrine.hs`

  * Add `dObligations :: [ObligationDecl]`

* `src/Strat/Poly/DSL/AST.hs`

  * Add `RPObligation RawObligationDecl`
  * Raw form should mirror `rule` syntax but uses an *obligation expression language* (see below).
  * Minimal fields:

    ```hs
    data RawObligationDecl = RawObligationDecl
      { rodName  :: Text
      , rodMode  :: Text              -- schema mode name (e.g. "C" or "M")
      , rodTyVars :: [RawParamDecl]   -- allow (a@C) etc
      , rodTmVars :: [RawParamDecl]   -- allow (n : Nat) etc, if needed
      , rodDom   :: [RawInputShape]   -- usually ports only
      , rodCod   :: [RawPolyTypeExpr]
      , rodLHS   :: RawOblDiagExpr
      , rodRHS   :: RawOblDiagExpr
      }
    ```
  * Optional: support `for_gen` quantified obligations (see below).

* `src/Strat/DSL/Parse.hs`

  * Parse:

    ```
    obligation <name> = (...) : <dom> -> <cod> @<mode> =
      <obl-expr> == <obl-expr>
    ```
  * Optional quantified form:

    ```
    obligation <name> for_gen @<mode> =
      <obl-expr> == <obl-expr>
    ```

#### 2.4.3 Obligation expression language (minimal but powerful)

Do **not** reuse raw diagram expressions directly: obligations must refer to:

* `map[ModExpr](…)` (uses target action)
* `@gen` (current generator, when `for_gen`)
* `lift_dom(op)` / `lift_cod(op)` (monoidal lifting of unary polymorphic generator over context)

Recommended AST:

```hs
data OblExpr
  = OE_Diag RawDiagExpr                 -- an ordinary diagram expression in the schema doctrine
  | OE_Map RawModExpr OblExpr
  | OE_Gen                             -- only valid in for_gen obligations
  | OE_LiftDom RawDiagExpr             -- expects unary op diagram template
  | OE_LiftCod RawDiagExpr
  | OE_Comp OblExpr OblExpr
  | OE_Tensor OblExpr OblExpr
  | OE_Id [RawPolyTypeExpr]
  | ...
```

**Interpretation at check time (given instance morphism `m : IFace → Target`):**

* `OE_Diag d`:

  1. elaborate `d` in IFace into a concrete schema `Diagram`
  2. translate to Target via `applyMorphismDiagram m`
* `OE_Map me e`:

  1. elaborate/translate `e` to a Target `Diagram`
  2. map `me` via morphism’s modality mapping to a Target `ModExpr`
  3. apply `applyModExpr targetDoc modExpr targetDiag`
* `OE_Gen`:

  * build the Target generator diagram for the current generator being quantified
* `OE_LiftDom op`:

  * translate unary operator `op` to Target
  * tensor it across the domain context of `OE_Gen`
* `OE_LiftCod op`:

  * tensor across codomain context

This design keeps obligation checking generic and avoids hard-coding “adjunction” or “cartesian”.

#### 2.4.4 When to run obligations

**File: `src/Strat/DSL/Elab.hs`**

* In `DeclImplements`, after verifying `morSrc/morTgt`, run:

  ```hs
  checkObligations ifaceDoc morph
  ```
* Fail elaboration if any obligation fails.

**Obligation check result**

* For each produced obligation equation `(lhs, rhs)` in Target, require joinability:

  * use `joinableWithin` with policy/fuel appropriate for schema checks (likely structural+computational bidirectional, bounded).

---

## 3. Tests/examples: what to delete/update/add

### 3.1 Tests — delete/update list

#### Delete (or rewrite completely)

* `test/Test/Poly/Dependent.hs`
  It is tightly coupled to `IndexTheory`, `IxVar`, `IXBound`. Rewrite as described below.

* Any tests expecting:

  * `structure` declarations
  * adjunction auto-gens (`unit_F`, `counit_F`)

#### Update (surgical)

* `test/Test/Poly/ModeTheory.hs`

  * remove adjunction-related tests
  * add modality-action coherence tests

* `test/Test/Poly/Surface.hs`

  * remove discipline-based error messages
  * replace with schema-based capability checks

* `test/Test/Poly/CCC.hs` and any run-based tests

  * update the loaded example files and expected behavior accordingly.

### 3.2 New tests to add (Phase A–D)

#### A. Dependent indices via term diagrams (replaces old Dependent.hs)

Create new test file: `test/Test/Poly/DependentTm.hs`:

Test 1 — term normalization in types

* Doctrine:

  * modes: `M`, `I`
  * in `I`: `type Nat`, `gen Z`, `gen S`, `gen add`
  * computational rules in `I` implementing addition on diagrams
  * in `M`: `type Vec(n : I.Nat, a@M) @M`
* Assert `normalizeTypeDeep` reduces:

  * `Vec(add(Z, n), A)` to `Vec(n, A)` (where `n` is a term param)
  * `Vec(add(S(Z), S(Z)), A)` to `Vec(S(S(Z)), A)` for closed terms

Test 2 — type unification uses term normalization

* Unify:

  * `Vec(add(Z, n), A)` with `Vec(n, A)` succeeds
  * `Vec(S(n), A)` with `Vec(n, A)` fails

Test 3 — scope safety (escape prevented by explicit arguments)

* Build a rewrite rule that applies under a binder with bound term vars in `dTmCtx`.
* Ensure a scope-0 term metavariable cannot “capture” bound term vars (should be impossible to construct occurrences wired to deeper vars).

#### B. Surface duplication/drop via schema instances

Add `test/Test/Poly/SurfaceStruct.hs`:

* Define in test source a minimal schema doctrine:

  * `doctrine StructCopy where { mode M; gen dup (a@M): [a] -> [a,a] @M; … laws … }`
  * `doctrine StructDrop …`
* Define target doctrine with/without morphism implementations.
* For each:

  * attempt to elaborate a surface term duplicating a variable
  * expect success iff `implements StructCopy for Target …` is present.
  * similar for drop.

#### C. Modality actions + map

Add `test/Test/Poly/ModAction.hs`:

* Define doctrine with modes `A`, `B`, modality `F : A -> B`, action `F` mapping each generator in `A` to a generator in `B`.
* Assert:

  * `map[F](g ; h)` equals `map[F](g) ; map[F](h)`
  * `mod_eq U.F -> id@A` plus actions implies `map[U.F](d)` joinable with `d`

#### D. Schema obligations: adjunction triangle

Add `test/Test/Poly/AdjunctionObligation.hs`:

* Define schema doctrine `AdjSchema` with modes `C`, `L`, modalities `F : C -> L`, `U : L -> C`,
  generators `eta`, `eps` (as in current auto-gen shapes).
* Attach obligations for triangles using `map`.
* Define a target doctrine that *incorrectly* defines `eta/eps` (or actions) and show:

  * elaboration fails at `implements AdjSchema for Target using m` with triangle obligation name in the error.
* Define a corrected target doctrine and show it succeeds.

---

## 4. Examples / stdlib: new/deleted/updated

### 4.1 stdlib updates

#### Update: `stdlib/struct.cartesian.llang`

* Remove `structure M = cartesian;`
* Keep generators and laws; they now purely define the schema doctrine.

If you also want partial capabilities:

* Add new schema doctrines:

  * `stdlib/struct.copy.llang` (dup + coassoc + cocomm)
  * `stdlib/struct.drop.llang` (drop only, no laws needed beyond well-typedness)
  * Optionally `stdlib/struct.affine.llang`, `stdlib/struct.relevant.llang`

#### New: `stdlib/schema.adjunction.llang`

* A schema doctrine for adjunction:

  * declare modes `C`, `L`
  * declare modalities `F : C -> L`, `U : L -> C`
  * declare generators:

    * `eta (a@C) : [a] -> [U(F(a))] @C`
    * `eps (b@L) : [F(U(b))] -> [b] @L`
  * declare **obligations**:

    * Triangle 1 in `L`: `eps ; map[F](eta) == id`
    * Triangle 2 in `C`: `map[U](eps) ; eta == id`
  * Optional `for_gen` naturality obligations using `@gen` and `lift_dom/lift_cod`.

#### New: `stdlib/schema.monad.llang` (optional in Phase D)

* Monad schema with modality `T : M -> M`, generators `ret`, `join`, obligations for monad laws.

#### New: `stdlib/schema.fibration.llang` (optional; the dependent-type story)

* This can come later; Phase A already subsumes index theory.
* If implemented, fibration schema’s obligations can ensure well-behaved reindexing.

### 4.2 examples updates

#### Dependent examples

Update these to use term-diagram indices (no `index_*`):

* `examples/dependent/vec.llang`

  * Remove `index_mode`, `index_fun`, `index_rule`
  * Replace index funs with generators in mode `I`:

    * `gen Z : [] -> [Nat] @I;` etc
    * rules as ordinary `rule computational ... @I` on diagrams
  * Type `Vec(n : Nat, a@M) @M` remains
  * Generator instances in the run remain syntactically similar:

    * `append{A, S(Z), S(Z)} ; expect22{A}` is still fine if type args are inferred.

* `examples/dependent/implicit_binder_index.llang`

  * Binder slot must explicitly mark term variables:

    * `binder { tm n : Nat } : [Vec(n)]`

* `examples/dependent/free_index_must_fail.llang`

  * Keep intent: running `make` without supplying the term parameter must fail.
  * Update to new term parameters; error should mention missing term argument / unsolved term meta.

#### Mode examples (lnl, staging)

* `examples/lib/modes/lnl.llang`

  * Remove `structure` and `adjunction`
  * Import `stdlib/struct.cartesian.llang`
  * Define required gens `dup/drop` (or import) and provide an implementation morphism:

    * `morphism cartInst : StructCartesian -> LNL { … }`
    * `implements StructCartesian for LNL using cartInst`
  * Define unit/counit generators explicitly (or via schema morphism), and create an adjunction instance:

    * `morphism adjInst : SchemaAdjunction -> LNL { … }`
    * `implements SchemaAdjunction for LNL using adjInst`
  * Add modality `action F` and `action U` if the adjunction obligations use `map`.

* `examples/lib/modes/staging.llang`, `staging_mode_map.llang`, etc.

  * If they only relied on `mod_eq`, they may not need actions.
  * If they need `map`, add `action quote` / `action splice` mappings.

#### Pushout examples

* `examples/lib/pushout/*`

  * Remove merging of index theories (since they no longer exist).
  * Otherwise mostly unchanged, but update any `structure` usage.

---

## 5. “How to check your own work” (bullet-proof guidance)

### 5.1 Mechanical validation checklist (per phase)

**Always:**

1. `stack test` (must be green)
2. Run at least 2 example runs:

   * one algebraic: `examples/run/algebra/ccc.run.llang`
   * one dependent: new `examples/run/dependent/vec.run.llang` (create if needed)
3. Grep for removed constructs:

   * `grep -R "index_mode|index_fun|index_rule" -n src stdlib examples test` must return nothing
   * `grep -R "structure .*=" -n` must return nothing
   * `grep -R "adjunction " -n` must return nothing

### 5.2 Expected outputs (sanity checks)

#### Dependent Vec example

* After normalization, the type index `add(S(Z), S(Z))` should normalize to `S(S(Z))`.
* Ensure `extract diagram` output contains **no** residual “index function” artifacts (none exist anymore).
* If you log types, `Vec(add(S(Z), S(Z)), A)` should become `Vec(S(S(Z)), A)`.

#### Free term parameter must fail

* Running a term that leaves term parameters unsolved should produce a clear error:

  * must mention the generator name and the missing term arguments / unsolved term metavars.

#### Action/map coherence

* Add a tiny test doctrine and run:

  * `map[U.F](d)` should normalize/join to `d` when `mod_eq U.F -> id@A` and actions are coherent.

### 5.3 Debugging tips

* Add a `--debug` flag to your CLI run path if helpful (optional).
* When obligation checks fail, print:

  * the obligation name
  * the instantiated LHS/RHS diagrams (pretty-printed)
  * and the normalization trace depth/fuel if joinability fails.

---

## 6. SPEC.md updates (what to change)

Update SPEC.md to match the new kernel. Concrete edit plan:

### 6.1 Remove or rewrite these sections entirely

* Anything describing:

  * `IndexTheory`, `IxTheory`, `IxTerm`, `IxVar`, `IXBound`
  * `index_mode`, `index_fun`, `index_rule`
  * `structure` and the discipline lattice
  * `adjunction F dashv U` and auto-generated unit/counit
  * hard-coded `dup/drop` lookup

### 6.2 Add/replace with these sections

#### Type arguments and dependent indices

* Replace:

  * `TypeArg = TAType | TAIndex IxTerm`
    with:
  * `TypeArg = TAType | TATm TermDiagram`
* Define `TermDiagram` restriction (and defer full details to `RESTRICTIONS.md`).

#### Definitional equality for term indices

* Replace index normalization section with:

  * term arguments normalize by diagram rewriting in their term mode
  * policy: `UseOnlyComputationalLR` by default (or configurable)
  * fuel-bounded

#### Modality actions and `map`

* Introduce:

  * `action μ` declares generator images for each generator in `src(μ)`
  * `map[μ](d)` elaborates by applying these images recursively
  * action correctness: preserves rewrite equality in the source mode
  * coherence with `mod_eq`: equal modality expressions must induce equal actions (checked on generators)

#### Schemas as doctrines + obligations

* Specify:

  * a schema is just a doctrine used as an interface
  * obligations are extra declarations checked at `implements`
  * obligations can refer to `map`, and optionally quantified forms (`for_gen`)

### 6.3 Pushout section adjustment

* Remove references to “index theory merging”.
* If you keep pushout requiring identical mode theory, mention actions too:

  * either require identical sets of actions, or define a merge strategy (can be restricted initially).

---

## 7. Create `RESTRICTIONS.md` (temporary tradeoffs)

Add a new file `RESTRICTIONS.md` documenting any temporary limits. Keep it short and explicit.

Minimum content (current known restriction):

### 7.1 Term fragment restriction for type indices

* Term arguments (`TATm`) are restricted to a fragment:

  * no boxes
  * no feedback
  * no splices
  * no binder arguments inside term diagrams
  * only generator nodes (`PGen`) and term metavariable nodes (`PTmMeta`)
  * exactly one output
* Rationale:

  * simplifies normalization/unification and ensures definitional equality remains tractable
* Enforcement:

  * `validateTermDiagram` (or checks inside `checkType`) rejects out-of-fragment terms.

### 7.2 (Optional) Additional restrictions if you choose them

Only add these if you actually implement them:

* “term indices must live in acyclic modes”
* “term normalization uses only computational rules”
* “no map inside rules” (if you enforce it)

---

## 8. Concrete worklist (recommended commit order)

1. **Delete IndexTheory** and compile by stubbing term args:

   * introduce `PS_Tm` / `TATm` but initially don’t normalize them (just typecheck)
   * update compilation errors until green

2. Implement **term argument normalization** in `normalizeTypeDeep`.

3. Implement **unifyTm** and integrate into type unification and diagram boundary unification.

4. Remove `structure`:

   * delete VarDiscipline and all uses
   * update surface elaboration to schema-based duplication/drop.

5. Add modality **actions**:

   * implement `action` decl parsing/elaboration/storage
   * implement `applyModExpr` and `map[...]` syntax
   * add action-preserves-rules validation.

6. Add **obligations** and enforce at `implements`.

7. Update stdlib and examples accordingly.

---

## 9. Files touched (index)

This is a non-exhaustive “expect to edit” list to guide navigation:

* Core types:

  * `src/Strat/Poly/TypeExpr.hs`
  * `src/Strat/Poly/TypeTheory.hs`
  * `src/Strat/Poly/UnifyTy.hs`
  * `src/Strat/Poly/Diagram.hs`
  * `src/Strat/Poly/Graph.hs`

* Doctrine:

  * `src/Strat/Poly/Doctrine.hs`
  * `src/Strat/Poly/ModeTheory.hs`

* Frontend DSL:

  * `src/Strat/DSL/Parse.hs`
  * `src/Strat/Poly/DSL/AST.hs`
  * `src/Strat/Poly/DSL/Parse.hs`
  * `src/Strat/Poly/DSL/Elab.hs`
  * `src/Strat/DSL/Elab.hs` (implements hook for obligations)

* Morphisms / pushout:

  * `src/Strat/Poly/Morphism.hs` (remove Ix mappings; add term arg mapping)
  * `src/Strat/Poly/Pushout.hs` (remove ix theory merge)

* Surfaces:

  * `src/Strat/Poly/Surface/Elab.hs`

* Prelude:

  * `src/Strat/Frontend/Prelude.hs` (remove dIndexModes/dIxTheory)

* Tests:

  * `test/Test/Poly/Dependent.hs` (replace)
  * `test/Test/Poly/Surface.hs` (rewrite)
  * add new tests for actions/obligations

* stdlib/examples:

  * `stdlib/struct.cartesian.llang` (remove `structure`)
  * new `stdlib/schema.adjunction.llang`
  * update `examples/dependent/*`
  * update `examples/lib/modes/*` using adjunction/structure

---

## 10. Notes on engineering tradeoffs (and remedies)

### Tradeoff allowed now: term fragment restriction for indices

This is acceptable and already expected. Keep it confined to:

* checks in `checkType` / `normalizeTypeDeep` / `unifyTm`
* documented in `RESTRICTIONS.md`

**Remedy later (no duplication):**

* Expand allowed fragment gradually:

  * allow limited boxes if you define semantics for indices under binders
  * allow richer term graphs (sharing) once unifier supports it
  * keep the same `TermDiagram` representation; only relax validators.

### Avoid these tradeoffs (they cause major later duplication)

* Keeping any form of separate index unifier/normalizer “just for now”.
* Hard-coding `dup/drop` by name “temporarily”.
* Keeping `adjunction` keyword and auto-generated unit/counit.
