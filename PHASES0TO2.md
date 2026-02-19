## Phase 0 — Baseline + refactoring scaffolding

### 0.1 Lock in a “Kernel boundary” module

**Goal:** Reduce coupling so later refactors don’t require chasing imports across the whole tree.

#### Add: `src/Strat/Poly/Kernel.hs`

Create a new internal module that re-exports the *intended stable* kernel-facing API used by the frontend and DSL elaboration. Start small and explicit.

Recommended exports (based on current code usage patterns):

* `Doctrine`, `validateDoctrine`, `checkDoctrine`

  * from `Strat.Poly.Doctrine`
* `TypeExpr`, `TypeArg`, `TypeRef`, `TypeName`, `TypeVarName`

  * from `Strat.Poly.TypeExpr` (and any small supporting modules already used)
* Type normalization entry points

  * from `Strat.Poly.TypeNormalize`
* Unification entry points

  * from `Strat.Poly.UnifyTy`
* Join-proof search entry points and results

  * `SearchOutcome(..)` from `Strat.Common.Search`
  * `autoJoinProof` from `Strat.Poly.Normalize` (if used outside Poly)

Keep the surface small; don’t “export *everything*”. This module’s job is *curation*.

#### Minimal migration (do now, not later)

Update the **frontend/DSL** modules that are most likely to churn in upcoming phases to import `Strat.Poly.Kernel` instead of the underlying modules directly. Concretely:

* `src/Strat/DSL/Elab.hs`
* `src/Strat/Frontend/Run.hs` (if it imports Poly normalization/unification directly)
* `src/Strat/Frontend/ModuleEnv.hs` (if it uses Poly types)

Do not attempt a repo-wide migration; just move the boundary to where it pays off first.

### 0.2 Baseline regression snapshot

No code change needed other than ensuring current tests compile after Phase 0.1.

---

## Phase 1 — Typed doctrine functors (replace `doctrine_template`)

### Phase 1 design decisions (resolve open choices)

1. **Functor definitions are stored as values in `ModuleEnv`**, not as hidden doctrines/morphisms in the normal namespaces.

   * This avoids name collisions and prevents internal names (especially underscore-prefixed) from leaking into user-visible results.
2. **Functor application must preserve the target doctrine’s names.**

   * Current `computePolyPushout` *always* prefixes disjoint names and canonically renames shared items to the source’s names. That is unacceptable for `apply` because the result becomes hard to use (and functor bodies with internal names become unreferencable).
3. Therefore, **implement a right-biased pushout variant** for `apply`:

   * Shared interface items are identified using the *target’s* images.
   * Target’s disjoint items keep their original names.
   * Functor-body disjoint items keep their original names *unless they collide*; collisions are resolved by prefixing with the functor name (and freshening deterministically).

### 1.1 Remove templates and instantiation from the top-level DSL

#### Change: `src/Strat/DSL/AST.hs`

Remove:

* `RawDoctrineTemplate`
* `RawDoctrineInstantiate`
* `DeclDoctrineTemplate`
* `DeclDoctrineInstantiate`

Add:

* `RawDoctrineFunctor`
* `RawDoctrineApply`
* `DeclDoctrineFunctor`
* `DeclDoctrineApply`

Recommended AST shapes:

```haskell
data RawDoctrineFunctor = RawDoctrineFunctor
  { rdfName      :: Text          -- functor name
  , rdfParam     :: Text          -- parameter name (reserved; not yet used for qualification)
  , rdfSchema    :: Text          -- doctrine name of schema
  , rdfBodyItems :: [RawPolyItem] -- body = poly doctrine items (like in doctrine blocks)
  }

data RawDoctrineApply = RawDoctrineApply
  { rdaName       :: Text         -- new doctrine name
  , rdaFunctor    :: Text         -- functor name
  , rdaTarget     :: Text         -- target doctrine name
  , rdaUsingMorph :: Maybe Text   -- optional morphism name schema->target
  }
```

Extend `RawDecl` accordingly.

#### Change: `src/Strat/DSL/Parse.hs`

Remove parsing support for:

* `doctrine_template ... where { ... }`
* `doctrine X = instantiate ... using { ... }`

Add parsing support for:

**Functor declaration**

```llang
doctrine_functor F(L : Schema) where {
  -- poly items: mode/modality/mod_eq/type/gen/cell/action/obligation...
}
```

**Functor application**

```llang
doctrine New = apply F to Target using someMorphism;
doctrine New = apply F to Target;  -- allowed only if schema->target morphism is unique in env
```

Parsing constraints:

* Exactly one parameter for now.
* `L` is parsed and stored but not used for qualification (document this).

### 1.2 Update the environment to store functors (not templates)

#### Change: `src/Strat/Frontend/Env.hs`

Remove:

* `meTemplates :: Map Text DoctrineTemplate`

Add:

* `meFunctors :: Map Text DoctrineFunctorDef`

Add new definition (in a good place: probably `Strat.Frontend.Env` or a new small module if you want to keep Env light):

```haskell
data DoctrineFunctorDef = DoctrineFunctorDef
  { dfName   :: Text
  , dfSchema :: Text
  , dfBody   :: Doctrine   -- elaborated doctrine extending schema
  , dfIncl   :: Morphism   -- inclusion morphism Schema -> dfBody
  }
```

Update:

* `emptyModuleEnv`
* `mergeEnv`
* any pretty/debug printing of env if present

### 1.3 Elaborate functor declarations

#### Change: `src/Strat/DSL/Elab.hs`

Add a new elaboration branch:

* `DeclDoctrineFunctor`

Implementation steps:

1. **Lookup schema doctrine** in `meDoctrines`.

2. **Elaborate the functor body** as a poly doctrine that extends schema:

   * Construct a `RawPolyDoctrine` with:

     * `rpdName = "<internal>"` (not exposed, but must be valid text)
     * `rpdExtends = Just schemaName`
     * `rpdItems = rdfBodyItems`
   * Call `Strat.Poly.DSL.Elab.elabPolyDoctrineWithBudgetResult env rawPolyDoctrine`
   * Extract the `Doctrine` value.

3. **Build inclusion morphism** `Schema -> Body`.

   * Do **not** reuse `buildPolyFromBase` (it is entangled with “extends” and env insertion).
   * Instead, add a **pure helper** inside `Strat.Poly.Pushout` (or a new module under `Strat.Poly.Morphism`) that constructs an inclusion morphism given two doctrines.

Best option (minimal diff + reuse existing logic):

* In `Strat.Poly.Pushout`, **export** a new utility:

  * `mkInclusionMorphism :: MorphismName -> Doctrine -> Doctrine -> Either Text Morphism`
* Implement it by reusing the existing `buildInj` logic (it already creates correct generator images with binder metavariables).

4. Store `DoctrineFunctorDef` into `meFunctors`.

   * Do **not** insert the functor body doctrine into `meDoctrines`.
   * Do **not** insert the inclusion morphism into `meMorphisms`.

5. Validate uniqueness:

   * If a functor name already exists, error with a clear message.

### 1.4 Elaborate functor application

#### Change: `src/Strat/DSL/Elab.hs`

Add a new elaboration branch:

* `DeclDoctrineApply`

Steps:

1. Lookup functor def `F` in `meFunctors`.

2. Lookup target doctrine `L` in `meDoctrines`.

3. Resolve the implementation morphism `m : Schema -> L`:

   * If `using` is given: lookup in `meMorphisms` and check `morSrc` name matches `dfSchema` and `morTgt` name matches `L`.
   * If `using` absent:

     * scan `meMorphisms` for morphisms where `src = dfSchema` and `tgt = L`
     * require **exactly one**; otherwise error with candidates listed.

4. Compute `apply` result as a right-biased pushout/merge (details in 1.5).

5. Insert:

   * the new doctrine into `meDoctrines`
   * generated morphisms into `meMorphisms`:

     * `New.inl : dfBody -> New` (coercion)
     * `New.inr : L -> New` (coercion)
     * `New.glue : Schema -> New` (coercion)
       These names match existing pushout conventions and keep downstream tools consistent.

### 1.5 Implement right-biased pushout for `apply`

This is the critical part to keep results usable and clean.

#### Change: `src/Strat/Poly/Pushout.hs`

Add:

* `computePolyPushoutPreferRight :: Text -> Text -> Morphism -> Morphism -> Either Text PolyPushoutResult`

  * Parameters:

    * `newName` (doctrine name)
    * `leftPrefix` (use the functor name for collision renames)
    * `incl : Schema -> Body`
    * `impl : Schema -> Target`

Semantics:

* Produce pushout where **Target’s names are canonical**.

Implementation structure (recommended for clarity):

1. **Validate preconditions** (mostly same as current `computePolyPushout`):

   * `morSrc incl == morSrc impl`
   * identity `morModeMap` and `morModMap` for both morphisms (keep consistent with current pushout requirements)
   * same mode theory *up to 1-category structure* (see Phase 2 notes; for now compare modes+modalities+mod_eq only)

2. **Extract interface renamings**

   * Use `requireAttrSortRenameMap`, `requireTypeRenameMap`, `requireGenRenameMap` on both morphisms to get:

     * src -> image maps in Body and Target
     * for types, also the permutation information (see below)
   * Compute renaming maps that rename **Body’s interface images** to **Target’s interface images**:

     * `AttrSortRenameMap` : `imgB -> imgT`
     * `TypeRenameMap` : `imgB -> imgT`
     * `GenRenameMap` : `imgB -> imgT`
   * Compute a `TypePermMap` for renaming `imgB` to `imgT`.

     * If you implement the general case (incl not identity), use the permutation composition formula:

       * `invB` = inverse perm stored for `src -> imgB`
       * `invT` = inverse perm stored for `src -> imgT`
       * desired perm from `imgB`-arg-order to `imgT`-arg-order:

         * `perm = [ invB !! i | i <- invertPerm invT ]`
       * Handle `Nothing` perms as identity `[0..n-1]`
     * If you want a simpler first landing:

       * accept only identity `incl` (it should be identity for functor bodies anyway) and compute perm purely from `impl`.

3. **Collision-only renaming for Body disjoint items**

   * Unlike `computePolyPushout`, do **not** rename Target disjoint names at all.
   * For Body disjoint names (types/gens/cells/attrsorts):

     * keep original name unless it conflicts with something already in Target (or conflicts after interface renaming)
     * if conflict:

       * rename to `fresh(leftPrefix <> "_" <> oldName)`
       * freshening must be deterministic and stable:

         * use the existing `freshTypeName`, `freshGenName`, etc.

   You need new helpers parallel to `disjointTypeRenames` / `disjointGenRenames` that only rename on collision (instead of prefixing everything).

4. **Rename Body doctrine**

   * Apply a single `renameDoctrine` with:

     * interface rename maps
     * disjoint collision rename maps
   * IMPORTANT: `renameDoctrine` must be extended to rename:

     * `dActions` (renaming `maGenMap` keys and diagrams)
     * `dObligations` (traverse `RawOblExpr` and rename embedded `RawDiagExpr` + generator references)
       Current code leaves `dActions`/`dObligations` untouched, which is incorrect under renaming and will break functors that define actions/obligations.

5. **Merge renamed Body into Target**

   * Fix `mergeDoctrine` so it merges the full doctrine record correctly (see 1.6).
   * Result doctrine name becomes `newName`.

6. **Build morphisms**

   * `inr : Target -> New`:

     * inclusion; use `buildInj` with empty rename maps (identity)
   * `inl : Body -> New`:

     * use the same rename maps used for renaming Body into the merged doctrine
   * `glue : Schema -> New`:

     * best: **retarget** the implementation morphism `impl` to the pushout doctrine:

       * `glue = impl { morName = newName <> ".glue", morTgt = newDoctrine, morIsCoercion = True }`
     * This is correct because `New` contains Target unchanged, so all referenced declarations still exist.

7. Return `PolyPushoutResult { pdrDoctrine = New, pdrInl = inl, pdrInr = inr, pdrGlue = glue }`.

#### Also fix correctness bugs in existing pushout helpers

While you’re here (this matters for robustness and keeps the codebase cleaner):

* In `requireTypeRenameMap`:

  * when morphism omits a mapping and defaults to identity, **check that the target doctrine actually contains that type** and that its arity matches.
* In `requireAttrSortRenameMap`:

  * same: if default identity is assumed, ensure target has that attrsort.

These checks prevent silent failures and make error messages sane.

### 1.6 Make doctrine merge/rename actually correct for actions and obligations

#### Change: `src/Strat/Poly/Pushout.hs`

Fix `mergeDoctrine` and `renameDoctrine`.

##### `mergeDoctrine`

Current `mergeDoctrine` discards right-hand `dAcyclicModes`, `dActions`, `dObligations` by copying them from `base` only. This is wrong for functors and for pushouts in general.

Implement merging as:

* `dName`: set by caller (`newName`)
* `dModes`: must be compatible; keep base’s (they should match)
* `dAcyclicModes`: union (or require equality and keep union; union is safe)
* `dAttrSorts`: merge maps; on collision require identical decl
* `dTypes`: merge per mode; on collision require identical decl
* `dGens`: merge per mode; on collision require identical decl
* `dCells2`: merge by name; on collision require iso-equal or identical (reuse `mergeCells2`)
* `dActions`: merge by modality name; on collision require identical `ModAction` (including `maGenMap`)
* `dObligations`: merge by obligation name; on collision require identical

##### `renameDoctrine`

Extend it so renaming is applied consistently to all payloads:

* `dActions`:

  * rename `maGenMap` keys `(mode, genName)` using gen rename map
  * rename diagrams in values using `renameDiagram`
* `dObligations`:

  * traverse both `obLHSExpr` and `obRHSExpr`:

    * rename `OblExprGen` references using gen rename map
    * rename embedded `RawDiagExpr`:

      * generator names in `RDGen`
      * types inside `RDId`, `RDTerm`, etc using the existing `renameTy` (you may need a `renameRawPolyTypeExpr` helper to reuse `renameTypeExpr`)
  * do not change `obBoundary` except by applying `renameTy` to its `TypeExpr`s (it currently stores elaborated `TypeExpr`, so use the same path as for cell boundaries)

If there isn’t already a raw-type-expr renamer, add it in a small new module (e.g. `Strat.Poly.DSL.Rename`) rather than embedding more traversal logic in `Pushout.hs`.

### 1.7 Delete `doctrine_template` machinery

#### Delete file

* `src/Strat/DSL/Template.hs`

#### Remove references

* Remove `Strat.DSL.Template` from imports in `Strat.DSL.Elab`.
* Remove Template-related code paths:

  * `elabDoctrineTemplate`
  * `elabDoctrineInstantiate`
  * any map updates to `meTemplates`

### 1.8 Update tests

#### Change: `test/Test/DSL/Templates.hs` → rename to `Functors.hs` (recommended)

* Replace the template/instantiate test with a functor/apply test.

Add at least these cases:

1. **Basic apply preserves target names**

   * schema `S` with `mode M; type X @M;`
   * target `L` with `mode M; type Box @M;`
   * morphism `impl : S -> L` mapping `X -> Box`
   * functor `F(L : S)` adds `gen flip : [X] -> [X] @M;`
   * apply: `doctrine R = apply F to L using impl;`
   * Assert in the elaborated doctrine `R`:

     * `Box` exists
     * no type `X` exists (unless target actually has `X`)
     * `flip` has signature `[Box] -> [Box]`

2. **Collision renaming uses functor name prefix**

   * target has `gen get : [] -> [Box] @M;`
   * functor also introduces `gen get : [] -> [X] @M;`
   * after apply, target’s `get` must remain `get`, functor’s must become `F_get` (or `F_get_1` if needed)
   * Assert both exist.

3. **`using` omission resolves unique morphism**

   * Provide exactly one `S -> L` morphism in env; omit `using` in apply; test succeeds.
   * Provide two and ensure apply fails with a “non-unique morphism” error mentioning candidates.

### 1.9 Update examples and data-files

#### Replace template examples

* Rewrite `examples/lib/templates/state.template.llang` into **schema + morphisms + functor + apply**.
  Suggested replacement file name: `examples/lib/functors/state.llang` (cleaner), but you can also keep location and rename contents.

Concrete content pattern (works with the right-biased apply semantics):

```llang
doctrine Base where {
  mode M;
  type Nat @M;
  type Bool @M;
}

doctrine StateSchema where {
  mode M;
  type S @M;
}

morphism chooseNat : StateSchema -> Base where {
  type S@M -> Nat@M;
}

morphism chooseBool : StateSchema -> Base where {
  type S@M -> Bool@M;
}

doctrine_functor State(L : StateSchema) where {
  gen get : [] -> [S] @M;
  gen put : [S] -> [] @M;
}

doctrine StateNat = apply State to Base using chooseNat;
doctrine StateBool = apply State to Base using chooseBool;
```

* Update `examples/run/templates/state.run.llang` accordingly (or rename directory from `templates` to `functors` and update references).

#### Update `package.yaml` `data-files`

Remove entries for deleted template files, and add your new functor example files if tests/examples load them via `getDataFileName`.

At minimum remove:

* `examples/lib/templates/state.template.llang`
* `stdlib/effects/exception.template.llang`
* `stdlib/effects/writer.template.llang`

(Or rewrite them as functors; see RESTRICTIONS note below about schema limitations.)

---

## Phase 2 — Mode theory 2-cells (`mod_transform`)

### Phase 2 design decisions (resolve open choices)

* `mod_eq` remains the definitional equality (rewrite system) on `ModExpr`.
* `mod_transform` introduces **directed 2-cells** between `ModExpr`s, and **does not affect definitional equality**.
* **Style 1** witness (recommended for first landing): a transform is witnessed by a **named generator** with a constrained signature.
* No implicit coercion insertion yet. Users explicitly use the witness generator in diagrams. (Auto-insertion can come later.)

### 2.1 Extend `ModeTheory` to include transforms

#### Change: `src/Strat/Poly/ModeTheory.hs`

Add:

```haskell
newtype ModTransformName = ModTransformName Text
  deriving (Eq, Ord, Show)

data ModTransformDecl = ModTransformDecl
  { mtdName    :: ModTransformName
  , mtdFrom    :: ModExpr
  , mtdTo      :: ModExpr
  , mtdWitness :: GenName
  } deriving (Eq, Show)

data ModeTheory = ModeTheory
  { mtModes      :: Map ModeName ModeInfo
  , mtDecls      :: Map ModName ModDecl
  , mtEqns       :: [ModEqn]
  , mtTransforms :: Map ModTransformName ModTransformDecl
  }
```

Update:

* `emptyModeTheory`
* any constructors in tests (`mkModes` in `test/Test/Poly/Helpers.hs`)

Add helper:

* `addModTransformDecl :: ModTransformDecl -> ModeTheory -> Either Text ModeTheory`

  * check `mtdFrom` and `mtdTo` are well-formed mod expressions
  * check `meSrc`/`meTgt` match
  * check name uniqueness

### 2.2 Add new poly item + parsing

#### Change: `src/Strat/Poly/DSL/AST.hs`

Add:

* `RPModTransform RawModTransformDecl`

and define:

```haskell
data RawModTransformDecl = RawModTransformDecl
  { rmtName    :: Text
  , rmtFrom    :: RawModExpr
  , rmtTo      :: RawModExpr
  , rmtWitness :: Maybe Text
  }
```

#### Change: `src/Strat/DSL/Parse.hs`

Extend `polyItemDecl` to parse:

```llang
mod_transform eta : id@C => U.F;
mod_transform eta : id@C => U.F witness etaGen;
```

Parsing rules:

* `witness` clause is optional; if omitted, witness defaults to the transform name.
* Require terminating `;` as with other poly items.

### 2.3 Elaborate `mod_transform` into the doctrine

#### Change: `src/Strat/Poly/DSL/Elab.hs`

In the `elabPolyItem` dispatcher, add:

* `RPModTransform decl -> ...`

Implementation steps in elaboration:

1. Elaborate `RawModExpr` → `ModExpr` using existing machinery.

2. Enforce:

   * `meSrc from == meSrc to`
   * `meTgt from == meTgt to`

3. Determine witness name:

   * `witness = fromMaybe rmtName rmtWitness`

4. Lookup witness generator:

   * mode must be `meTgt from`
   * generator must exist in `dGens` for that mode

5. Witness signature check (keep strict for Phase 2; it makes the feature well-defined):

Require the witness generator `w` to satisfy:

* `gdTyVars w` has **exactly 1** type variable `A` with:

  * `tvMode A == meSrc from`
* `gdTmVars w` is empty
* `gdDom w == [InPort (TMod from (TVar A))]` up to definitional simplification of `TMod id` if your normalizer does that
* `gdCod w == [TMod to (TVar A)]` (again, allow definitional simplification)
* `gdAttrs w` empty (or allow, but then you must specify how attributes behave under transforms; simplest is empty for now)

6. Insert `ModTransformDecl` into `dModes.mtTransforms`.

### 2.4 Doctrine merge/rename must handle transforms

This is required so:

* pushouts and applies don’t drop transforms
* renames (collision renaming in apply) don’t leave transforms pointing at old witness names

#### Change: `src/Strat/Poly/Pushout.hs`

* Extend `mergeDoctrine` (Phase 1 fix) to merge mode theories:

  * require same modes + modality decls + mod_eq list (the 1-category part)
  * union `mtTransforms`, requiring identical on name collision

* Extend `renameDoctrine` to rename transforms’ witness generator names:

  * apply `GenRenameMap` to `mtdWitness`
  * leave `mtdFrom`/`mtdTo` unchanged

### 2.5 Update tests

#### Change: `test/Test/Poly/Helpers.hs`

Update `mkModes` to populate `mtTransforms = M.empty`.

#### Add: `test/Test/Poly/ModeTransforms.hs` (or extend `ModeTheory.hs`)

Add tests:

1. **Parse + elab success**

   * Create a doctrine with:

     * modes `C`, `D`
     * modalities `F : C->D`, `U : D->C`
     * generator `eta(a:C)` with signature `[]?` per your type-var syntax; minimally:

       * `gen eta(a : C) : [a] -> [U(F(a))] @ C;`
     * transform:

       * `mod_transform eta : id@C => U.F;`
   * Assert:

     * `mtTransforms` contains entry `eta`
     * `mtdFrom` is `id@C`, `mtdTo` is `U.F`, witness is `eta`

2. **Reject mismatched endpoints**

   * `mod_transform bad : F => U;` where src/tgt mismatch
   * Expect elaboration error.

3. **Reject wrong witness signature**

   * witness generator exists but has:

     * wrong mode
     * or extra ports
     * or missing type var
   * Expect error that cites expected shape.

### 2.6 Update stdlib example (optional but recommended)

#### Change: `stdlib/schema.adjunction.llang`

Add:

```llang
mod_transform eta : id@C => U.F;
mod_transform eps : F.U => id@D;
```

This makes stdlib demonstrate 2-cells. Because these generators already exist, it’s a low-cost upgrade.

---

## SPEC.md updates (keep it consistent with code after Phases 0–2)

### Add/modify in “DSL syntax summary” (Section 8)

1. **Remove** any mention of:

   * `doctrine_template`
   * `instantiate`

2. **Add**:

#### Doctrine functors

* Syntax:

  * `doctrine_functor F(L : Schema) where { <poly items> }`
* Meaning:

  * `F` defines an extension doctrine `Body` elaborated as if it were `doctrine Body extends Schema`.
  * A functor is stored as `(Schema, Body, incl : Schema -> Body)`.

#### Apply

* Syntax:

  * `doctrine New = apply F to Target using impl;`
  * `doctrine New = apply F to Target;` (only if unique `Schema -> Target` morphism exists)
* Meaning:

  * `New` is computed as the pushout of `Schema -> Body` and `Schema -> Target`, with **Target’s names preserved**.
  * New declarations introduced by the functor body keep their names unless they collide with Target; collisions are resolved by prefixing with the functor name.

Also document inserted morphisms:

* `New.inl`, `New.inr`, `New.glue`

### Update “Mode theory” section

Add a new subsection:

#### `mod_transform`

* Syntax:

  * `mod_transform t : μ => ν [witness g];`
* Semantics:

  * Adds a directed 2-cell between modality expressions.
  * Does not contribute to definitional equality (`mod_eq`).
* Witness constraints (Phase 2 restrictions):

  * The witness is a generator satisfying the constrained polymorphic signature described above.

---

## RESTRICTIONS.md updates (keep it consistent with code after Phases 0–2)

Add a new section “Functor restrictions (Phase 1)”:

1. **Single parameter only**:

   * `doctrine_functor` supports exactly one doctrine parameter `L : Schema`.

2. **Schema should be signature-only (recommended restriction)**

   * Because morphisms currently map types/generators but not cells/actions/obligations, using a schema with equations/obligations is not semantically enforceable across implementations.
   * Until morphisms map cells/obligations, schemas used for functor parameters should contain:

     * modes, modalities, mod_eq (optionally)
     * attrsort/type/gen/data declarations
     * **no cells, no actions, no obligations**
       (If you choose not to enforce this in code, document it as a semantic caveat.)

3. **Apply naming**

   * Target’s names are preserved.
   * Functor-introduced disjoint declarations are collision-renamed using `FunctorName_...`.

Add a new section “Transform restrictions (Phase 2)”:

* `mod_transform` does not rewrite modalities and does not change `mod_eq`.
* Witness must be a generator with:

  * exactly one type variable
  * one input port and one output port
  * types `μ(A) -> ν(A)` as described
* No automatic coercion insertion yet; transforms are resources, not definitional equalities.

---

## Summary of required file touchpoints (Phases 0–2)

### Phase 0

* `src/Strat/Poly/Kernel.hs` (new)
* selective import updates in frontend/DSL

### Phase 1

* `src/Strat/DSL/AST.hs`
* `src/Strat/DSL/Parse.hs`
* `src/Strat/DSL/Elab.hs`
* `src/Strat/Frontend/Env.hs`
* `src/Strat/Poly/Pushout.hs` (new apply pushout + correct merge/rename)
* delete `src/Strat/DSL/Template.hs`
* tests: replace `test/Test/DSL/Templates.hs` with functor tests
* examples + `package.yaml` data-files adjustments

### Phase 2

* `src/Strat/Poly/ModeTheory.hs`
* `src/Strat/Poly/DSL/AST.hs`
* `src/Strat/DSL/Parse.hs` (poly items parser)
* `src/Strat/Poly/DSL/Elab.hs`
* `src/Strat/Poly/Pushout.hs` (merge/rename transforms)
* tests: add `ModeTransforms` coverage, update `mkModes` helper
* optional stdlib update: `stdlib/schema.adjunction.llang`

---

## Implementation “gotchas” to prevent avoidable churn

1. **Do not leak internal names** (especially underscore-prefixed) into user-visible doctrines.

   * Store functor bodies in `meFunctors` only.
2. **Fix `mergeDoctrine` + `renameDoctrine` before relying on apply**.

   * Otherwise actions/obligations/transforms will silently disappear or become invalid.
3. **Keep apply deterministic**.

   * Collision renaming must use stable freshening rules (no map-order dependence).
