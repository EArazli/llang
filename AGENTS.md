## What this bundle clearly fixed (static review)

I cannot run the Haskell test suite in this environment (no GHC/stack/cabal available), so the review below is based on reading the code + the added tests in `test/`.

### 1. Substitution semantics are no longer “under-applied”

* `applySubstTy` in `src/Strat/Poly/UnifyTy.hs` is now a **cycle-safe chase** with a visited set.
* `normalizeSubst` and `composeSubst` are now present and used to keep substitutions closer to a normal form.
* There are direct tests for the intended behavior:

  * `test_applySubstChase` (a→b, b→C implies a→C)
  * `test_applySubstCycle` (cycle does not loop)
  * `test_normalizeSubst` (normalization composes chains)

This fixes the agent’s original report about “hang vs under-apply” without reintroducing divergence.

### 2. Box names are treated as metadata (as per the new spec)

* `diagramIsoEq` in `src/Strat/Poly/Graph.hs` now treats `PBox _ d1` and `PBox _ d2` as compatible regardless of the box name, while still requiring the **inner diagrams** to be isomorphic.
* Pattern matching also ignores box names: `payloadCompatible (PBox _ _)` is always `True` in `src/Strat/Poly/Match.hs` (box interior remains opaque to matching unless the pattern includes a box edge, which is consistent with the design).

There’s a targeted test: `test_boxNameIrrelevantIso` in `test/Test/Poly/Basic.hs`.

### 3. Doctrine validation is stricter in the right places

* `validateDoctrine` now rejects **duplicate tyvars** in generator declarations and in 2-cells:

  * `ensureDistinctTyVars` used in `checkGen` and `checkCell` in `src/Strat/Poly/Doctrine.hs`.
* There are tests: `test_duplicateGenTyVarsRejected`, `test_duplicateCellTyVarsRejected`.

This closes a real soundness hole (duplicate binders make template/substitution semantics ambiguous).

### 4. Pushout merging is now “by body” (α-equivalent), not “by name”

* `mergeCells` in `src/Strat/Poly/Pushout.hs` now:

  * compares cells by **(mode, tyvar-count, diagram-iso up to α-renaming of tyvars)**,
  * dedups on body,
  * errors only on class/orientation conflicts.
* `mergeGenTables` now accepts α-equivalent generator declarations, via `genDeclAlphaEq`.

There are tests:

* `test_pushoutDedupCellsByBody`
* `test_pushoutDedupGenDeclAlphaEq`

This addresses the agent’s “dedup only on (mode,name)” complaint and is a meaningful step toward theory-correct colimits.

### 5. Type-map templates are now general (explicit binders), not “constructor-with-distinct-vars only”

This is a correct/general move if you want the morphism layer to match “signature morphisms as term interpretations”.

Changes are consistent across:

* AST: `RawPolyTypeMap` includes `rpmtParams` (`src/Strat/Kernel/DSL/AST.hs`)
* parser: `type <SrcType>(a,b,...) @M -> <expr> @M;` (`src/Strat/Kernel/DSL/Parse.hs`)
* elaboration: arity checked, binder distinctness checked, RHS vars restricted (`src/Strat/Poly/DSL/Elab.hs`)

There are tests:

* `test_typeMapBinderMismatchRejected`
* `test_typeMapUnknownVarRejected`

And morphism checking supports parameter reordering, with a direct test:

* `test_typeMapReorder` in `test/Test/Poly/Morphism.hs`.

### 6. STLC “surface parity” moved in the right direction

You removed the hardcoded poly STLC surface and added a “legacy surface → core term → diagram” pipeline:

* `src/Strat/Poly/Surface/LegacyAdapter.hs`
* `polyrun` now supports `surface_syntax` and `core_doctrine` (`Parse.hs`, `RunSpec.hs`, `RunPoly.hs`)
* Example: `examples/poly/ccc_surface/stlc.runspec.llang` now declares:

  * `surface STLC;`
  * `surface_syntax STLC_Syntax;`
  * `core_doctrine CCC;`

This is the right structural decision if you want “legacy surface system” to be reusable as a front-end while keeping polygraphs as the kernel.

### 7. CCC equation port has executable-style tests

`test/Test/Poly/CCC.hs` checks that `beta` and `beta_app` reduce as expected under the chosen rewrite policy. That’s the right kind of parity test: it verifies operational consequences, not just textual similarity.

---



## Bottom line

Relative to the agent’s original ambiguity list, this bundle resolves most foundational issues (substitution chasing, α-invariance for box names, dedup-by-body in pushouts, general type templates, and a path toward surface parity via a legacy adapter).

The remaining high-impact correctness hole is **pushout + parameter permutation**: accepted by the spec, accepted by validation, but not implemented, and it can break either:

* the ability to compute pushouts in cases that should work, or
* the intended commutativity property.

Fixing that should be your next move, with the concrete regression test described above.
