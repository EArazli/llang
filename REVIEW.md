# Review: Simplification / Unification Opportunities

This note is a targeted engineering review of the current Haskell codebase + DSL artifacts (not a critique of the semantics). It focuses on:

- simplification while retaining existing features,
- unifying/generalizing “the same idea in two places,” and
- opportunities to remove current restrictions (especially those called out in `RESTRICTIONS.md`) in a principled way.

---

## Easy, surefire things to do

1. **Deduplicate topological-sort / acyclicity code**
   - Today there are (at least) two near-identical Kahn-style implementations:
     - `src/Strat/Poly/Foliation.hs` (`topoOrder`)
     - `src/Strat/Frontend/Run.hs` (`topologicalEdges`)
   - Extract a shared helper (e.g. `Strat.Poly.GraphAlgo.topoEdges :: Diagram -> Either Text [Edge]`) and call it from both.
   - Side benefit: `ensureAcyclicIfRequired` and SSA evaluation/extraction share the same notion of “cycle.”

2. **Centralize `ModuleEnv` lookups (doctrine/morphism/pipeline/surface/derived)**
   - Duplicated helpers exist in multiple modules with slightly different error strings:
     - `src/Strat/Frontend/Compile.hs` (`lookupDoctrine`, `lookupSurface`, `lookupMorphism`)
     - `src/Strat/Frontend/Run.hs` (`lookupDoctrine`, `lookupMorphism`, `lookupPipeline`, `lookupDerivedDoctrine`)
     - `src/Strat/Frontend/Coerce.hs` (`lookupMorphism`)
     - `src/Strat/DSL/Elab.hs` (lookup helpers near the bottom)
   - Create a single module (e.g. `Strat.Frontend.Lookup`) and use it everywhere.
   - Result: fewer “almost the same” helpers, more uniform UX for errors.

3. **Unify “apply a morphism chain” logic**
   - There are multiple foldl-based chains with very similar “source mismatch” checks:
     - `src/Strat/Frontend/Compile.hs` (`applyMorphisms`)
     - `src/Strat/Frontend/Run.hs` (inline morphism application logic inside phases)
     - `src/Strat/Frontend/Coerce.hs` (`applyCoercionPath`)
   - Create one shared `applyMorphismChain` that returns `(Doctrine, Diagram)` plus a structured error that can be rendered by callers.

4. **Eliminate duplicate “dedupe ports” helpers**
   - `src/Strat/Poly/Foliation.hs` has a local `dedupePorts`.
   - `src/Strat/Poly/CriticalPairs.hs` defines another `dedupePorts`.
   - Replace both with `Strat.Util.List.dedupe` (already used in `src/Strat/Poly/Graph.hs`) or move a port-specific helper to a single place.

5. **Factor duplicated prelude doctrine definitions**
   - `src/Strat/Frontend/Prelude.hs` defines `docDoctrine` and `artifactDoctrine` with a lot of repeated structure (modes, attr sorts, `comp_*`, `empty/text/line/cat/indent`).
   - Extract a helper like `mkDocLikeDoctrine :: Text -> [GenDecl] -> Doctrine` (or parameterize the extra constructors + extra gens), then define both by configuration.

6. **Standardize name rendering utilities**
   - Repeated mini-renderers occur throughout (e.g. several `renderModeName (ModeName t) = t` definitions).
   - Put canonical renderers in one place (`Strat.Poly.ModeSyntax` / `Strat.Poly.ObjPretty` / a new `Strat.Poly.Render`) and use them everywhere.

7. **Use `Data.Graph` for small graph algorithms**
   - Custom implementations exist for:
     - classification order: `src/Strat/Poly/ModeTheory.hs` (`classificationOrder`)
     - coercion BFS: `src/Strat/Frontend/Coerce.hs` (`findUniqueCoercionPath`)
   - Replacing these with `Data.Graph`-based utilities is usually a net reduction in code and edge cases.

8. **Tighten the extraction pipeline surface area**
   - `ValueExtractorSpec.ExtractDoc { veStdout :: Bool }` is currently parsed/elaborated but ignored by execution:
     - parsed in `src/Strat/DSL/Parse.hs`, elaborated in `src/Strat/DSL/Elab.hs`, but not honored in `src/Strat/Frontend/Run.hs` (`extractValue`).
   - Either implement `veStdout` (e.g., suppress `ArtExtracted` stdout) or delete it from the DSL and types to remove dead configuration.

9. **Consolidate parser “prelude” combinators**
   - `sc/lexeme/symbol/keyword/ident` are implemented separately in:
     - `src/Strat/DSL/Parse.hs`
     - `src/Strat/Poly/DSL/Parse.hs`
     - `src/Strat/Poly/Surface/Parse.hs`
   - A shared parsing prelude (even if parameterized by comment style / ident rules) would reduce drift and make it easier to evolve syntax consistently.

10. **Remove or merge thin re-export modules**
   - There are tiny “API façade” modules like:
     - `src/Strat/Poly/GraphCanon.hs`
     - `src/Strat/Poly/DefEq.hs`
     - `src/Strat/Poly/Kernel.hs`
   - If backwards compatibility is not desired, folding these into the real implementation modules simplifies navigation and reduces the public surface area.

---

## Opportunities that need detailed work (design + implementation)

1. **Remove the “single `classifiedBy` edge per mode” restriction**
   - Spec/notes: `SPEC.md` + `RESTRICTIONS.md` mention the current limit; code is `mtClassifiedBy :: Map ModeName ClassificationDecl` in `src/Strat/Poly/ModeTheory.hs`.
   - Workable direction:
     - Make classification edges keyed (e.g. by `cdTag`) and choose them explicitly in surface syntax, or
     - Extend `Obj` to carry an explicit “code representation” tag so equality/normalization knows which classifier mode/universe to use.
   - Touch points:
     - `src/Strat/Poly/ModeTheory.hs`, `src/Strat/Poly/ObjClassifier.hs`
     - object equality + normalization: `src/Strat/Poly/DefEq.hs`, `src/Strat/Poly/ObjNormalize.hs`
     - constructor resolution: `src/Strat/Poly/Doctrine.hs` (`deriveCtorTables*`, eligibility checks)
   - Update canonical examples/tests involving classification (`docs/CANONICAL_COVERAGE.md` + `test/Test/Poly/ClassificationResolution.hs`).

2. **Make NbE primitive/operator selection configurable from the DSL**
   - Restriction called out explicitly in `RESTRICTIONS.md` (“primitive selection fixed”).
   - Implementation already has `NbeConfig` (`src/Strat/Poly/Term/NBE/Config.hs`), but the doctrine builder hardcodes `defaultNbeConfig` (`src/Strat/Poly/Doctrine.hs`, `mkDefFragments`).
   - Workable direction:
     - Extend `mode ... defeq nbe ...` syntax to optionally supply `lam/app/Arr/eta`,
     - Store config per mode (in `ModeInfo`, or separately in `Doctrine`), and
     - Thread it into `TypeTheory`/`DefFragmentNBE`.
   - Update tests under `test/Test/Poly/NBE.hs` and add at least one example with non-default names.

3. **Lift the “runs only allowed in the main file” restriction**
   - Current behavior: `src/Strat/Frontend/Loader.hs` rejects `runs` in non-main imports.
   - Workable direction:
     - Decide how imported runs are named (namespace prefix? re-export?) and how `--run` selection works when multiple files contribute runs.
     - Update `selectRun` (`src/Strat/Frontend/Run.hs`) and the loader’s `diffEnv`/merge strategy.
   - Tests to add/update:
     - a tiny two-file example where an imported module defines a run and the main module selects/aliases it.

4. **Remove the “canonical prefix” restriction on term metavariable inputs**
   - Restriction in `RESTRICTIONS.md`: `PTmMeta` inputs must match the prefix induced by `tmvScope`.
   - Current enforcement is in:
     - `src/Strat/Poly/TermExpr.hs` (`diagramGraphToTermExprUnchecked`, `validateTermGraph`)
     - `src/Strat/Poly/Term/NBE/Normalize.hs` (`checkMetaPrefix`)
   - Workable direction:
     - Represent explicit dependency on term-context indices (e.g., store `[Int]` or a small “scope map” on `TmVar`/`PTmMeta`) rather than encoding it via boundary prefixing.
     - Update conversions and normalizers to honor that explicit map.
   - This would simplify term graph construction (no need for `saturateUnusedPrefixInputs`) and make “context-sensitive normalization” failures rarer/more principled.

5. **Unify the poly diagram expression language and the surface template expression language**
   - The following ASTs are strongly parallel:
     - `src/Strat/Poly/DSL/AST.hs` (`RawDiagExpr`)
     - `src/Strat/Poly/Surface/Spec.hs` (`TemplateExpr`)
   - Workable direction:
     - Define a shared core “diagram expression” AST with optional holes/captures,
     - Make surface actions compile into that AST rather than a separate one.
   - Payoff:
     - fewer parsers/printers/elaborators doing the same work twice,
     - term refs/splice/binder args become uniform concepts across both frontends.

6. **Expand definitional normalization fragments beyond the current restrictions**
   - Both TRS and NbE normalization reject boxes/feedback/splices/attrs in definitional paths (see `RESTRICTIONS.md` and checks in `src/Strat/Poly/TermExpr.hs`, `src/Strat/Poly/Term/NBE/Normalize.hs`, `src/Strat/Poly/Rewrite.hs`).
   - Workable direction:
     - Decide which structural constructs should be definitional (vs. always computational),
     - Either desugar them away before entering defeq engines, or extend engines to interpret them.
   - This is large but high leverage: it removes several “cannot normalize/check due to unsupported fragment” errors that currently surface in surprising places.

7. **Make structural capabilities less ad-hoc in the surface elaborator**
   - Today surface dup/drop are capability-based and require explicit `implements` defaults (`RESTRICTIONS.md`, implementation in `src/Strat/Poly/Surface/Elab.hs` around `connectUses`).
   - Workable direction:
     - Encode “structural discipline” as explicit mode data (cartesian/affine/linear/…) and derive `dup/drop` when the discipline permits it, or
     - Allow per-surface local defaults for dup/drop rather than relying on global `implements` lookup.
   - This can make surface programs more portable across doctrines and reduce the “missing dup/drop capability” failure mode.

8. **Replace the “pending universe resolution” special cases with a more principled elaboration pass structure**
   - Current approach:
     - `deriveCtorTablesForElab` (`src/Strat/Poly/Doctrine.hs`) tolerates unresolved classifier modes and “pending universes” by building provisional constructor tables.
   - Workable direction:
     - Split doctrine elaboration into explicit passes:
       1) collect modes + modality graph,
       2) compute classifier dependency order on the declared graph (with stubs),
       3) elaborate universes/constructors with that environment,
       4) validate final doctrine normally.
   - Goal: fewer implicit heuristics (like “defer unknown constructor eligibility errors”) and clearer failure modes.

9. **Turn value extraction into a general “host semantics doctrine” path**
   - Current extraction is a bespoke evaluator for the prelude doctrines embedded in `src/Strat/Frontend/Run.hs` (`extractDoc`, `extractFileTree`, `evalArtifactDiagram`).
   - Workable direction:
     - Treat extraction as a compilation/morphism to a dedicated host-doctrine, then interpret the resulting normal form generically (constructor-driven), so the evaluator doesn’t need hardcoded generator names.
   - Benefits:
     - reduces special-casing (“Artifact allows Doc/FileTree”) and makes it easier to add new host-level extractors.

---

If you want, I can take one “easy” item (graph algo + env lookup dedupe is a good first one), implement it, and update tests/examples in the same PR-sized change.

