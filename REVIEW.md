# Review Findings (Implementation-Relevant Only)

This file keeps only issues that require code/spec work for the final end-state.
Plan-only wording cleanups are intentionally excluded.

## 1) Constructor derivation is not fully aligned with per-mode defeq engines (High)

Current `deriveCtorTables` still uses a TRS-forced fragment path during eligibility checks, even for modes declared `defeq nbe`.
It also treats defeq failures as non-eligibility (`False`) instead of surfacing errors.

Why this matters:
- ctor eligibility can differ from the actual definitional equality used later by the kernel.
- misconfigurations can be silently masked as missing constructors.

Required fix:
- make ctor eligibility use the same per-mode defeq fragment selection (TRS/NbE) as the rest of the kernel.
- stop swallowing eligibility defeq errors; return contextual errors.
- decouple NbE `Arr` validation from circular dependence on already-derived ctor tables.

Primary code locations:
- `src/Strat/Poly/Doctrine.hs` (`deriveCtorTables`, `validateNbeConfigForMode`)

## 2) Unclassified-mode policy is not explicit/finalized in validation (Medium)

Current behavior effectively allows unclassified modes to exist, but they do not get constructor vocabularies and fail later on constructor use.
This is workable but not an explicit policy guarantee.

Why this matters:
- behavior is under-specified and diagnostics can be later/less direct than needed.

Required fix (choose one and enforce):
- either require all modes to be classified, or
- keep unclassified modes but add explicit early validation rejection for object-constructor use in those modes.

Primary code locations:
- `src/Strat/Poly/Doctrine.hs` (validation path)
- `src/Strat/Poly/ObjClassifier.hs` (classifier fallback behavior)

## 3) Claimed “canonical doctrine” coverage is not concretely represented as named artifacts (Medium/Low)

Current regression suite is strong on properties and stdlib/exemplar loading, but explicit named doctrine artifacts corresponding to all claimed canonical targets are not clearly present.

Why this matters:
- completion claims can overstate what is concretely exercised.

Required fix:
- either add explicit runnable examples/tests for each claimed canonical doctrine target, or
- restate completion criteria as property-based coverage and link those concrete tests.

Primary code locations:
- `test/Test/Frontend/StdlibIntegration.hs`
- `test/Test/Frontend/ExamplesSmoke.hs`
- `examples/`, `stdlib/`

## 4) Generated-obligation undecided policy should be explicit in SPEC (Low, docs correctness)

Kernel behavior is strict: generated action/comprehension/BC obligation checks reject `undecided`.
This should be stated directly in spec text for generated obligations.

Required fix:
- add explicit normative statement to SPEC: generated obligations must be proved during doctrine elaboration; undecided is rejection.

Primary code locations:
- `src/Strat/Poly/DSL/Elab.hs`
- `SPEC.md`
