# Canonical Doctrine Coverage

This project treats "canonical doctrine coverage" as an explicit list of named artifacts, not an implied claim from broad smoke tests.

## Canonical Targets

| Target | Executable / Load Artifact | Primary Validating Tests |
| --- | --- | --- |
| Build-native module/doc emission | `examples/build/hello_doc.llang` (`build main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`hello doc module target`), `test/Test/Frontend/Builds.hs` |
| Module linking and bundling | `examples/build/bundle_docs.llang` (`build main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`bundle doc target`), `test/Test/Frontend/Builds.hs` |
| Doctrine-backed module data packages | `examples/build/doctrine_data_package.llang` (`build main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`module data package target`), `test/Test/Frontend/Builds.hs`, `test/Test/Frontend/ExamplesSmoke.hs` |
| Structured JS codegen | `examples/build/logic_full_adder_codegen.llang` (`build main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`logic codegen target`), `test/Test/Frontend/ExampleCodegen.hs` |
| Explicit sharing quotation behavior | `examples/build/explicit_sharing_js_codegen.llang` (`build main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`sharing quotation target`), `test/Test/Frontend/Pipeline.hs`, `test/Test/Frontend/ExampleCodegen.hs` |
| Type-changing AD build path | `examples/build/autodiff_times_sin.llang` (`build main`, `build core`) | `test/Test/Frontend/CanonicalCoverage.hs` (`autodiff js target`, `autodiff core target`), `test/Test/Frontend/ExampleCodegen.hs`, `test/Test/Poly/Morphism.hs` |
| Endomorphic AD quotation path | `examples/build/autodiff_times_sin_pair_core.llang` (`build share`) | `test/Test/Frontend/CanonicalCoverage.hs` (`pair autodiff share target`), `test/Test/Frontend/ExampleCodegen.hs` |
| Adjunction schema artifact elaboration | `stdlib/schema.adjunction.llang` | `test/Test/Frontend/CanonicalCoverage.hs` (`schema adjunction target`) |
| Monad schema artifact elaboration | `stdlib/schema.monad.llang` | `test/Test/Frontend/CanonicalCoverage.hs` (`schema monad target`) |

## Scope of Claim

- Coverage claims are limited to the targets listed above.
- General broad checks still exist:
  - `test/Test/Frontend/ExamplesSmoke.hs` (all build examples),
  - `test/Test/Frontend/StdlibIntegration.hs` (all stdlib files elaborate),
  but those are treated as supplemental checks rather than the canonical-target claim source.
