# Canonical Doctrine Coverage

This project treats "canonical doctrine coverage" as an explicit list of named artifacts, not an implied claim from broad smoke tests.

## Canonical Targets

| Target | Runnable / Load Artifact | Primary Validating Tests |
| --- | --- | --- |
| Two-layer classification (`Ty` classifies `Tm`) | `examples/run/classification_resolution.ok.run.llang` (`run main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`two-layer classification target`), `test/Test/Poly/ClassificationResolution.hs` |
| Three-layer classification (`Kd -> Ty -> Tm`) | `examples/run/classification_layered_3level.ok.run.llang` (`run main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`three-layer classification target`), `test/Test/Poly/ClassificationResolution.hs` |
| Dependent doctrine elaboration/use | `examples/run/dependent/vec.run.llang` (`run main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`dependent doctrine target`), `test/Test/Poly/Dependent.hs` |
| Pushout doctrine composition | `examples/run/pushout/nat_bool_plus.run.llang` (`run main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`pushout doctrine target`), `test/Test/Poly/Pushout.hs` |
| Classified modalities / classifier-lift coherence | `examples/run/modes/adjunction_real.run.llang` (`run triangle_left`) | `test/Test/Frontend/CanonicalCoverage.hs` (`classified modality target`), `test/Test/Poly/ModeTheory.hs`, `test/Test/Poly/ModeTransforms.hs` |
| Effects composition via functor/apply | `examples/run/effects/combined_with_handler.run.llang` (`run main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`effects composition target`), `test/Test/Frontend/StdlibIntegration.hs` |
| Foliation + forget roundtrip behavior | `examples/run/foliation/basic_foliate.run.llang` (`run main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`foliation+forget target`), `test/Test/Frontend/Pipeline.hs` |
| Codegen pipeline behavior | `examples/run/codegen/simple_codegen.run.llang` (`run main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`codegen target`), `test/Test/Frontend/ExampleCodegen.hs` |
| Data macro doctrine path | `examples/run/data/list.run.llang` (`run main`) | `test/Test/Frontend/CanonicalCoverage.hs` (`data macro target`), `test/Test/Poly/DataMacro.hs` |
| Adjunction schema artifact elaboration | `stdlib/schema.adjunction.llang` | `test/Test/Frontend/CanonicalCoverage.hs` (`schema adjunction target`) |
| Monad schema artifact elaboration | `stdlib/schema.monad.llang` | `test/Test/Frontend/CanonicalCoverage.hs` (`schema monad target`) |

## Scope of Claim

- Coverage claims are limited to the targets listed above.
- General broad checks still exist:
  - `test/Test/Frontend/ExamplesSmoke.hs` (all non-`xfail` runnable examples),
  - `test/Test/Frontend/StdlibIntegration.hs` (all stdlib files elaborate),
  but those are treated as supplemental checks rather than the canonical-target claim source.
