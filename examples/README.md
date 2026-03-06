Polygraph examples

This directory is split into libraries and runnable entrypoints:

- `examples/lib/**`: shared doctrines, morphisms, surfaces, templates. No `run` blocks.
- `examples/run/**`: runnable example files (usually wrappers that import `lib`).
- `examples/endtoend/**`: self-contained runnable pipelines built fully in userland.
  - `calc_plus_int.run.llang` (surface -> JS calculator)
  - `autodiff_times_sin.run.llang` (type-changing CCC forward AD morphism -> JS module)
- `examples/run/xfail/**`: runnable files that are expected to fail.

See `examples/run/README.md` for execution details.
For explicit canonical-target coverage mapping, see `docs/CANONICAL_COVERAGE.md`.

Quick index (non-exhaustive):

- `examples/run/algebra/`
  - `planar_monoid.run.llang`, `cart_monoid.run.llang`, `cat.run.llang`
  - `coherence_demo.run.llang`, `box_match.run.llang`, `ski.run.llang`
  - `loop_demo.run.llang`, `monoid_to_string.run.llang`, `subdiagram_match.run.llang`
  - `ccc.run.llang` (CCC beta-app normalization)
  - `mode_map_demo.run.llang`, `morphism_term.run.llang`, `peano.run.llang`
- `examples/run/dependent/`
  - `vec.run.llang`, `lambda_beta.run.llang`, `implicit_binder_index.run.llang`
  - `graded_monad.run.llang`
- `examples/run/terms/`
  - `term_ref.run.llang`, `cart_monoid.term.run.llang`, `stlc_bool.term.run.llang`
- `examples/run/surfaces/`
  - `cartesian_end_to_end.run.llang`
  - `planar_monoid.ssa.run.llang`
  - `implements_uses.run.llang`
- `examples/run/modes/`
  - `adjunction_real.run.llang`, `monad_instance.run.llang`, `for_gen_morphism_map.run.llang`
  - `lnl.counit.run.llang`, `lnl.unit.run.llang`
  - `staging.run.llang`, `staging_mode_map.run.llang`
  - `dual_discipline_term_surface.run.llang`, `quad_discipline_surface.run.llang`
- `examples/run/pushout/`
  - `pushout_basic.run.llang`, `comm_monoid.run.llang`
  - `nat_bool.run.llang`, `nat_bool_plus.run.llang`
- `examples/run/templates/` and `examples/run/effects/`
  - template instantiation + effects demos
- `examples/run/data/`
  - `list.run.llang` (data macro)
- `examples/run/doc/`
  - `hello_doc.run.llang` (`Doc` extraction)
- `examples/run/foliation/`
  - `basic_foliate.run.llang` (foliation + forget roundtrip)
- `examples/run/codegen/`
  - `simple_codegen.run.llang` (foliation + emission to `Doc`)
  - `logic_full_adder_codegen.run.llang` (JS-ish module emission + optional SSA)
- `examples/run/codegen/minifun/`
  - `concat2.run.llang` (MiniFun surface -> `Doc` emission)
- `examples/run/xfail/`
  - expected-fail checker/surface examples, including dependent index failures
  - includes `pushout_extend_confluence.fail.run.llang` (intentional confluence rejection)
