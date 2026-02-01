Polygraph examples

This directory is split into **libraries** and **runnable entrypoints**:

- `examples/lib/**`: shared doctrines, morphisms, models, surfaces, templates. **No `run` blocks.**
- `examples/run/**`: runnable example files (usually small wrappers that import `lib`).

See `examples/run/README.md` for how to execute the run files.

Quick index (non-exhaustive):

- `examples/run/algebra/`
  - `planar_monoid.run.llang`, `cart_monoid.run.llang`, `monoid.run.llang`
  - `hello_world.run.llang` (model-backed evaluation)
  - `coherence_demo.run.llang`, `loop_demo.run.llang`, `box_match.run.llang`
  - `cat.run.llang`, `ccc.run.llang`, `ski.run.llang`
  - `mode_map_demo.run.llang`, `morphism_term.llang`
- `examples/run/terms/`
  - `term_ref.run.llang`, `cart_monoid.term.run.llang`, `stlc_bool.term.run.llang`
- `examples/run/surfaces/`
  - `planar_monoid.ssa.run.llang`
  - `ccc_surface/*` (STLC surface runs)
  - `implements_uses.run.llang`
- `examples/run/pushout/`
  - `pushout_basic.run.llang`, `nat_bool.run.llang`, `nat_bool_plus.run.llang`
- `examples/run/templates/` and `examples/run/effects/`
  - template instantiation + effects macro demos
- `examples/run/data/`
  - `list.run.llang` (data macro)
- `examples/run/codegen/`
  - `compile_to_js.run.llang` (morphism-as-compilation to a string)
- `examples/run/runspec/`
  - `multi.llang` (multiple runs via `run_spec`)
