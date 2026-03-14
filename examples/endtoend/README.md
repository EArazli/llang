End-to-end examples

This directory contains the larger staged examples that either:

- point at canonical build-native files under `examples/build`, or
- keep a restored historic `.run.llang` path for a standalone migrated example.

Today:

- `autodiff_times_sin.run.llang` and `autodiff_times_sin_pair_core.run.llang`
  are thin `include` wrappers over the canonical build-native files.
- `calc_plus_int.run.llang` is a restored standalone build-native example that
  keeps its historic path here.

## Categorical Auto-Diff (`\x -> x * sin(x)`)

`examples/build/autodiff_times_sin.llang` stages a small lambda/CCC fragment through forward-mode AD and emits `times_sin.mjs`.

- `main` build:
  `project export prog -> apply forwardAD -> apply emitJS -> normalize -> emit via FileTree`
- `core` build:
  `project export prog -> apply forwardAD -> normalize`

Preview emitted output:

  `stack run -- examples/build/autodiff_times_sin.llang --build main`

Write the generated module to disk:

  `stack run -- examples/build/autodiff_times_sin.llang --build main --output`

Inspect the differentiated categorical core:

  `stack run -- examples/build/autodiff_times_sin.llang --build core`

## Pair-Based Endomorphic AD Core

`examples/build/autodiff_times_sin_pair_core.llang` isolates the pair-based endomorphic AD story at the reflected quotation boundary.

- `main` and `main2` lower the reflected quotation IR to shared JS after one or two `forwardAD` passes.
- `share` and `share2` expose the reflected quotation IR directly.

Inspect the first-order shared JS output:

  `stack run -- examples/build/autodiff_times_sin_pair_core.llang --build main`

Inspect the second-order shared JS output:

  `stack run -- examples/build/autodiff_times_sin_pair_core.llang --build main2`

Inspect the first-order reflected quotation IR:

  `stack run -- examples/build/autodiff_times_sin_pair_core.llang --build share`

## Calculator + Integer Coercion

`examples/endtoend/calc_plus_int.run.llang` is a larger standalone build-native
example at its historic path. It stages a small calculator language into JS and
emits `calc.mjs`.

Preview the emitted result:

  `stack run -- examples/endtoend/calc_plus_int.run.llang`

Write the generated module to disk:

  `stack run -- examples/endtoend/calc_plus_int.run.llang --output`
