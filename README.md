# llang

Typed doctrine kernel with rewriting, modular doctrine composition, a DSL, and a build-oriented CLI.

See `SPEC.md` for current semantics, `RESTRICTIONS.md` for deliberate implementation boundaries, `examples/README.md` for the current example set, and `docs/CANONICAL_COVERAGE.md` for explicit coverage targets.

Examples:
- JS codegen output:
  `stack run -- examples/build/logic_full_adder_codegen.llang --build main`
- Doctrine-backed module data package:
  `stack run -- examples/build/doctrine_data_package.llang --build main`
- Reflected quotation debug view for the same example:
  `stack run -- examples/build/logic_full_adder_codegen.llang --build share`
- Pair-based forward AD lowered to shared JS:
  `stack run -- examples/build/autodiff_times_sin_pair_core.llang --build main`
- The same pair-based example after two AD passes:
  `stack run -- examples/build/autodiff_times_sin_pair_core.llang --build main2`
- Inspect the reflected quotation IR directly:
  `stack run -- examples/build/autodiff_times_sin_pair_core.llang --build share`
- Write emitted `FileTree` artifacts to disk:
  `stack run -- examples/build/autodiff_times_sin.llang --build main --output`
