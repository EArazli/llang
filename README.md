# llang

Typed doctrine kernel with rewriting, modular doctrine composition, a DSL, and a small CLI.

See `SPEC.md` for the kernel semantics, `examples/README.md` for runnable examples, and `docs/CANONICAL_COVERAGE.md` for explicit canonical-target coverage artifacts.

Examples:
- JS codegen output:
  `stack run -- examples/run/codegen/logic_full_adder_codegen.run.llang --run main`
- Explicit sharing / letgraph debug view for the same example:
  `stack run -- examples/run/codegen/logic_full_adder_codegen.run.llang --run share`
- Pair-based forward AD lowered from the binder-style letgraph representation to a named, human-style JS export:
  `stack run -- examples/endtoend/autodiff_times_sin_pair_core.run.llang --run main`
- The same pair-based example, but with `forwardAD` applied twice through the same JS backend path:
  `stack run -- examples/endtoend/autodiff_times_sin_pair_core.run.llang --run main2`
- Write extracted `FileTree` artifacts to disk (only when `--output` is passed):
  `stack run -- examples/run/codegen/jsartifact_filetree_hello.run.llang --output`
