# llang

Typed doctrine kernel with rewriting, modular doctrine composition, a DSL, and a small CLI.

See `SPEC.md` for the kernel semantics, `examples/README.md` for runnable examples, and `docs/CANONICAL_COVERAGE.md` for explicit canonical-target coverage artifacts.

Examples:
- JS codegen output:
  `stack run -- examples/run/codegen/logic_full_adder_codegen.run.llang --run main`
- SSA schedule debug view for the same example:
  `stack run -- examples/run/codegen/logic_full_adder_codegen.run.llang --run ssa`
- Write extracted `FileTree` artifacts to disk (only when `--output` is passed):
  `stack run -- examples/run/codegen/jsartifact_filetree_hello.run.llang --output`
