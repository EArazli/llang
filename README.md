# llang

Typed doctrine kernel with rewriting, modular doctrine composition, a DSL, and a small CLI.

See `SPEC.md` for the kernel semantics and `examples/README.md` for runnable examples.

Examples:
- JS codegen output:
  `stack run -- examples/run/codegen/logic_full_adder_codegen.run.llang --run main`
- SSA schedule debug view for the same example:
  `stack run -- examples/run/codegen/logic_full_adder_codegen.run.llang --run ssa`
