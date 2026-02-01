Runnable examples

All files under `examples/run/**` are runnable entrypoints. They may import shared
modules from `examples/lib/**`.

From the repo root, run any example with:

  stack run -- <path-to-run-file>

If you have the `llang` executable on your PATH, you can also run:

  llang <path-to-run-file>

Notes:
- `examples/run/codegen/compile_to_js.run.llang` prints **JS source text** via a model.
  It does not execute JavaScript.
