Runnable examples

Files under `examples/run/**` are runnable entrypoints. They may import shared
modules from `examples/lib/**`.

`examples/run/xfail/**` are runnable but intentionally fail with checker/surface
errors.

From the repo root, run any example with:

  stack run -- <path-to-run-file>

If you have the `llang` executable on your PATH, you can also run:

  llang <path-to-run-file>

Notes:
- Pipelines are explicit (`pipeline ...`) and runs bind a pipeline via
  `run ... using ... where { source ... }`.
- Some files define multiple `run` blocks. For those, pass `--run <name>`:
  `stack run -- <path-to-run-file> --run <name>`.
- To materialize `FileTree` artifacts to disk, pass `--output`; otherwise the
  CLI only prints the extracted file listing/content.
