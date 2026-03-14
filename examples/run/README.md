Runnable legacy-path examples

Files under `examples/run/**` are restored entrypoints that now use the
build/module frontend. The old `run` construct is gone; these files keep the
historic paths while exposing ordinary `build` targets.

From the repo root, run any example with:

  `stack run -- <path-to-example>`

If a file defines multiple builds, pass `--build <name>`:

  `stack run -- <path-to-example> --build <name>`

To materialize `FileTree` output to disk, pass `--output`.
