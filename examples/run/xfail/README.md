Expected-fail runnable examples

Files under `examples/run/xfail/**` are intentionally rejected by the checker or
surface discipline checks.

Run from repo root:

  stack run -- <path-to-fail-run-file>

A non-zero exit with the documented error is the expected behavior.

Current categories include:
- surface capability failures (dup/drop discipline)
- dependent term-index failures
- doctrine-level validation failures (e.g. confluence rejection)
