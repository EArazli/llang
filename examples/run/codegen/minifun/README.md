MiniFun JS codegen example

This example shows a tiny surface language (MiniFun) elaborated to ConsoleExpr,
compiled to JSCode, and evaluated to a JS source string.

Run:
  stack run -- examples/run/codegen/minifun/concat2.run.llang

Expected output:
- a single value string containing JS source
- it reads two lines with nextLine() and prints their concatenation
- llang does not execute JS; it only emits source text
