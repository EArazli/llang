MiniFun JS codegen example

This example shows a tiny surface language (MiniFun) elaborated to ConsoleExpr,
compiled to `Doc`, and emitted as source text.

Run:
  stack run -- examples/run/codegen/minifun/concat2.run.llang

Expected output:
- a single line of emitted source text
- `print((nextLine() + nextLine()))`
- llang does not execute the emitted code
