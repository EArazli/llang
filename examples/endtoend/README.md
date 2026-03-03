End-to-end examples

This directory contains self-contained userland examples that do not import
`examples/lib/**` or `stdlib/**`.

## Plus Calculator (integers + `+`)

`calc_plus_int.run.llang` emits a terminal calculator as `calc.mjs`.
The generated JavaScript uses only Node built-ins.

This example is fully userland and staged:

- `Calc` doctrine: a small calculator IR (`Expr`, `Step`, `Comp`, `Program`)
- `CalcSurface` surface: grouped `Comp`/`Step`/`Expr` forms in one grammar (`bind`, `read`, `run`, plus `let`/`if`/`for`/`set`/`print`)
- `lowerCalc : Calc -> JSAst`: lowering to a JS-oriented AST doctrine
- `PrettyArtifact` doctrine: reusable Doc combinators (`prefix`, `suffix`, `joinWith`, `blockWithHead`, `call1`, `infix`, `decl`, `assign`, `stmtTerm`) with computational rules
- `emitJS : JSAst -> PrettyArtifact`: JS emission using the helper combinators
- source doctrine/surface exposes monadic calculator composition (`bind`, `ret`, `read`, `run`); codegen lowers this via lambda application + block-IIFE to plain JS (no required JS monad runtime)
- runtime helper lambdas (`isEmpty`, `isDigitChar`, `isWhitespace`) are assembled via user-space `JSAst` helper builders (`varLenEqZero`, `varBetweenStr`, `varCharCodeAt0LteInt`, `constLambda1`), not hard-coded JS text
- pipeline: `normalize(topmost) -> apply lowerCalc -> normalize(computational_lr) -> apply emitJS -> apply erasePretty -> extract FileTree`

Build (preview extracted file content):

  stack run -- examples/endtoend/calc_plus_int.run.llang

Build and write output to disk:

  stack run -- examples/endtoend/calc_plus_int.run.llang --output

Run generated calculator:

  node examples/endtoend/out/calc.mjs <<< "41 + 1 + 8"

Expected output:

  50
