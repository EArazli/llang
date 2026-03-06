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

## Categorical Auto-Diff (`\x -> x * sin(x)`)

`autodiff_times_sin.run.llang` stages a tiny lambda/CCC fragment through
forward-mode AD and emits `times_sin.mjs`.

This example is fully userland and explicitly staged:

- `SmoothLam` doctrine: a cartesian/lambda fragment with `Arr`, `lam`, `app`,
  `dup`, `mul`, `sin`, beta, and a small packaging generator
- `forwardAD : SmoothLam -> DualLam`: a real type-changing morphism with
  `R -> Dual`, preserving `dup`/`lam`/`app` and mapping only smooth primitives
  (`mul`, `sin`) to differentiated ones (`dmul`, `dsin`)
- `emitJS : DualLam -> DualJS`: a separate backend morphism; the remaining
  rewrite rules are only for JavaScript rendering and module packaging
- the example now exercises real lambda application: the outer function applies
  an inner helper `\y -> y * sin(y)` to its argument, and beta reduction
  happens in the staged lambda fragment rather than in JavaScript
- the emitted artifact is now a reusable module with named `mulDual`/`sinDual`
  helpers and shared `dx`, instead of an inline residual blob plus top-level IO
- pipeline: `apply forwardAD -> apply emitJS -> normalize(computational_lr) -> extract FileTree`

Build (preview extracted file content):

  stack run -- examples/endtoend/autodiff_times_sin.run.llang

Build and write output to disk:

  stack run -- examples/endtoend/autodiff_times_sin.run.llang --output

Evaluate the generated module at `x = 1`:

  node --input-type=module -e 'import { timesSin } from "./examples/endtoend/out/times_sin.mjs"; console.log(JSON.stringify(timesSin(1), null, 2));'

Expected output:

  {
    "value": 0.8414709848078965,
    "derivative": 1.3817732906760363
  }
