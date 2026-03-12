End-to-end examples

This directory contains end-to-end userland examples. Most are self-contained.

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
- `DualCore` doctrine: a genuine differentiated target with `Dual`,
  low-level dual-number structure (`mkDual`, `splitDual`, `addR`, `mulR`,
  `sinR`, `cosR`), and differentiated primitives `dmul`/`dsin`
- `forwardAD : SmoothLam -> DualCore`: a real type-changing morphism with
  `R -> Dual`, preserving `dup`/`lam`/`app` and mapping smooth primitives
  into the differentiated core (`mul -> dmul`, `sin -> dsin`)
- `DualCore` itself carries the AD equations:
  normalizing after `forwardAD` expands `dmul` and `dsin` into explicit
  product-rule and chain-rule diagrams over the low-level dual-number core
- `emitJS : DualCore -> DualJS`: a separate backend morphism; JavaScript now
  only lowers the differentiated target IR and does not define the AD meaning
- the example now exercises real lambda application: the outer function applies
  an inner helper `\y -> y * sin(y)` to its argument, and beta reduction
  happens in the staged lambda fragment rather than in JavaScript
- the emitted artifact is now a reusable module with named `mulDual`/`sinDual`
  helpers and shared `dx`, instead of an inline residual blob plus top-level IO
- `main` pipeline: `apply forwardAD -> apply emitJS -> normalize(computational_lr) -> extract FileTree`
- `core` pipeline: `apply forwardAD -> normalize(computational_lr) -> extract diagram`

Build (preview extracted file content):

  stack run -- examples/endtoend/autodiff_times_sin.run.llang

Build and write output to disk:

  stack run -- examples/endtoend/autodiff_times_sin.run.llang --output

Inspect the differentiated categorical core before codegen:

  stack run -- examples/endtoend/autodiff_times_sin.run.llang --run core

Evaluate the generated module at `x = 1`:

  node --input-type=module -e 'import { timesSin } from "./examples/endtoend/out/times_sin.mjs"; console.log(JSON.stringify(timesSin(1), null, 2));'

Expected output:

  {
    "value": 0.8414709848078965,
    "derivative": 1.3817732906760363
  }

## Pair-Based Endomorphic AD Core

`autodiff_times_sin_pair_core.run.llang` isolates the pair-based endomorphic AD
story at the reflected quotation boundary.

- `SmoothLam` is closed under differentiation by adding `Pair`, `mkPair`,
  `fst`, `snd`, `add`, `cos`, and `neg`
- `forwardAD : SmoothLam -> SmoothLam` is an actual endomorphism with
  `R -> Pair(R, R)` and primitive images expressed as composites in the same
  doctrine
- the source run is an open core term `dup ; (id * (id ; sin)) ; mul`, so after
  one AD pass quotation targets a closed reflected `Prog` in the generated
  quotation doctrine, with `q_begin`, `q_*` binding steps, and `q_end`
- `main` runs:
  `apply forwardAD -> normalize -> quote using SharePair into SmoothLam_Q -> apply emitJS -> normalize -> extract Doc`
- `main2` uses the exact same path, with the only semantic difference being a
  second `apply forwardAD` before normalization
- `share` / `share2` keep the same quoted programs in reflected diagram form for
  debugging

Inspect the first-order shared JS output:

  stack run -- examples/endtoend/autodiff_times_sin_pair_core.run.llang --run main

Inspect the second-order shared JS output through the same path:

  stack run -- examples/endtoend/autodiff_times_sin_pair_core.run.llang --run main2

Inspect the first-order reflected quotation IR directly:

  stack run -- examples/endtoend/autodiff_times_sin_pair_core.run.llang --run share

Current status:

  So `main` and `main2` differ only by the extra `forwardAD` application in the
  pipeline. They share the same fragment, the same reflected quotation target,
  and the same fragment-relative quotation algorithm. `main` / `main2` lower
  that reflected IR through an ordinary userland JS backend, while `share` /
  `share2` expose the thin reflected IR with `Seq`, `Prog`, `Digit`, `RefId`,
  `RefIds`, `q_begin`, `q_*`, and `q_end` nodes.
