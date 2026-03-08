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
story while still lowering the quoted result through a small JS backend.

- `SmoothLam` is closed under differentiation by adding `Pair`, `mkPair`,
  `fst`, `snd`, `add`, `cos`, and `neg`
- `forwardAD : SmoothLam -> SmoothLam` is an actual endomorphism with
  `R -> Pair(R, R)` and primitive images expressed as composites in the same
  doctrine
- the source run is an open core term `dup ; (id * (id ; sin)) ; mul`, so after
  one AD pass the emitted JS is a lambda from a seeded pair input `p0` to
  `[value, derivative]`
- `main` runs:
  `apply forwardAD -> normalize -> quote into SmoothLam_Share -> apply lowerJS -> normalize -> apply emitJS -> normalize -> extract Doc`
- `main2` uses the exact same path, with the only semantic difference being a
  second `apply forwardAD` before normalization

Build the first-order JS module:

  stack run -- examples/endtoend/autodiff_times_sin_pair_core.run.llang --run main

Build the second-order JS module through the same backend:

  stack run -- examples/endtoend/autodiff_times_sin_pair_core.run.llang --run main2

Current status:

  This example now lands the userland sharing path directly in the Milestone 2
  presentation. The differentiated term is quoted into `SmoothLam_Share` with
  nested `let_*` / `returnRefs` structure, then lowered through an ordinary
  morphism `lowerJS : SmoothLam_Share -> PairJS`, rendered by an ordinary
  `emitJS : PairJS -> PairJSDoc`, and finally extracted with `extract Doc`.

  There is no language-level JS extractor in this path. The backend cleanup is
  userland too: `PairJS` carries the explicit expression/program structure, its
  local computational rules inline obviously safe return patterns and recover
  nearby pair destructuring from sibling `[0]` / `[1]` projections, and the
  final `PairJSDoc` stage renders the JS module through ordinary `Doc`
  combinators.

  So `main` and `main2` differ only by the extra `forwardAD` application in the
  pipeline. They share the same quoting, letgraph optimization, `PairJS`
  lowering, `PairJSDoc` rendering, and `Doc` extraction path.
