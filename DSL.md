# 1) Proposed architecture

## 1.1 Entities (all file-defined)

You will have three “modules” the user can define (in `.llang` files):

1. **Doctrine** (already implemented)

   * Your existing `doctrine ... where { ... }` and `doctrine X = Expr;`
   * Elaborates to `Presentation` via `elabDocExpr` (existing).

2. **Syntax** (new)

   * Defines a *notation-driven* bidirectional syntax for **surface terms**.
   * Compiles to:

     * `parse : Text -> Either Text CombTerm` (or directly `Term`, but use `CombTerm` first)
     * `print : Term -> Text` (canonical)
   * “Elaboration” is, initially, just: parse → `CombTerm` → existing `elaborate` into typed kernel `Term`.
   * Later extension: syntax-defined macros / elaboration beyond op application.

3. **Model** (new)

   * Defines an interpretation for operations into runtime `Value`.
   * Compiles to your existing `Strat.Backend.Model`.

Separately, you add a **Run block** (new) that selects:

* a doctrine (expression or name),
* a syntax,
* a model,
* rewrite policy and fuel,
* a list of `open` namespaces for unqualified name resolution,
  and then the **rest of the file** is the expression to run.

This makes the system “file-driven” rather than “CLI-driven”.

---

# 2) The syntax DSL (parser/printer/elaboration)

## 2.1 Scope: what you can realistically support now

### Supported now (Syntax v1)

* Atoms: `e`, `Z`, `S`, `id`, …
* Function-call fallback: `f(x,y,z)` with commas and parentheses.
* Prefix operators: `-x`, `k x` or `k(x)` depending on chosen token.
* Infix operators: `x + y`, `x * y`, with precedence + associativity.
* Parentheses grouping.
* Optional variable prefix (for pattern vars): `?x`.

This covers your current use-cases (monoid, peano, category core, SKI application if you want `t u` later).

### Not supported yet (Syntax v2+)

* Binding syntax (lambda, let, pattern binders) *as user-defined*.
* Implicit arguments / type-directed argument insertion.
* Arbitrary CFG grammars with ambiguity resolution and multi-valued printing.

You can still keep the current hardcoded `LangLambda` temporarily, but the v1 goal is to eliminate the hardcoded combinator parser/printer.

## 2.2 SyntaxSpec as an abstract object

Define a syntax specification as a small AST that does *not* commit to Megaparsec vs distributors, etc.

Core design:

* `SyntaxSpec` contains:

  * parse operators (notation rules)
  * print operators (a subset; canonical printing)
  * a few global options:

    * allow function-call parsing
    * allow qualified identifiers `A.B.C`
    * var prefix string, default `?`

### “Instantiation” against a doctrine

A `SyntaxSpec` is independent of a doctrine, but **to run a program** you instantiate it against a `Presentation` + a list of `open` namespaces:

`instantiateSyntax :: Presentation -> [Text] -> SyntaxSpec -> Either Text SyntaxInstance`

Instantiation:

* resolves each op name used in the spec (e.g. `m`) to an actual `OpName` in `presSig`

  * resolution: exact match first, else try `ns <> "." <> name` for each `open ns`
* checks arity constraints:

  * atom must refer to arity 0 op
  * prefix/postfix must refer to arity 1 op
  * infix must refer to arity 2 op
* produces:

  * a parser yielding `CombTerm` where `COp` names are **fully-qualified resolved names** (so elaboration doesn’t need “qualifyCombTerm hacks”)
  * a printer mapping fully-qualified `OpName` back to canonical surface tokens

This is the key to “syntax independent from doctrine but actually runnable”.

## 2.3 Printer correctness contract (what you can promise)

For a `SyntaxInstance`:

* Printing is **canonical**: every kernel term prints to a single string.
* Parsing may be larger than printing (if you add parse-only sugar).
* You can enforce a useful round-trip property:

> For all kernel terms `t` in the image of elaboration,
> `parse(print(t))` succeeds and elaborates to a term α-equal to `t`.

You do **not** try to preserve original formatting/comments. This is canonical printing, not concrete syntax reification.

---

# 3) The model DSL (backend/models)

## 3.1 Scope (Model v1)

A model definition is a set of equations giving a semantics for each op name in a small total expression language.

It is **not**:

* a general-purpose programming language
* a categorical semantics engine
* an external code runner

It is:

* enough for Nat → Int, Monoid → String, SKI → symbolic, etc.

## 3.2 ModelSpec instantiation

As with syntax, `ModelSpec` is independent of doctrine but instantiated against `(Presentation, open namespaces)` so op names resolve uniquely to actual `OpName`.

`instantiateModel :: Presentation -> [Text] -> ModelSpec -> Either Text Model`

* resolve op names exactly / via `open`
* check arity matches the number of parameters in the model clause
* compile RHS expressions to `Env -> Either RuntimeError Value`

### Expression language (suggested minimal set)

* Literals: int, string, bool
* Variables: clause parameters
* List: `[e1, e2, ...]`
* Builtins:

  * `+`, `*` on Int
  * `++` on String
  * `==` on Int/String/Bool (optional)
  * `if cond then a else b` (optional but very useful)
* A default behavior:

  * `default = symbolic;` (fallback to `VAtom/VList` behavior)
  * or `default = error "msg";`

You can typecheck this DSL (recommended but optional initially). At minimum, runtime errors should be explicit and informative.

---

# 4) File-based “program” execution

## 4.1 A run block + rest-of-file expression

Add a top-level construct:

```llang
import "./monoid.llang";
import "./monoid.syntax.llang";
import "./monoid.models.llang";

run where {
  doctrine Combined;        # or doctrine (Base@C) & (Ext@C);
  open C;                   # enables writing e,m,k instead of C.e,C.m,C.k

  syntax MonoidSyntax;
  model  StringMonoid;

  policy UseOnlyComputationalLR;
  fuel 50;

  # optional outputs:
  show normalized;
  show value;
  show cat;
}
---
k(m(e, e))
```

Key parsing trick: everything after `---` is treated as raw text and is parsed by the chosen syntax instance (not by the `.llang` meta-parser).

This exactly matches your “rest of file is one expression” requirement while keeping the module language parseable.

## 4.2 Import resolution (minimal now)

* `import "<relative-path>";` only.
* Imports are resolved relative to the directory of the importing file.
* Loader:

  * detects cycles
  * merges environments (doctrines/syntaxes/models)
  * duplicate names are errors (for now)

Later extension: modules/namespacing for imports.

---

# 5) Pushback / adjustments (important)

## 5.1 Full user-defined elaboration (beyond op application) is not cheap

If by “elaboration” you mean “define lambda with binding and compile it into CCC operations”, that is *not* achievable with only the notation table DSL.

You have two realistic future paths:

1. **Macro elaboration over a first-order surface AST** (pattern→term rewriting on `CombTerm`)

   * good for syntactic sugar, numerals, desugaring, “let” expansion
   * not good for real binding constructs (free variable analysis, capture-avoidance)

2. **Second-order/binder-aware elaboration** (Fiore/Plotkin/Turi/Fiore/Mahmoud style)

   * correct, elegant, but it’s essentially implementing layer S properly
   * that’s a larger project than “parsers and printers”

So: implement Syntax v1 now (notations, invertible parse/print), and keep an explicit “Syntax v2: binder-aware syntax & elaboration” milestone.

## 5.2 “Concat backend” in the Conal sense is a separate milestone

Your current `CatExpr` is “op application AST”, not a categorical language with composition/products/etc.

You can still demonstrate semantics-swapping today via different `model`s.
True compiling-to-categories (as a target language and model) is a bigger extension and belongs after:

* the syntax/model DSLs stabilize
* the run-file story stabilizes
* the kernel coherence story stabilizes

---

# 6) Detailed implementation instructions for the agent

Below is a staged plan that minimizes breakage and keeps tests passing progressively.

````markdown
# Agent plan: user-defined syntax + user-defined models + run-file programs

## Stage 0 — Refactor boundaries (no functionality change)
Goal: introduce a front-end “module environment” type and loader pipeline without changing kernel semantics.

1. Add `Strat.Frontend.Env`:
   ```hs
   data ModuleEnv = ModuleEnv
     { meDoctrines :: Map Text DocExpr
     , meSyntaxes  :: Map Text SyntaxSpec
     , meModels    :: Map Text ModelSpec
     , meRun       :: Maybe RunSpec   -- only allowed in the main file
     }
   emptyEnv :: ModuleEnv
   mergeEnv :: ModuleEnv -> ModuleEnv -> Either Text ModuleEnv  -- reject duplicates
````

2. Keep existing `Strat.Kernel.DSL.*` intact for now, but plan to extend it in Stage 1.

   * Do NOT delete `loadDoctrines` yet; keep CLI/tests stable.

3. Add a small helper `NameResolution` module:

   ```hs
   resolveOpText :: Signature -> [Text] -> Text -> Either Text OpName
   -- tries exact, then each open ns as prefix
   ```

## Stage 1 — Extend the file DSL to include syntax/model/run/import

Goal: parse one file into `ModuleEnv` including doctrines/syntaxes/models/run.

1. Extend `Strat.Kernel.DSL.AST`:

   * Add:

     * `RawSyntaxDecl`
     * `RawModelDecl`
     * `RawRunDecl`
     * `RawImportDecl`
   * Extend `RawDecl` with:

     * `DeclImport FilePath`
     * `DeclSyntaxWhere Text [RawSyntaxItem]`
     * `DeclModelWhere Text [RawModelItem]`
     * `DeclRun RawRun`
       Keep existing doctrine decls unchanged.

2. Extend `Strat.Kernel.DSL.Parse`:

   * Parse:

     * `import "path";`
     * `syntax NAME where { ... }`
     * `model NAME where { ... }`
     * `run where { ... } --- <takeRest>`
       *Important:* after `---`, use `takeRest` to capture expression text verbatim until EOF.

3. Extend `Strat.Kernel.DSL.Elab` (or create `Strat.Frontend.DSL.Elab`):

   * `elabRawFile :: RawFile -> Either Text ModuleEnv`
   * Doctrine elaboration stays as-is.
   * For now:

     * syntax/model elaboration just store the raw specs (as SyntaxSpec/ModelSpec) without instantiation.

4. Write tests:

   * `Test/Kernel/DSL` add parsing tests for syntax/model/run/import.

## Stage 2 — SyntaxSpec v1 (notations) + instantiateSyntax

Goal: remove hardcoded combinator parser/printer from CLI path.

1. Define `Strat.Syntax.Spec`:

   ```hs
   data Assoc = LeftAssoc | RightAssoc | NonAssoc
   data Notation
     = NAtom    { nTok :: Text, nOp :: Text, nPrint :: Bool }
     | NPrefix  { nPrec :: Int, nTok :: Text, nOp :: Text, nPrint :: Bool }
     | NPostfix { nPrec :: Int, nTok :: Text, nOp :: Text, nPrint :: Bool }
     | NInfix   { nAssoc :: Assoc, nPrec :: Int, nTok :: Text, nOp :: Text, nPrint :: Bool }

   data SyntaxSpec = SyntaxSpec
     { ssName        :: Text
     , ssNotations   :: [Notation]
     , ssAllowCall   :: Bool
     , ssVarPrefix   :: Text  -- default "?"
     , ssAllowQualId :: Bool  -- default True
     }

   data SyntaxInstance = SyntaxInstance
     { siParse :: Text -> Either Text CombTerm
     , siPrint :: Term -> Text
     }
   ```

2. Implement `instantiateSyntax :: Presentation -> [Text] -> SyntaxSpec -> Either Text SyntaxInstance`
   Steps:

   * Resolve each `nOp` to a concrete `OpName` using `resolveOpText`.
   * Check arity constraints vs the doctrine signature.
   * Build an expression parser using Megaparsec:

     * term atoms: parens, varprefix, function-call, bare ident
     * operator table from notations:

       * NInfix → InfixL/InfixR/InfixN
       * NPrefix → Prefix
       * NPostfix → Postfix
     * Each operator constructs `COp (renderOpName resolvedOp) [..]` with fully qualified name.
   * Build a canonical printer:

     * Use a precedence-based pretty printer over kernel `Term`.
     * Recognize operators by `OpName` and arity.
     * Print only using `nPrint=True` notations; otherwise fallback `Op(args)`.

   Important: printing operates on kernel `Term`, not `CombTerm`.

   * For printing, pattern-match on `termNode` and use `OpName` lookups.

3. Replace CLI’s `parseSurface` path for comb terms:

   * Deprecate `Strat.Surface.Combinator.Parse.parseCombTerm` in the main pipeline.
   * Keep it for tests or until Stage 3 completes, but run-file mode should use SyntaxInstance.

4. Tests:

   * Add `Test/Syntax.hs`:

     * instantiate a syntax against `examples/monoid.llang Combined` and check:

       * `parse "k(m(e,e))"` elaborates and normalizes to `e`
     * roundtrip property on printed normalized forms:

       * `parse (print norm)` yields same term after elaboration

## Stage 3 — ModelSpec v1 + instantiateModel

Goal: user-defined models replace `Strat.Backend.Models`.

1. Define `Strat.Model.Spec`:

   ```hs
   data ModelSpec = ModelSpec
     { msName    :: Text
     , msClauses :: [OpClause]
     , msDefault :: DefaultBehavior
     }

   data OpClause = OpClause
     { ocOp    :: Text
     , ocArgs  :: [Text]
     , ocExpr  :: MExpr
     }

   data DefaultBehavior
     = DefaultSymbolic
     | DefaultError Text

   data MExpr
     = MVar Text
     | MInt Int
     | MString Text
     | MBool Bool
     | MList [MExpr]
     | MIf MExpr MExpr MExpr
     | MBinOp Text MExpr MExpr   -- "+", "*", "++", "=="
   ```

2. Parse model DSL in `Strat.Kernel.DSL.Parse`:
   Example syntax:

   ```
   model NatModel where {
     default = error "unknown op";
     op Z() = 0;
     op S(n) = n + 1;
     op add(x,y) = x + y;
   }
   ```

   (Allow either `op Z = 0;` or `op Z() = 0;` but normalize internally.)

3. Implement `instantiateModel :: Presentation -> [Text] -> ModelSpec -> Either Text Model`

   * Resolve `ocOp` to `OpName`.
   * Check arity matches `length ocArgs`.
   * Compile `MExpr` to `Env -> Either RuntimeError Value`.
   * Implement builtins with runtime checks and informative errors.
   * DefaultSymbolic should behave exactly like existing `symbolicModel`.

4. Tests:

   * `Test/Model.hs`:

     * define NatModel in a test `.llang` fragment, instantiate, evaluate `mul(S(S(Z)), add(S(Z), S(S(Z))))` to `VInt 6`.

## Stage 4 — Program runner: imports + run block + expression

Goal: `stack exec llang-exe -- file.llang` runs without extra CLI args if the file has `run`.

1. Implement `Strat.Frontend.Loader`:

   ```hs
   loadModule :: FilePath -> IO (Either Text ModuleEnv)
   ```

   * Parse file to RawFile, extract imports.
   * Recursively load imports (relative paths).
   * Merge all envs (reject duplicate names).
   * Enforce: only the *main* file may contain `run`; imported files must not.

2. Implement `Strat.Frontend.Run`:

   ```hs
   runFile :: FilePath -> IO (Either Text RunResult)
   data RunResult = ...
   ```

   Pipeline:

   * Load env
   * Read `RunSpec` (doctrine expr/name, syntax name, model name, open list, fuel, policy, show flags, exprText)
   * Elaborate doctrine expr → Presentation
   * compileRewriteSystem
   * instantiateSyntax(pres, open, syntaxSpec)
   * parse exprText using syntax parser → CombTerm
   * elaborate(defaultInstance pres with exact op names) → Term
   * normalize
   * compileTerm (existing)
   * instantiateModel(pres, open, modelSpec) → Model
   * evalTerm
   * render outputs (prefer printing normalized term using syntax printer)

3. Update `Strat.CLI`:

   * Add a new entry path:

     * if args are a single file path:

       * try run-file mode; if there is no `run` block, fall back to old positional mode error/behavior
   * Or add a subcommand `run FILE`.

4. Update tests:

   * Add a new program file under `examples/monoid.run.llang` (or reuse `.llang`):

     * imports monoid + syntax + model
     * run block + expression `k(m(e,e))`
   * `Test/CLI` should call the new runner and check normalized/value outputs.

## Stage 5 — Standard library migration (remove hardcoded parsers/models)

Goal: nothing is hardcoded; builtins live in files.

1. Create `stdlib/` file(s) shipped with package data:

   * `stdlib/syntax.llang` defines `syntax CombDefault where { ... }`
   * `stdlib/models.llang` defines `model Symbolic where { default = symbolic; }`
2. Ensure examples import stdlib instead of relying on compiled-in models.
3. Keep a minimal internal fallback symbolic model only for boot/debug, but do not use it in main paths.

## Future extension points (do NOT implement now)

* Syntax v2: binder-aware syntax + elaboration (Fiore/Mahmoud style)
* Syntax backend swap: interpret SyntaxSpec into distributors `Grammar` for alternative parse/print semantics
* Model v2: semantics over a categorical target language (true concat-style)

````

---

# 7) Concrete example files to add immediately (to validate the new system)

### `examples/monoid.syntax.llang`
```llang
syntax MonoidSyntax where {
  # canonical printing
  print atom "e" = e;
  print infixl 6 "*" = m;
  print prefix 9 "k" = k;

  # parsing conveniences
  parse atom "ε" = e;

  allow call;
  varprefix "?";
}
````

### `examples/monoid.models.llang`

```llang
model StringMonoid where {
  default = error "unknown op";

  op e() = "";
  op m(x,y) = x ++ y;
  op k(x) = x;

  # optional: allow atoms x,y as strings
  # If you want that, use default = symbolic and then special-case in printing,
  # or add explicit op clauses for x() and y().
}
```

### `examples/monoid.run.llang`

```llang
import "./monoid.llang";
import "./monoid.syntax.llang";
import "./monoid.models.llang";

run where {
  doctrine Combined;
  open C;

  syntax MonoidSyntax;
  model StringMonoid;

  policy UseOnlyComputationalLR;
  fuel 50;

  show normalized;
  show value;
  show cat;
}
---
k(e * e)
```

Expected:

* normalized prints as `e`
* value prints as `""` (or `VString ""` depending on rendering mode)

