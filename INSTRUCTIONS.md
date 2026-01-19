## 0. Goals and invariants

### What must become true after this change

1. **Interfaces are not a separate thing.**
   An “interface” is just a **doctrine** (a presentation) used as a requirement. The system should not treat them differently at the type level.

2. **A morphism/interpretation maps operations to terms, not merely to other operations.**
   This is the standard notion of a theory interpretation:

   * sort constructors ↦ sort constructors (for now; keep it name→name)
   * operations ↦ well-typed target **terms** (with parameters corresponding to the source op’s arity)
   * equations must be preserved (obligations)

3. **Requirements must be first-class and compositional.**

   * A surface can `requires` **multiple** interfaces (doctrines).
   * A run must provide **implementations** (morphisms) that satisfy those requirements.
   * If not provided explicitly, the system should attempt to resolve them deterministically (identity / declared default / unique candidate), and error on ambiguity.

4. **`ContextDiscipline` must be explicit (starting with `cartesian`).**
   Surfaces (and optionally SOGAT) must declare which context discipline they assume. Only `cartesian` is implemented now, but the code structure must isolate the assumption so that adding other disciplines later (“Option B”) is a local change.

5. **Run configuration must be reusable at module and term granularity.**

   * You can define named `run_spec`s in any module.
   * You can define multiple named `run`s (terms) in a single file.
   * A run can reuse a spec (`run … using …`) with local overrides.
   * Execution can select which run to execute (default `main`, or explicit selection).

### “Option B” (future) clarified

“Option B” = making contexts/binding/substitution **parametric** over a discipline (cartesian/linear/affine/…): the surface layer and any HOAS-to-GAT compilation should not hard-code cartesian structural rules. This change **does not implement** non-cartesian behavior; it makes the assumption explicit and isolates the boundary so adding another discipline won’t require re-plumbing the whole system.

---

## 1. Terminology (unified language)

* **Doctrine**: a `Presentation` (signature + equations).
* **Interface**: a doctrine used as a requirement.
* **Interpretation / Morphism** `M : I -> D`: maps I’s symbols into D’s language:

  * sort ctor map
  * op map (op ↦ term)
  * preserves equations (obligations)
* **Requirement**: `requires alias : InterfaceExpr;` attached to a surface (and later: models/run specs).
* **Implementation**: a morphism that discharges the obligations of an interface inside a target doctrine.
* **Run spec**: a reusable configuration block (doctrine/syntax/model/surface/…).
* **Run**: an executable term paired with a config (usually via a run spec).

---

## 2. User-facing DSL changes

This section defines the new/updated concrete syntax. Make this the single source of truth for parser+examples+tests.

### 2.1. Surface: multiple requirements + explicit context discipline

Inside `surface … where { … }` add:

* `context_discipline cartesian;`  **(required)**
* multiple `requires` are allowed:

  * `requires ccc : CCC_Bool;`
  * `requires mon : Monoid;`

Example:

```llang
surface STLC where {
  context_discipline cartesian;

  requires ccc : CCC_Bool;

  context_sort Ty;

  sort Term : (A:Ty) -> Type;

  op Lam : (A:Ty)(B:Ty)(t:Term(B) [x:Term(A)]) -> Term(Arr(A,B));
  op App : (A:Ty)(B:Ty)(f:Term(Arr(A,B)))(x:Term(A)) -> Term(B);

  -- context compilation stays explicit
  derive contexts using ccc and tyObj;

  define BoolTy : Ty := ccc.Bool;
  define True  : Term(BoolTy) := ccc.T;
  define False : Term(BoolTy) := ccc.F;
}
```

**Notes**

* `context_discipline` is “explicit knob”; only accepts `cartesian` now.
* `requires` remains as-is syntactically but now can appear multiple times.

### 2.2. Morphisms: op ↦ term

Replace the old “op ↦ op” mapping with “op ↦ term”, while retaining shorthand compatibility.

#### New op mapping forms

1. **General form (recommended):**

   ```llang
   op f(x,y,...) = <term using ?x, ?y, ...>;
   ```

2. **Shorthand renaming (backward compatible):**

   ```llang
   op f = g;
   ```

   Meaning: `f(x1,...,xn)` maps to `g(x1,...,xn)` (auto-applied to all args).

3. **Shorthand identity:**

   ```llang
   op f = f;
   ```

   Still valid.

#### Full morphism example with a nontrivial op→term mapping

```llang
doctrine Invol where {
  sort Obj;
  op f : (x:Obj) -> Obj;
  rule inv : (x:Obj) -> f(f(x)) -> x;
}

doctrine Invol2 where {
  sort Obj;
  op g : (x:Obj) -> Obj;
  rule inv : (x:Obj) -> g(g(x)) -> x;
}

morphism Double : Invol -> Invol2 where {
  sort Obj = Obj;

  -- nontrivial: f(x) ↦ g(g(x))
  op f(x) = g(g(?x));
}
```

### 2.3. Declared default implementations

Add a new top-level declaration that registers a default morphism to satisfy a requirement when running in a target doctrine:

```llang
implements <InterfaceExpr> for <TargetExpr> using <MorphismName>;
```

Example:

```llang
implements CCC_Bool for CCC using CCCIface;
```

This is not the morphism itself; it is a **choice of default** implementation among potentially many morphisms.

### 2.4. Reusable run specs and multiple named runs

#### Run spec declaration

```llang
run_spec <SpecName> where {
  doctrine <DocExpr>;        -- may be omitted if provided by run
  syntax <SyntaxName>;       -- optional
  model <ModelName>;         -- optional
  surface <SurfaceName>;     -- optional
  surface_syntax <SurfSyn>;  -- optional
  open <Name>;               -- repeatable
  policy <PolicyName>;       -- optional
  fuel <Int>;                -- optional
  show <Item>;               -- repeatable

  -- explicitly satisfy required aliases if needed:
  implements <alias> = <MorphismName>;  -- (accept `use` as backward compat if you want)
}
```

#### Run declaration (term-level)

```llang
run <RunName> using <SpecName> where { <overrides...> }
---
<program text (surface or core), uninterpreted by DSL parser>
---
```

* The second `---` terminator is required if more declarations follow.
* If the file ends immediately, EOF can implicitly terminate the last run for backward compatibility.

#### Selection semantics

* If a file defines a `run main ...`, that’s the default.
* Otherwise, if exactly one `run` exists, execute it.
* Otherwise error: “multiple runs; specify which run to execute”.

CLI must add a way to select (see §6.4).

---

## 3. Kernel changes: morphisms as op→term

This is the mathematical core of the change.

### 3.1. Data structure changes

#### Files to edit

* `src/Strat/Kernel/Morphism.hs`
* `src/Strat/Kernel/DSL/AST.hs`
* `src/Strat/Kernel/DSL/Parse.hs`
* `src/Strat/Kernel/DSL/Elab.hs`
* (recommended cleanup) create `src/Strat/Kernel/AlphaEq.hs` and delete duplicated alpha-eq code.

#### Introduce `OpInterp`

In `Strat.Kernel.Morphism`:

```haskell
data OpInterp = OpInterp
  { oiTele :: [Binder]  -- template vars (target-sorted)
  , oiRhs  :: Term      -- target term with free vars oiTele
  }
```

Update:

```haskell
data Morphism = Morphism
  { morSrc     :: Presentation
  , morTgt     :: Presentation
  , morSortMap :: Map SortName SortName
  , morOpMap   :: Map OpName OpInterp
  , morCheck   :: MorphismCheck
  }
```

**Invariant:** `oiRhs` must be well-typed in the target signature under context `oiTele`, and must have sort equal to the translated source op result sort.

### 3.2. Term translation semantics

Define:

* `applyMorphismSort :: Morphism -> Sort -> Sort`
* `applyMorphismTerm :: Morphism -> Term -> Term`

with behavior:

1. **Sort translation**

   * map sort ctor name via `morSortMap`
   * translate each index term via `applyMorphismTerm`

2. **Term translation**

   * variables: keep the same `Var` identity; translate its sort.
   * operation application `f(args)`:

     * lookup `OpInterp` for `f`
     * translate each arg recursively
     * substitute template vars `oiTele` with translated args in `oiRhs`

You need a helper:

```haskell
applyOpInterp :: OpInterp -> [Term] -> Term
```

Implementation detail:

* Build `subst :: Map Var Term` from `oiTele` vars to supplied args.
* `applySubstTerm subst oiRhs`

**Important:** choose template vars scopes so they cannot accidentally collide with variables in translated args (use a unique scope prefix based on morphism name + op name). Even though current substitution does not re-substitute into inserted terms, keeping scopes disjoint avoids fragile debugging later.

### 3.3. Morphism checking updates (obligations)

Update `checkMorphism`:

* **Sort mapping check** remains: ensures mapped sort constructor telescopes match target sort constructors (arity and binder sorts), up to α-equivalence.
* **Op mapping check** changes:

  * for each source op `f`, check `oiTele` length matches source arity.
  * check `oiTele` binder sorts equal translated source binder sorts (after correctly translating indices).
  * check `oiRhs` has sort equal translated source result sort.
* **Equation preservation** stays: apply morphism to both sides and check joinability under target rewrite system (policy+fuel).

### 3.4. Eliminating alpha-eq duplication (recommended)

Right now the repo duplicates `alphaEqSortCtor/alphaEqOpDecl` in multiple places and `Strat.Kernel.Morphism` imports a module that does not exist (`Strat.Kernel.AlphaEq`). Fix this while touching morphisms:

* Create `src/Strat/Kernel/AlphaEq.hs` exporting:

  * `alphaEqSort :: Sort -> Sort -> Bool`
  * `alphaEqSortCtor :: SortCtor -> SortCtor -> Bool`
  * `alphaEqOpDecl :: OpDecl -> OpDecl -> Bool`
* Move the canonical implementation from `Strat.Kernel.DoctrineExpr` into this module.
* Update imports in:

  * `Strat.Kernel.Morphism`
  * `Strat.Kernel.DoctrineExpr`
  * `Strat.Kernel.DSL.Elab`
* Delete local duplicates.

This reduces sprawl and prevents “two subtly different alpha-eq implementations”.

### 3.5. Building `morOpMap` in elaboration

This is the nontrivial engineering: elaborating op interpretations requires typing `oiRhs`, which requires knowing the translated sorts.

#### 3.5.1. AST changes for morphism items

In `src/Strat/Kernel/DSL/AST.hs`, replace:

```haskell
data RawMorphismItem
  = RMISort Text Text
  | RMIOp   Text Text
```

with:

```haskell
data RawMorphismItem
  = RMISort Text Text
  | RMIOp
      { rmiSrcOp  :: Text
      , rmiParams :: Maybe [Text]  -- names (no '?')
      , rmiRhs    :: RawTerm
      }
```

Rationale: binder names are erased in `OpDecl` (kernel binders don’t store names). To write RHS terms referencing parameters (`?x`), the morphism clause must supply the parameter names explicitly.

#### 3.5.2. Parser changes for morphism items

In `src/Strat/Kernel/DSL/Parse.hs`, update morphism op item parsing:

* Accept `op f = g;` (no params)
* Accept `op f(x,y,...) = <term>;`

Pseudo-grammar:

```
opItem :=
  "op" qualifiedIdent ( "(" ident ("," ident)* ")" )? "=" term ";"
```

Implementation:

* `params <- optional (parens (ident `sepBy` comma))`
* RHS uses existing `term` parser (`RawTerm`).

#### 3.5.3. Elaboration algorithm for op interps

In `src/Strat/Kernel/DSL/Elab.hs`, in `elabMorphismDecl`:

1. Resolve `morSrc` and `morTgt` presentations (already done).
2. Build sort map (existing logic).
3. **Build op interpretation plan**:

   * For each source op name `f` in `sigOps (presSig src)`:

     * if user supplied `RMIOp` for `f`, use it.
     * else default: RHS is `RApp <sameNameInTarget> []` (shorthand). Require target has an op of same resolved name.
4. **Dependency ordering (required for dependent indices)**:

   * Compute dependency graph `f -> g` if `g` appears in any **term indices inside sorts** of `f`’s telescope or result sort.

     * Traverse `OpDecl tele res`.
     * For each `Sort _ indices`, traverse each index `Term` collecting `TOp` names, and recursively collect ops inside each index’s `termSort` indices as well (deep).
   * Topologically sort; if cycle, error with the set of ops in the SCC.
   * This is the minimal structure needed so you can translate sorts that mention earlier ops like `Arr(A,B)` in `Tm(Arr(A,B))`.
5. **Elaborate each `OpInterp` in topo order**:

   * Let source decl be `OpDecl tele res`.
   * Determine parameter names:

     * If `rmiParams = Just names`, length must equal `length tele`, and names must be unique.
     * If `Nothing`:

       * Allow only if RHS contains **no variables** (`RVar`).
         If RHS contains any `RVar`, error: “op mapping for f uses variables; provide parameter list”.
       * Generate internal names like `x0..x(n-1)` (not user-visible; only to auto-apply shorthand).
   * Create fresh template vars and translated binder sorts **sequentially** to handle dependency on earlier binders:

     * Maintain `subst :: Map Var Term` mapping source binder vars to target template var terms.
     * For each binder `Binder v s` in source tele:

       1. Compute `s'0 = applyMorphismSortPartial sortMap opMapKnown s`
       2. Compute `s'  = applySubstSort subst s'0` (replace source vars by template vars)
       3. Fresh var `v'`
       4. Add binder `Binder v' s'` to `oiTele`
       5. Extend `subst` with `v -> mkVar s' v'`
     * Translate result sort similarly: `res' = applySubstSort subst (applyMorphismSortPartial … res)`
   * Prepare RHS raw term:

     * If RHS is `RApp g []` and arity is `n>0`, expand to `RApp g [RVar name1, …, RVar namen]`.
   * Elaborate RHS into a typed target `Term` using existing `elabTerm`:

     * `env = Map name_i -> (v'_i, s'_i)`
     * `rhsTerm <- elabTerm (presSig tgt) env rhsRaw`
     * Check `termSort rhsTerm == res'` (exact; if you want alpha-eq sorts, define and use it).
   * Insert `morOpMap[f] = OpInterp oiTele rhsTerm`
6. Construct `Morphism` and run `checkMorphism` with the chosen policy+fuel.

#### 3.5.4. Partial translation helpers

During topo-order elaboration, you only have a partial `opMapKnown`. Implement:

```haskell
applyMorphismTermPartial
  :: SortMap -> Map OpName OpInterp -> Term -> Either MorphismError Term
applyMorphismSortPartial
  :: SortMap -> Map OpName OpInterp -> Sort -> Either MorphismError Sort
```

If an index term uses an op not yet in `opMapKnown`, error with a cycle/missing dependency message. This keeps failure modes crisp.

---

## 4. Surface/Foundation changes: explicit `ContextDiscipline`

### 4.1. Data model changes

Files:

* `src/Strat/Surface2/Def.hs`
* `src/Strat/Kernel/DSL/AST.hs`
* `src/Strat/Kernel/DSL/Parse.hs`
* `src/Strat/Surface2/Elab.hs`
* Update all surface examples and surface tests.

Add in `Surface2.Def`:

```haskell
data ContextDiscipline
  = CtxCartesian
  deriving (Eq, Ord, Show)
```

Update `SurfaceDef`:

* Replace:

  * `sdRequires :: SurfaceRequire`
* With:

  * `sdRequires :: [SurfaceRequire]`
* Add:

  * `sdCtxDisc :: ContextDiscipline`

### 4.2. Surface DSL items

In `Kernel.DSL.AST` add a raw surface item:

```haskell
data RawSurfaceItem
  = RSContextDiscipline Text
  | RSRequires Text RawExpr
  | ...
```

In parser, add:

```llang
context_discipline cartesian;
```

Only accept the literal `cartesian` for now.

### 4.3. Elaboration

In `Surface2.Elab.elabSurfaceDecl`:

* Collect all `RSRequires`.

  * Error if none (interfaces are required for core compilation).
* Collect exactly one `RSContextDiscipline`.

  * Error if missing or repeated.
* Store in `SurfaceDef.sdCtxDisc`.

**No behavior change yet** beyond being explicit and validated.

### 4.4. Setting up Option B boundary (minimal but real)

Do **not** thread a new context representation everywhere yet. Instead:

* Identify all places that assume “cartesian list context” and annotate them with:

  * `-- TODO(ContextDiscipline): currently assumes cartesian contexts`
* Centralize creation of initial context in one place:

  * in `Frontend.Run.buildSurfaceGoal` or `Surface2.Engine`, add:

    ```haskell
    emptyCtxFor :: ContextDiscipline -> Ctx
    ```
  * For now: `emptyCtxFor CtxCartesian = emptyCtx` (current empty list).
* Similarly, add `extendCtxFor`, `lookupCtxFor` wrappers (even if trivial).
  This creates a single call boundary for later.

This is the “set the project up for option B” part: you have explicit discipline + a single choke point where context operations are chosen.

---

## 5. Requires/Implements with obligations

### 5.1. Multiple requirements in surfaces

Update every caller that assumes a single requirement:

* `Frontend.Run.buildMorphismEnv`
* `Frontend.Run.readbackCoreBool` (see §5.4)
* Any surface utility that references `sdRequires`

### 5.2. Add `implements … for … using …;` declaration

#### AST

In `Kernel.DSL.AST` add:

```haskell
data RawDecl
  = ...
  | DeclImplements RawImplementsDecl

data RawImplementsDecl = RawImplementsDecl
  { ridInterface :: RawExpr
  , ridTarget    :: RawExpr
  , ridMorphism  :: Text
  }
```

#### Parser

Add a top-level decl parser:

```llang
implements <expr> for <expr> using <Ident>;
```

#### Environment

In `Strat.Frontend.Env` extend `ModuleEnv` with a registry:

```haskell
meImplDefaults :: Map (Text, Text) Text
-- (ifacePresName, targetPresName) -> morphismName
```

Store by `presName` pairs, not by full presentations (no `Ord Presentation`).

#### Elaboration

In `Kernel.DSL.Elab.step`:

* resolve `ifacePres <- elabDocExpr ifaceExpr`
* resolve `tgtPres  <- elabDocExpr tgtExpr`
* lookup morphism by `ridMorphism` in `meMorphisms`
* check `morSrc == ifacePres` and `morTgt == tgtPres` (or compare by `presName` if full equality is too strict; prefer full).
* insert into `meImplDefaults`; error on duplicate key.

This is the explicit “implements” relation. The obligation is discharged because morphisms are already checked for equation preservation at declaration time.

### 5.3. Requirement resolution algorithm in runs

Replace the current single-requirement logic with:

For each `SurfaceRequire { srAlias, srPres }` required by the surface:

Resolve an implementation morphism `M : srPres -> runPres` as:

1. **Explicit** in run spec/run overrides:

   * `implements srAlias = MorphName;`
2. **Declared default implementation**:

   * if `meImplDefaults[(presName srPres, presName runPres)] = MorphName`, use it.
3. **Identity**:

   * if `presName srPres == presName runPres`, use identity morphism.
4. **Unique candidate morphism**:

   * search all morphisms in env where `morSrc == srPres` and `morTgt == runPres`.
   * if exactly one: use it.
   * if >1: error “ambiguous implementation for alias …; specify implements alias = … or declare implements … for … using …”
5. Otherwise error “missing implementation for alias … (requires …, target …)”.

This eliminates “sprawl” because most runs no longer need an explicit `use` line once defaults are declared.

### 5.4. Readback and core-eval updates for multiple requires

#### Core evaluation

In `Strat.Surface2.CoreEval.resolveOp`, instead of returning a target `OpName`, return an **OpInterp** (or directly the instantiated term) by using the morphism.

Change behavior:

* old: resolve alias+slot → target op name → `mkOp`
* new: resolve alias+slot → `OpInterp` → substitute args → resulting term (may be composite)

You’ll likely want a helper in `Kernel.Morphism`:

```haskell
lookupInterp :: Morphism -> OpName -> Either Text OpInterp
```

#### Boolean readback

Current `readbackCoreBool` assumes bool constants map to single target ops. With op→term morphisms, that assumption is false.

Update logic:

* Find an alias/morphism whose **source presentation contains** ops named `T` and `F` (resolved via `resolveOpNameIn`).
* Compute the translated constants as terms:

  * `tTerm = applyOpInterp (morOpMap[tOp]) []` (or just `oiRhs` for arity 0)
  * `fTerm = ...`
* Compare the normalized result term against `normalize(tTerm)` and `normalize(fTerm)` (same rewrite system/policy/fuel as the run).

  * If equal, return `True/False`.
  * Else `Nothing`.

This makes readback robust to nontrivial implementations later.

---

## 6. Run specs: module-level reuse and term-level runs

### 6.1. AST additions

In `Kernel.DSL.AST` add:

```haskell
data RawDecl
  = ...
  | DeclRunSpec Text RawRun       -- specName + raw config (rrExprText ignored/empty)
  | DeclRun     RawNamedRun       -- a named run term

data RawNamedRun = RawNamedRun
  { rnrName   :: Text
  , rnrUsing  :: Maybe Text
  , rnrRun    :: RawRun           -- includes overrides + exprText
  }
```

Keep `RawRun` structure (it already supports optional fields and has `rrUses`).

### 6.2. Parser changes (multiple runs per file)

Update `Parse.rawFile` to parse `many decl` and include run-related decls as normal decls (not a final `optional runDecl` that consumes rest-of-file).

#### `run_spec` parser

* `run_spec <ident> where { <runItems> } ;`
* Produce `DeclRunSpec specName rawRun{ rrExprText = "" }`

#### `run` parser with delimited body

Grammar:

```
run <name> (using <spec>)? where { <runItems> }
--- <take until terminating --- at start of line or EOF> ---
```

Implementation approach in Megaparsec:

* Parse header and block normally.
* Parse a delimiter line:

  * `symbol "---"` but ensure it’s on its own line (consume `eol`).
* Capture expression text until:

  * either the next delimiter line `---` (on its own line), OR EOF
* If a closing delimiter is present, consume it and continue parsing more decls.

**Key correctness constraint:** expression text is uninterpreted by DSL parser; do not attempt to parse it here.

### 6.3. Elaboration and environment integration

Extend `ModuleEnv` with:

```haskell
meRunSpecs :: Map Text RawRun
meRuns     :: Map Text RunSpec
```

Update `Kernel.DSL.Elab.elabRawFileWithEnv`:

* When encountering `DeclRunSpec name rawRun`:

  * insert into `meRunSpecs`, error on duplicates.
* When encountering `DeclRun rawNamedRun`:

  * store temporarily in a list or map in the accumulating env (e.g. `meRawRuns :: [RawNamedRun]`) OR just finalize later.
* After folding all decls, **resolve and elaborate runs**:

  * for each `RawNamedRun`:

    1. if `using = Just specName`:

       * lookup base `RawRun` in `meRunSpecs` (including imported specs already merged into base env)
       * merge base config with overrides:

         * scalar fields: override wins if `Just`
         * list fields (`rrOpen`, `rrShow`): concatenate base then override
         * `rrUses`: right-biased union by alias (override wins)
         * `rrExprText`: take from run (never from base)
    2. call existing `elabRun :: RawRun -> Either Text RunSpec`
    3. insert into `meRuns` keyed by run name

This reuses current defaulting behavior (`defaultFuel`, default policy, default show set, etc.).

### 6.4. Loader restriction: runs only in main file; specs allowed anywhere

In `Strat.Frontend.Loader`:

* Keep allowing `run_spec` declarations in imported modules.
* Reject `run` declarations in imported modules (like current behavior for the single run block).

  * Error message: “runs are only allowed in the main module; move it to the entry file.”

### 6.5. CLI selection

Update `Strat.CLI` and `app/Main.hs` to accept:

* `llang <file> [--run <RunName>]`

Update `Strat.Frontend.Run.runFile` to:

* load env
* select run spec:

  * if `--run name` provided: lookup in `meRuns`, else error
  * else:

    * if `meRuns` contains `"main"`: run it
    * else if exactly one run: run it
    * else error listing available runs

Add error text that prints available run names.

---

## 7. Frontend changes required by morphism op→term

### 7.1. Identity morphism must build OpInterp

Update `Frontend.Run.identityMorphism`:

* sort map = identity on sort ctors
* for each op `f` with decl `OpDecl tele res`:

  * build args as `mkVar s v` for each binder in `tele`
  * rhs = `mkOp (presSig pres) f args`
  * store `OpInterp tele rhs`

This requires no binder names; uses `Var`s from the signature decl as template vars.

### 7.2. `Surface2.CoreEval` must apply OpInterp

Update evaluation of core op calls so that alias calls produce a term via op interpretation instead of a target op name.

### 7.3. Ensure all places using `morOpMap :: Map OpName OpName` are updated

Search and fix:

* `Strat.Surface2.CoreEval`
* `Strat.Frontend.Run.readbackCoreBool`
* any helper that assumes op name mapping

---

## 8. Automated test plan (broad and directly checkable)

Update existing tests and add new ones. The goal is that the agent can run `test` and get deterministic failures that localize issues.

### 8.1. Kernel DSL parsing tests

File: `test/Test/Kernel/DSL.hs`

Add/adjust tests:

1. **Parse morphism op mapping with params**

   * Input:

     ```llang
     morphism M : A -> B where { op f(x,y) = g(?y,?x); }
     ```
   * Assert AST contains `RMIOp { rmiParams = Just ["x","y"], rmiRhs = ... }`.

2. **Parse shorthand**

   * `op f = g;` must parse with `rmiParams = Nothing` and `rmiRhs = RApp "g" []`.

3. **Parse run_spec and multiple runs**

   * A file with `run_spec S ...` and two runs must parse into two `DeclRun` entries and one `DeclRunSpec`.

4. **Delimited run body**

   * Ensure `---` terminator is respected and subsequent decls parse.

### 8.2. Kernel morphism correctness tests

File: `test/Test/Kernel/Morphism.hs`

Update old tests (which assumed op↦op) and add new ones.

#### Existing tests updates

* The “identity morphism” test can remain, but now compares:

  * `applyMorphismTerm idMor term` equals term (α-eq if needed).
* Update “renaming morphism” test to use shorthand op mappings.

#### New tests

1. **Nontrivial op→term interpretation preserves equations**

   * Use the `Invol/Invol2/Double` example (construct presentations in Haskell or parse a DSL snippet and elab).
   * Assert `checkMorphism` returns `Right ()`.

2. **Bad op interpretation fails obligation**

   * Source: involution `f(f(x)) = x`
   * Target: involution `g(g(x)) = x`
   * Map `f(x) = g(?x)` should **fail** because:

     * translated lhs: `g(g(x))` reduces to `x`
     * translated rhs: `x`
     * Actually this one would pass. Choose a failing map, e.g. `f(x) = g(g(g(?x)))`:

       * `f(f(x))` ↦ `g^6(x)` reduces to `x` (still passes).
         Use a target with *no* involution equation and expect failure:
     * Target doctrine with `g` but no rule `g(g(x)) -> x`
     * Then mapping `f(x)=g(g(x))` fails preservation.
   * Assert `checkMorphism` returns `Left (MorphismEquationViolation ...)`.

3. **Param list required if RHS uses variables**

   * DSL snippet:

     ```llang
     morphism M : A -> B where { op f = g(?x); }
     ```
   * Expect elaboration error with a specific message.

4. **Param arity mismatch**

   * `op f(x) = ...` but `f` is binary → error.

### 8.3. Requires/implements resolution tests

Add a new test module: `test/Test/Frontend/Implements.hs`

Scenarios (can be done by constructing envs directly, not via CLI):

1. **Explicit run implements wins**

   * Surface requires alias `i : I`
   * Run doctrine `D`
   * Two morphisms `m1, m2 : I -> D`
   * Run spec uses `implements i = m2`
   * Assert resolution picks `m2`.

2. **Declared default is used**

   * Same setup, but run spec provides nothing and `implements I for D using m1;` exists
   * Assert `m1` is used.

3. **Unique candidate fallback**

   * No declared default, only one morphism exists
   * Assert it is used.

4. **Ambiguity error**

   * No explicit, no default, two candidates
   * Assert error mentions ambiguity and suggests disambiguation.

### 8.4. Run spec reuse + multi-run selection tests (integration)

Update `test/Test/CLI.hs` and example files accordingly.

Add/adjust end-to-end example tests:

1. **Run spec in imported module**

   * `examples/runspec/spec.llang` defines `run_spec`.
   * `examples/runspec/main.llang` imports it and defines `run main using <spec>`.
   * CLI test runs `main.llang` and asserts expected output (value/cat/normalized).

2. **Multiple runs in a single file**

   * `examples/runspec/multi.llang` defines `run main ...` and `run other ...`.
   * Test:

     * default executes `main`
     * with `--run other` executes `other`

### 8.5. Surface tests impacted by `context_discipline` and multi-requires

Update:

* `test/Test/Surface2/Elab.hs`
* `test/Test/Surface2/Determinism.hs`
* Any surface DSL snippets must include `context_discipline cartesian;`
* Any `SurfaceDef` constructions must set `sdRequires = [...]` and `sdCtxDisc = CtxCartesian`.

---

## 9. Examples reorganization and updates

### 9.1. Minimal required edits to existing examples

#### Add `context_discipline cartesian;` to every `surface` example

Search/replace in `examples/**.surface.llang`.

#### Update morphism syntax in example morphisms

Most of your existing morphisms are `op f = f;` which remains valid (shorthand), so they may require no change.

However, update any morphism examples that relied on op↦op *without application* semantics in edge cases. Under the new shorthand, `op f = g;` always means full application to all args. That matches old behavior.

#### Add declared default implementations

In `examples/ccc_surface/ccc.interface.llang` (or a new “wiring” file), add:

```llang
implements CCC_Bool for CCC using CCCIface;
```

Then you can delete `use ccc = CCCIface;` / `implements ccc = CCCIface;` from individual runs unless you want to override.

### 9.2. Introduce run specs to reduce sprawl

#### Create a reusable config file for the STLC/CCC example

Create `examples/ccc_surface/stlc.runspec.llang`:

```llang
import "examples/ccc_surface/ccc.interface.llang";
import "examples/ccc_surface/ccc.llang";
import "examples/ccc_surface/stlc.surface.llang";
import "examples/ccc_surface/stlc.surfacesyntax.llang";
import "stdlib/syntax.llang";
import "stdlib/models.llang";

run_spec STLCinCCC where {
  doctrine CCC;
  open CCC;
  syntax CatSyntax;
  model Symbolic;
  surface STLC;
  surface_syntax Stlc;
  show result;
  show cat;
  show value;
}
```

Then replace `examples/ccc_surface/stlc.run.llang` with a thin term file:

```llang
import "examples/ccc_surface/stlc.runspec.llang";

run main using STLCinCCC;
---
(lam x:Bool. x) true
---
```

This demonstrates module-level reuse and eliminates duplicated run blocks.

### 9.3. New example: nontrivial op→term morphism

Add `examples/morphism_term.llang` exactly as in §2.2.

Optionally add a run that loads it (no evaluation needed; morphism check runs at elaboration).

### 9.4. New example: multi-run file + selection

Add `examples/runspec/multi.llang`:

```llang
import "examples/ccc_surface/stlc.runspec.llang";

run main using STLCinCCC;
---
(lam x:Bool. x) true
---

run beta using STLCinCCC;
---
(lam x:Bool. lam y:Bool. x) false true
---
```

Your CLI tests should assert:

* default executes `main`
* `--run beta` executes `beta`

---

## 10. Implementation order (to minimize rework)

1. **Kernel op→term morphisms**

   * Add `OpInterp`, update `Morphism` and translation.
   * Update morphism DSL AST/parse/elab.
   * Update `checkMorphism`.
   * Add/update kernel morphism tests.

2. **Frontend/surface integration**

   * Update identity morphism and core eval to use `OpInterp`.
   * Fix readback for booleans to compare translated terms.

3. **Multiple requires + ContextDiscipline**

   * Update surface AST/elab/def.
   * Update affected tests.

4. **Implements declarations + requirement resolution**

   * Add top-level `implements … for … using …;`.
   * Add env registry and resolution algorithm.
   * Tests for resolution and ambiguity.

5. **Run specs + multi-run parsing + selection**

   * Add `run_spec` and named `run` blocks.
   * Update loader restrictions.
   * Update CLI and run selection.
   * Update CLI tests and examples.

6. **Example refactor**

   * Move repeated configs into run specs.
   * Add new examples demonstrating new features.

---

## 11. Common pitfalls and how to avoid them

1. **Binder names are not stored in `OpDecl`.**
   Do not try to recover parameter names from the signature; require them syntactically (`op f(x,y)=...`) whenever RHS uses `?x`-vars.

2. **Dependent indices require dependency ordering.**
   If you skip topo sorting, morphisms will mysteriously fail on theories where result sorts contain terms like `Tm(Arr(A,B))`.

3. **Do not assume boolean constants map to ops.**
   With op→term, `T` could map to a compound term. Readback must compare normalized terms.

4. **Ambiguity must be an error, not a choice.**
   If multiple morphisms satisfy a requirement and there’s no explicit/default choice, fail loudly.

5. **Keep ContextDiscipline explicit but behavior-neutral for now.**
   Don’t refactor the entire surface engine; just add the explicit field and centralize context operations behind wrappers.

---

## 12. Concrete “definition of done” checklist

* [ ] `morphism` supports `op f(x,...) = <term>` and shorthand `op f = g`.
* [ ] Morphism checking validates op interpretations and equation preservation.
* [ ] Surfaces require `context_discipline cartesian;` and may list multiple `requires`.
* [ ] Top-level `implements I for D using M;` exists and is used for default requirement resolution.
* [ ] Runs resolve requirements using (explicit alias impl) > (declared default) > (identity) > (unique candidate) > error.
* [ ] `run_spec` exists; multiple named runs per file exist; selecting run works.
* [ ] All unit tests updated and extended as in §8.
* [ ] Examples updated; new examples added; CLI tests updated.

