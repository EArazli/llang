# Surface v2: Generic binder-aware syntax + user-defined typing rules + CCC/STLC example

This document is an implementation spec for adding a **fully generic** (user-defined) binder-aware surface layer on top of the existing kernel, with **typing rules in the DSL** and **elaboration into kernel terms** via an `interface` mapping.

The goal is:
- Users define a CCC doctrine as usual (`doctrine`).
- Users define a surface language (syntax with binders + judgments + rules + elaboration) in files (`surface`).
- Users define one or more surface syntaxes (`surface_syntax`) for parsing/printing surface terms.
- Users define one or more backends/models (`model`) – we will keep these symbolic.
- A single program file selects doctrine + surface + surface_syntax + interface + model, then runs one surface expression.

No STLC frontend is hardcoded into Haskell beyond a **generic** surface engine.

---

## 0. Clarify the new entities and how they coexist with existing ones

### `doctrine`
Unchanged. A doctrine is a typed (dependent-sorted) presentation: sorts, ops, equations, rewrite policies.

### `syntax` (existing)
Unchanged. This is Syntax v1: first-order notation for *core terms* (kernel `Term` via `CombTerm`). It is suitable for:
- core combinator programming
- untyped first-order DSLs
- direct manipulation of kernel terms

### `surface` (new)
A `surface` defines a **binder-aware** syntax category system (second-order signature), plus **judgments** and **inference rules** (typing rules, equality rules, etc.), plus **elaboration actions** that construct kernel terms via an `interface`.

- **Surfaces are not required for every doctrine.**
- Use `surface` when you want binders, contexts, and proof-driven elaboration (STLC, linear lambda, etc.).
- You can still write/run programs directly in kernel terms without surfaces.

### `surface_syntax` (new)
A `surface_syntax` defines parser/printer notations for a particular `surface`. It **does not replace** `syntax`.
- `syntax` parses/prints kernel terms (core programming).
- `surface_syntax` parses/prints *surface terms* (binder-aware).

### `interface` (new)
An interface maps abstract names used by surface elaboration (e.g. `CCC.eval`) to **concrete doctrine symbols** (e.g. `C.eval`).

**Can we auto-construct interfaces?**
- Sometimes, if a doctrine uses canonical names, we can provide a “by convention” shortcut later.
- In general, **no**: the interface cannot always be inferred because:
  - doctrines may name primitives differently,
  - doctrines may present structure differently (derived ops vs primitives),
  - a surface may require a *choice* of structure (e.g. which product association), which isn’t unique.
Therefore interfaces remain explicit and first-class.

---

## 1. Dependencies (allowed, non-obscure, recommended)

### Required (already likely present)
- `megaparsec` (already used in many Haskell projects; suitable for surface parsing)
- `text`, `containers`, `mtl`

### Recommended for correctness / maintainability
- `prettyprinter` (for canonical pretty printing; avoid brittle string concatenation)
- `tasty-quickcheck` + `QuickCheck` (property tests for substitution, roundtrips, rule soundness)

### Optional (future)
- `unification-fd` or `unification-fd`-style library could help, but **do not adopt it now** because we need higher-order pattern unification; it’s easier to implement Miller-pattern unification directly for our restricted ABT patterns.

---

## 2. Surface v2 core representation (Haskell)

Create a new subsystem under:
- `src/Strat/Surface2/...`

### 2.1 Syntactic sorts and ABT (presheaf) terms

We implement second-order abstract syntax via ABTs with de Bruijn indices for bound variables.

#### Names
- `Sort2Name` – names for surface syntactic sorts (e.g. `Ty`, `Tm`)
- `Con2Name` – names for constructors within a sort
- `JudgName` – names for judgments (e.g. `HasType`, `TyWf`, `Eq`)

#### Core surface term types
```hs
newtype Sort2Name = Sort2Name Text
newtype Con2Name  = Con2Name  Text
newtype JudgName  = JudgName  Text

-- de Bruijn bound variables
newtype Ix = Ix Int

data STerm
  = SBound Ix
  | SFree Text                -- global names / constants
  | SCon Con2Name [SArg]       -- constructor applied to args
  deriving (Eq, Ord, Show)

data SArg = SArg
  { saBinders :: [STerm]       -- binder types (surface terms, usually in sort Ty)
  , saBody    :: STerm
  } deriving (Eq, Ord, Show)
````

Notes:

* `saBinders` is the list of binder **types** introduced by this argument. (This is what makes the syntax second-order.)
* For untyped binders, allow binder “type” to be a distinguished surface sort (or use a dummy `UnitTy`).

#### Substitution / weakening

Implement:

* `weaken :: Int -> STerm -> STerm`  (shift indices >= cutoff)
* `subst0 :: STerm -> STerm -> STerm` (substitute for bound index 0, capture-avoiding)
* `substMany :: [STerm] -> STerm -> STerm`

These must traverse into `SArg` bodies, increasing cutoff by binder count.

**Tests required:**

* standard de Bruijn laws:

  * `subst0 (SBound 0) t == t`
  * shifting/substitution commutation laws (QuickCheck)

### 2.2 Patterns for rules: Miller patterns only

To keep proof search decidable and implementable, we restrict meta-variables in rule patterns to **Miller patterns**: metavariables applied only to distinct bound variables.

Define pattern terms:

```hs
newtype MVar = MVar Text

data PTerm
  = PBound Ix
  | PFree Text
  | PCon Con2Name [PArg]
  | PMeta MVar [Ix]           -- meta-var applied to a list of distinct bound indices
  deriving (...)

data PArg = PArg { paBinders :: [PTerm], paBody :: PTerm }
```

Unification/matching for patterns:

* `matchPTerm :: PTerm -> STerm -> Maybe Subst2`
* where `Subst2` maps `MVar` to a *lambda-abstraction* represented as a closure:

  * `MVar ↦ (arity k, body STerm)` meaning it expects k bound vars; apply by substituting those vars.

This is standard second-order pattern matching and is the right operational core for Fiore/Mahmoud-style second-order algebraic theories.

**Tests required:**

* match soundness: applying the resulting substitution to the pattern yields the target term.
* occurs-check for metavariables.

---

## 3. DSL additions: `surface`, judgments, rules, and elaboration actions

### 3.1 New top-level declarations

Extend the `.llang` meta-parser to support:

* `surface <Name> where { ... }`
* `surface_syntax <Name> for <SurfaceName> where { ... }`
* `interface <Name> for doctrine <DocExpr> where { ... }`

And extend `run where { ... }` to allow selecting a surface pipeline:

```
run where {
  doctrine <DocNameOrExpr>;
  open <Ns> ...;

  surface <SurfaceName>;
  surface_syntax <SurfaceSyntaxName>;
  interface <InterfaceName>;

  model <ModelName>;
  policy <RewritePolicy>;
  fuel <Int>;

  show normalized;
  show value;
  show cat;
}
---
<surface expression text>
```

### 3.2 Surface declaration contents

A surface has 4 sections:

1. **Sorts**
2. **Constructors**
3. **Judgments**
4. **Rules**

#### (1) Sorts

Example:

```
sort Ty;
sort Tm;
```

#### (2) Constructors (second-order)

Constructor declarations include:

* result sort
* arguments, each with a binder list (possibly empty)
* optional sort annotation for each argument and binder type

Example for STLC:

```
con UnitTy : Ty;
con ProdTy : (a:Ty) (b:Ty) -> Ty;
con ArrTy  : (a:Ty) (b:Ty) -> Ty;

con Var : (i:Nat) -> Tm;                 # optional if you want explicit vars; not required if using bound vars only
con Lam : (A:Ty) (body : [x:A] Tm) -> Tm;
con App : (f:Tm) (x:Tm) -> Tm;
con Pair : (x:Tm) (y:Tm) -> Tm;
con Fst  : (p:Tm) -> Tm;
con Snd  : (p:Tm) -> Tm;
```

**Important:** The binder list `[x:A]` introduces one bound variable into the body. The binder type `A` is a surface term of sort `Ty`.

We will represent each constructor argument as:

* binder types (a list of `Ty` terms)
* body term of some sort

We do not attempt to infer binder types. They are part of surface syntax + typing rules.

#### (3) Judgments

Judgments are declared with:

* input parameters (surface terms, contexts)
* output parameters (for elaboration results), explicitly marked

We need at minimum:

* a typing judgment that produces an elaboration term in the kernel.

Proposed judgment declaration syntax:

```
judgement HasType :
  (Γ:Ctx) (t:Tm) (A:Ty)
  => (e:Core);
```

Where:

* `Ctx` is a built-in meta-sort representing contexts of typed variables.
* `Core` is a built-in meta-sort representing kernel terms produced by elaboration.

You may also add:

```
judgement TyWf : (Γ:Ctx) (A:Ty) => ();
judgement EqTy : (Γ:Ctx) (A:Ty) (B:Ty) => ();
```

but for the MVP, `HasType` suffices.

#### (4) Rules

Rules are Horn-clause style with premises and a conclusion, plus an elaboration expression.

Example (STLC-style, declarative):

```
rule var :
  premise lookup(Γ, i) = A;
  --------------------------------
  HasType(Γ, #i, A) => proj(Γ, i);

rule lam :
  premise HasType(Γ, body, B) => eBody  under (Γ, x:A);
  -----------------------------------------------
  HasType(Γ, Lam(A, body), ArrTy(A,B)) => curry(A,B,Γ,eBody);

rule app :
  premise HasType(Γ, f, ArrTy(A,B)) => eF;
  premise HasType(Γ, x, A)         => eX;
  -----------------------------------------------
  HasType(Γ, App(f,x), B) => appCCC(A,B,Γ,eF,eX);
```

Key required features:

* Premises can bind outputs (`=> eF`, `=> eX`).
* Premises can extend context (`under (Γ, x:A)` or `Γ + A`).
* Conclusions can mention bound outputs and pattern variables.
* Terms in rules are patterns (`PTerm`) supporting binders and metavariables.

### 3.3 Elaboration expression language (`CoreExpr`)

Rules must construct kernel terms in a doctrine-independent way. They do so by calling interface operations.

Define a small `CoreExpr` language:

* Variables referencing:

  * rule metavariables (surface terms)
  * premise outputs (core terms)
  * context objects derived from Γ
* Interface op application:

  * `ccc.comp(...)`, `ccc.eval(...)`, etc.
* Built-in meta-functions:

  * `ctxObj(Γ)` : Core object term for the context object (product of types)
  * `tyObj(A)`  : Core object term for surface type A
  * `proj(Γ, i)` : Core morphism term for i-th variable projection
  * `pairM(e1,e2)` etc (optional helper)
* Conditionals are not needed for STLC; avoid general recursion.

Concrete syntax sketch:

```
ccc.comp( ctxObj(Γ), prod(exp(tyObj(A), tyObj(B)), tyObj(A)), tyObj(B),
         ccc.eval(tyObj(A), tyObj(B)),
         ccc.pair(exp(tyObj(A), tyObj(B)), tyObj(A), ctxObj(Γ), eF, eX))
```

But we will provide abbreviations for readability in the surface file (see the CCC example below).

**Important:** CoreExpr is not a general programming language. It is a typed AST builder for kernel terms.

---

## 4. Interfaces: kinds and instances

### 4.1 Interface kind (what a surface requires)

A surface can declare it requires an interface kind:

```
requires interface CCC;
```

The interface kind `CCC` is a set of named slots:

* Sort slots:

  * `ObjSort`, `HomSort`
* Op slots:

  * `id`, `comp`, `Unit`, `prod`, `terminal`, `exl`, `exr`, `pair`,
  * `exp`, `curry`, `eval`

Later, other surfaces can require other interface kinds.

### 4.2 Interface instance declaration

User maps interface slots to doctrine symbols:

```
interface MyCCC for doctrine CCC where {
  ObjSort = C.Obj;
  HomSort = C.Hom;

  id   = C.id;
  comp = C.comp;

  Unit = C.Unit;
  prod = C.prod;
  terminal = C.terminal;
  exl = C.exl;
  exr = C.exr;
  pair = C.pair;

  exp = C.exp;
  curry = C.curry;
  eval  = C.eval;
}
```

Validation performed at instantiation time:

* each slot must resolve to a declared symbol in the selected doctrine presentation,
* arities match expected,
* sort ctor shapes match expected (especially `Hom(Obj,Obj)`).

---

## 5. Execution pipeline (new “Surface runner”)

When `run` selects a surface pipeline:

1. Load modules (imports).
2. Elaborate doctrine to `Presentation`.
3. Compile rewrite system (kernel) as before.
4. Instantiate interface against presentation.
5. Parse surface term using `surface_syntax` (binder-aware parser).
6. Typecheck + elaborate using surface rules:

   * input: surface term `t`
   * output: surface type `A` (if inferred) and core term `e : Core`
7. Convert `CoreExpr` output to kernel `Term` (typed) via interface mapping.
8. Normalize kernel term using rewrite system.
9. Compile to `CatExpr` (existing).
10. Evaluate using selected `model` (symbolic), as before.
11. Print:

* surface pretty-printed input (optional)
* elaborated kernel term (debug flag)
* normalized kernel term printed using core `syntax` if provided, else raw
* `cat` and `value`

---

## 6. Proof search / typechecking engine (generic, declarative)

We implement a generic backward-chaining engine for judgments.

### 6.1 Representation of goals and derivations

```hs
data Goal = Goal
  { gJudg  :: JudgName
  , gArgs  :: [STermOrCtxOrCore]     -- mixed arguments
  , gOuts  :: [MetaVar]              -- output placeholders
  }

data Derivation = Derivation
  { dRule   :: RuleName
  , dSubst  :: Subst2
  , dPrem   :: [Derivation]
  , dOut    :: [CoreExpr]            -- outputs computed by rule
  }
```

### 6.2 Strategy (deterministic enough, but still generic)

* Try rules in declared order.
* Unify the goal with the conclusion pattern (pattern unification on surface terms; first-order on contexts).
* For each premise:

  * extend environment if premise is “under extended context”
  * recursively solve premise goals
* Evaluate rule’s `CoreExpr` template in an environment where:

  * matched metavariables are available
  * premise outputs are available

Use a fuel/limit to prevent runaway search. For STLC this will be syntax-directed and fast.

### 6.3 Context operations

We need built-in context primitives usable in rules:

* empty context `∙`
* extend `Γ, x:A`
* lookup `(Γ ⊢ #i : A)` where `#i` is de Bruijn variable

Implement context as:

```hs
data Ctx = Ctx [STerm]   -- list of types, newest at end (or front); choose one and stick to it
```

Provide builtin relation:

* `lookup(Γ, i) = A` which reduces deterministically.

---

## 7. Testing guidance (treat as “proof obligations”)

### 7.1 Unit tests for Surface2 core (must-have)

1. **ABT substitution laws**

* property tests for `weaken`/`subst0`
* alpha-stability: substitution should not capture

2. **Pattern matching soundness**

* if `matchPTerm p t = σ` then `applySubstPTerm σ p == t`

3. **Context lookup**

* deterministic correctness of `lookup`

### 7.2 Tests for the rule engine (must-have)

1. **Single-step rule application**

* Create a minimal surface with one judgment and one rule that matches a constructor.
* Ensure the engine produces a derivation with expected outputs.

2. **Backtracking behavior**

* Two rules can match; ensure ordering is respected, and errors are informative.

3. **Fuel cutoff**

* Engine terminates with a readable error when fuel exhausted.

### 7.3 End-to-end tests for CCC/STLC example (must-have)

Use the example files below. Add tests that:

* parse surface term under both surface syntaxes
* typecheck succeeds
* elaborated kernel term has sort `Hom(ctxObj(Γ), tyObj(A))`
* normalization preserves sort
* symbolic evaluation returns a value (non-error)

### 7.4 Golden tests (recommended)

Store expected normalized kernel term prettyprints and compare.

---

## 8. Full end-to-end CCC implementation (example files)

Create a folder `examples/ccc_surface/` with:

### 8.1 Doctrine: `ccc.doctrine.llang`

(Use a reasonably small CCC core. Equations can be minimal for the demo.)

```llang
doctrine CCC where {
  sort Obj;
  sort Hom(Obj, Obj);

  op id : (x:Obj) -> Hom(?x, ?x);

  op comp :
    (a:Obj) (b:Obj) (c:Obj)
    (f:Hom(?b, ?c)) (g:Hom(?a, ?b))
    -> Hom(?a, ?c);

  computational idL :
    (a:Obj) (b:Obj) (g:Hom(?a, ?b)) |-
      comp(?a, ?b, ?b, id(?b), ?g) -> ?g;

  computational idR :
    (a:Obj) (b:Obj) (f:Hom(?a, ?b)) |-
      comp(?a, ?a, ?b, ?f, id(?a)) -> ?f;

  op Unit : Obj;
  op prod : (a:Obj) (b:Obj) -> Obj;

  op exl : (a:Obj) (b:Obj) -> Hom(prod(?a, ?b), ?a);
  op exr : (a:Obj) (b:Obj) -> Hom(prod(?a, ?b), ?b);

  op pair :
    (a:Obj) (b:Obj) (c:Obj)
    (f:Hom(?c, ?a)) (g:Hom(?c, ?b))
    -> Hom(?c, prod(?a, ?b));

  op exp : (a:Obj) (b:Obj) -> Obj;

  op curry :
    (a:Obj) (b:Obj) (c:Obj)
    (f:Hom(prod(?c, ?a), ?b))
    -> Hom(?c, exp(?a, ?b));

  op eval :
    (a:Obj) (b:Obj)
    -> Hom(prod(exp(?a, ?b), ?a), ?b);

  # Optional β reduction for demo
  computational beta :
    (a:Obj) (b:Obj) (c:Obj)
    (f:Hom(prod(?c, ?a), ?b)) |-
      comp(prod(?c, ?a), prod(exp(?a, ?b), ?a), ?b,
           eval(?a, ?b),
           pair(exp(?a, ?b), ?a, prod(?c, ?a),
                comp(prod(?c, ?a), ?c, exp(?a, ?b),
                     curry(?a, ?b, ?c, ?f),
                     exl(?c, ?a)),
                exr(?c, ?a)))
        -> ?f;

  # Base objects for STLC demo
  op Bool : Obj;
  op T : Hom(Unit, Bool);
  op F : Hom(Unit, Bool);
}
```

### 8.2 Interface: `ccc.interface.llang`

```llang
interface CCCIface for doctrine CCC where {
  ObjSort = Obj;
  HomSort = Hom;

  id   = id;
  comp = comp;

  Unit = Unit;
  prod = prod;
  exl  = exl;
  exr  = exr;
  pair = pair;

  exp  = exp;
  curry = curry;
  eval  = eval;
}
```

### 8.3 Surface: `stlc.surface.llang`

This defines STLC *entirely in the DSL*, including typing rules and elaboration into CCC via the interface.

```llang
surface STLC where {
  requires interface CCC;

  sort Ty;
  sort Tm;

  # Types
  con BoolTy : Ty;
  con UnitTy : Ty;
  con ProdTy : (a:Ty) (b:Ty) -> Ty;
  con ArrTy  : (a:Ty) (b:Ty) -> Ty;

  # Terms
  con True  : Tm;
  con False : Tm;

  con Pair  : (x:Tm) (y:Tm) -> Tm;
  con Fst   : (p:Tm) -> Tm;
  con Snd   : (p:Tm) -> Tm;

  con Lam : (A:Ty) (body : [x:A] Tm) -> Tm;
  con App : (f:Tm) (x:Tm) -> Tm;

  judgement HasType : (Γ:Ctx) (t:Tm) (A:Ty) => (e:Core);

  # Builtins for translating Ty -> CCC Obj
  define tyObj(UnitTy) = ccc.Unit;
  define tyObj(BoolTy) = ccc.Bool;
  define tyObj(ProdTy(A,B)) = ccc.prod(tyObj(A), tyObj(B));
  define tyObj(ArrTy(A,B))  = ccc.exp(tyObj(A), tyObj(B));

  # Context object: right-associated products ending in Unit
  define ctxObj(∙) = ccc.Unit;
  define ctxObj(Γ, x:A) = ccc.prod(ctxObj(Γ), tyObj(A));

  # Projection morphism from context to variable i (de Bruijn from the right)
  # proj(Γ, 0) = exr(ctxObj(Γ'), A) where Γ = Γ', x:A
  # proj(Γ, i+1) = comp(ctxObj(Γ), ctxObj(Γ'), ..., exl, proj(Γ', i))
  define proj(Γ, 0) = ccc.exr(ctxObj(Γ'), tyObj(A))   where Γ = (Γ', x:A);
  define proj(Γ, i+1) =
    ccc.comp(ctxObj(Γ), ctxObj(Γ'), tyObj(Ai),
             proj(Γ', i),
             ccc.exl(ctxObj(Γ'), tyObj(A)))
    where Γ = (Γ', x:A);

  # Rules

  rule true :
    --------------------------------
    HasType(Γ, True, BoolTy) => ccc.comp(ctxObj(Γ), ccc.Unit, tyObj(BoolTy),
                                         ccc.T,
                                         ccc.terminal(ctxObj(Γ)));

  rule false :
    --------------------------------
    HasType(Γ, False, BoolTy) => ccc.comp(ctxObj(Γ), ccc.Unit, tyObj(BoolTy),
                                          ccc.F,
                                          ccc.terminal(ctxObj(Γ)));

  rule var :
    premise lookup(Γ, i) = A;
    --------------------------------
    HasType(Γ, #i, A) => proj(Γ, i);

  rule lam :
    premise HasType(Γ, body, B) => eBody  under (Γ, x:A);
    -----------------------------------------------
    HasType(Γ, Lam(A, body), ArrTy(A,B))
      => ccc.curry(tyObj(A), tyObj(B), ctxObj(Γ), eBody);

  rule app :
    premise HasType(Γ, f, ArrTy(A,B)) => eF;
    premise HasType(Γ, x, A)         => eX;
    -----------------------------------------------
    HasType(Γ, App(f,x), B)
      => ccc.comp(ctxObj(Γ),
                  ccc.prod(ccc.exp(tyObj(A), tyObj(B)), tyObj(A)),
                  tyObj(B),
                  ccc.eval(tyObj(A), tyObj(B)),
                  ccc.pair(ccc.exp(tyObj(A), tyObj(B)),
                           tyObj(A),
                           ctxObj(Γ),
                           eF,
                           eX));
}
```

Notes:

* This file assumes `ccc.Bool`, `ccc.terminal` exist; for the demo, either:

  * add `terminal` + `Bool` to the doctrine/interface, or
  * simplify `true/false` elaboration by treating them as constants `Hom(ctx, Bool)` directly.
    Keep this consistent; if `terminal` isn’t in the doctrine yet, include it.

### 8.4 Surface syntaxes

Two syntaxes that differ superficially (lambda token and arrow type token).

#### `stlc.syntax1.llang`

```llang
surface_syntax STLC1 for STLC where {
  # types
  ty print atom "Bool" = BoolTy;
  ty print atom "Unit" = UnitTy;
  ty print infixl 7 "*" = ProdTy;
  ty print infixr 5 "->" = ArrTy;

  # terms
  tm print atom "true" = True;
  tm print atom "false" = False;

  tm print binder "\\" ":" "." = Lam;     # \x : A . t
  tm print app = App;

  tm print tuple "," = Pair;
  tm print prefix "fst" = Fst;
  tm print prefix "snd" = Snd;
}
```

#### `stlc.syntax2.llang`

```llang
surface_syntax STLC2 for STLC where {
  # types
  ty print atom "𝟙" = UnitTy;
  ty print atom "𝔹" = BoolTy;
  ty print infixl 7 "×" = ProdTy;
  ty print infixr 5 "⇒" = ArrTy;

  # terms
  tm print atom "T" = True;
  tm print atom "F" = False;

  tm print binder "lam" ":" "=>" = Lam;   # lam x : A => t
  tm print app = App;

  tm print tuple "," = Pair;
  tm print prefix "π1" = Fst;
  tm print prefix "π2" = Snd;
}
```

### 8.5 Two symbolic models (trivial differences)

Keep these in `examples/ccc_surface/models.llang`.

```llang
model SymbolicTree where {
  default = symbolic;
}

model SymbolicTag where {
  # identical to symbolic except wraps the op name
  default = symbolic;
  # override only nullary ops for visibility
  op Bool() = "OBJ:Bool";
  op Unit() = "OBJ:Unit";
}
```

If your model DSL cannot easily return strings for Obj-sorts, keep both purely symbolic:

* second model returns a different atom prefix:

  * `op T() = "Const:T";` etc.
    This is sufficient to demonstrate semantics swapping.

### 8.6 Two run files (exercise both syntaxes/models)

#### `run1.llang` (syntax1 + SymbolicTree)

```llang
import "./ccc.doctrine.llang";
import "./ccc.interface.llang";
import "./stlc.surface.llang";
import "./stlc.syntax1.llang";
import "./models.llang";

run where {
  doctrine CCC;
  surface STLC;
  surface_syntax STLC1;
  interface CCCIface;

  model SymbolicTree;
  policy UseOnlyComputationalLR;
  fuel 300;

  show normalized;
  show cat;
  show value;
}
---
(\x:Bool. x) true
```

#### `run2.llang` (syntax2 + SymbolicTag)

```llang
import "./ccc.doctrine.llang";
import "./ccc.interface.llang";
import "./stlc.surface.llang";
import "./stlc.syntax2.llang";
import "./models.llang";

run where {
  doctrine CCC;
  surface STLC;
  surface_syntax STLC2;
  interface CCCIface;

  model SymbolicTag;
  policy UseOnlyComputationalLR;
  fuel 300;

  show normalized;
  show cat;
  show value;
}
---
(lam x:𝔹 => x) T
```

Expected:

* Both runs typecheck and elaborate.
* Both normalize to the CCC morphism corresponding to the variable projection / identity function applied to a constant (depending on your constant encoding).
* The `value:` differs between models (trivially), demonstrating backend swapping.
* The `cat:` output differs only in the value interpretation, not in the compiled categorical AST.

---

## 9. Implementation stages for the agent (do in order)

### Stage 1: Core ABT + substitution + pattern matching

* Implement `Strat.Surface2.Term` and `Strat.Surface2.Pattern`.
* Add unit tests: substitution laws, match soundness.

### Stage 2: Surface DSL parsing and elaboration (AST -> SurfaceDef)

* Extend DSL AST + parser + elaborator:

  * `surface`
  * `surface_syntax`
  * `interface`
* Store these in module environment alongside doctrines/syntax/models.

### Stage 3: Surface syntax parsing/printing (binder-aware)

* Implement a binder-aware parser/printer for `surface_syntax`:

  * types and terms have separate notation tables (`ty ...`, `tm ...`)
  * binder notation supported:

    * parse: `\x:A. t` and `lam x:A => t`
    * maintain env: name -> de Bruijn
  * application parsing (left-assoc) and printing (canonical, with parentheses)

Tests:

* parse/print roundtrip for closed terms
* alpha-equivalence aware roundtrip for binder terms (parse(print(t)) α= t)

### Stage 4: Generic judgment engine with rule matching

* Implement backward chaining for rules:

  * match goal with rule conclusion (pattern match)
  * solve premises (recursive)
  * compute outputs by evaluating `CoreExpr` templates

Tests:

* micro-surface with one rule
* STLC subset (var/lam/app) checks on small terms

### Stage 5: Interface instantiation + CoreExpr -> kernel Term

* Implement interface resolution into `OpName` / `SortName`.
* Implement `CoreExpr` evaluation to kernel `Term` using the interface.
* Implement built-in `tyObj`, `ctxObj`, `proj` functions (generic; not STLC hardcoding, just context utilities).

Tests:

* output kernel term sort-checks against signature
* normalization preserves sort
* `compileTerm` works as before

### Stage 6: End-to-end runner integration

* Extend `run` runner:

  * if `surface` fields present: use surface pipeline
  * else: use existing core pipeline
* Add golden tests for the provided examples in `examples/ccc_surface/`.

---

## 10. Notes on correctness and “proof-like” testing

Passing tests should establish (as close as feasible):

* ABT substitution is capture-avoiding and correct.
* Pattern matching for rules is sound (Miller patterns).
* Rule engine produces derivations whose premises are valid.
* Core elaboration builds kernel terms that typecheck in the chosen doctrine.
* Rewriting normalization is type-preserving (already tested in kernel suite).
* Syntaxes are correct up to α-equivalence.
* Models are swappable: same normalized term, different value.

This is the right shape of confidence for a research-grade metaprogramming system without implementing a full proof assistant kernel.