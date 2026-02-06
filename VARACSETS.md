## Feature: literals (and attribute variables) via VarACSet-style attributed polygraphs

This is an end-to-end implementation plan for adding **literals in surfaces** in a way that is (1) theory-agnostic, (2) minimizes special-casing, and (3) cleanly extends the doctrine/morphism/rewrite stack.

The core idea is: **make generator instances carry “attributes”** (parameters) whose values live in a small, general **attribute term language** with **variables** and **ground literals**. This is exactly the “Attributed C-set with variables” move: the underlying open hypergraph stays the same; we add extra components/fields on edges and extend matching to unify those fields.

This avoids the infinite-generator-name hack for numeric literals and keeps compilation/morphism/rewrite theoretically coherent.

---

## 1) Core design

### 1.1 Extend diagrams to attributed hypergraphs

Currently an edge payload is `PGen GenName` or `PBox BoxName Diagram`. Change this to:

* `PGen GenName AttrMap`
* `PBox BoxName Diagram`

Where:

* `AttrMap = Map AttrName AttrTerm`
* `AttrTerm` is a **typed** first-order term fragment:

  * variables (`AttrVar`) and ground literals (`AttrLit`)
  * (no function symbols initially; see §1.5 for planned extension)

This yields a VarACSet-like structure:

* the hypergraph incidence is the C-set core
* edge attributes are extra “attribute components”
* attribute values may contain variables
* matching produces **both** type substitutions and attribute substitutions

### 1.2 Add an attribute signature to doctrines

Doctrines get a new signature part:

* attribute sorts (`attrsort`)
* generator attribute fields (`gen ... {field:Sort, ...} : dom -> cod @Mode;`)

No assumptions about the underlying theory:

* attribute sorts are opaque symbols
* only literal *kinds* are language-level (int/string/bool) and are opt-in per sort

### 1.3 Extend matching/rewrite/morphism to unify attributes

Every place the kernel currently unifies types must also unify attributes:

* graph isomorphism matching (`diagramIsoMatchWithTyVars`)
* pattern matching (`Match`)
* critical pair overlap construction (`CriticalPairs`)
* rule application (`Rewrite`)
* morphism generator instantiation (`Morphism.applyMorphismDiagram`)

Matching must now produce:

* `TySubst` (existing)
* `AttrSubst` (new)

and apply both to RHS/morphism images.

### 1.4 Surface literals compile to generator attributes

Surfaces get a new pattern capture class:

* `int` / `string` / `bool` captures (in addition to `ident`, `<expr>`, `<type>`)

Elaboration templates gain **attribute arguments** on generator calls, with a dedicated **attribute-hole** syntax:

* `$...` stays “diagram hole / wire variable” (unchanged semantics)
* **`#name`** becomes “inject captured literal/identifier into an attribute term”

This avoids adding ad-hoc “literal constructors” in the elaborator.

### 1.5 Attribute term language scope (initial + extension path)

**Initial implementation (required now):**

* attribute terms are only:

  * literals: `42`, `"foo"`, `true/false`
  * variables: `x` (typed by context)

This is enough for literals + attribute variables and keeps the implementation contained.

**Planned extension (explicitly not part of this PR):**

* add function symbols (`attrfun f : (S1,...,Sn)->S;`)
* allow `f(t1,...,tn)` in attribute terms
* unify as first-order terms
* later: conditional rewrite rules / computed rewrites

The initial design must not block this extension.

---

## 2) Exact syntax changes

### 2.1 Doctrine: attribute sorts

Add to doctrine blocks:

```
attrsort <SortName> = int;
attrsort <SortName> = string;
attrsort <SortName> = bool;
attrsort <SortName>;
```

Semantics:

* if `= <kind>` is present, that sort admits that literal kind in attribute positions
* if omitted, the sort admits variables but not ground literals (until you extend later)

### 2.2 Doctrine: generator attribute fields

Extend generator declarations:

Old:

```
gen Add : [A,A] -> [A] @M;
```

New (optional attribute field list in braces):

```
gen Lit {n:Int} : [] -> [A] @M;
gen Binop {op:Str} : [A,A] -> [A] @M;
```

Rules/cells do **not** need explicit attribute-variable binders. Attribute variables are inferred from use sites and must be sort-consistent.

### 2.3 Diagram expressions: generator calls with attributes

Extend generator term syntax:

```
Lit(n=42)
Lit(42)              -- allowed iff exactly one attribute field
Binop(op="+")        -- string literal
```

Also compatible with type args:

```
Foo{Ty1,Ty2}(x=42)
```

Rules:

* you may specify attributes either *all positional* or *all named*, never mixed
* omission:

  * if generator has no attributes: ok
  * if generator has attributes: error (“missing attributes”)

### 2.4 Surface patterns: literal captures

Add new pattern items:

* `int`
* `string`
* `bool`

Example:

```
atom:
  int    => LIT(n)
| string => STR(s)
| bool   => BOOL(b)
;
```

### 2.5 Surface templates: attribute arguments and attribute holes

Extend template generator calls:

```
LIT(n) => lit(n=#n);;
```

Rules for `#name` inside attribute terms:

* if captured AST is:

  * `SALitInt k` → attribute literal int `k`
  * `SALitString t` → attribute literal string `t`
  * `SALitBool b` → attribute literal bool `b`
  * `SAIdent x` → attribute literal string `"x"` (identifier-as-symbol)
* otherwise: error

Also allow direct literals in templates:

```
foo(x=42, y="bar")
```

No support for computed attribute expressions in templates in this iteration.

### 2.6 Models: attribute arguments passed before wire arguments

**No syntax change** to model clauses. But semantics change:

* For generator `g` with attribute fields `[a1,...,ak]` and wire inputs `[x1,...,xn]`,
  the model clause receives arguments in order:

```
[a1, ..., ak, x1, ..., xn]
```

So you write:

```
op Lit(n) = n;
op Binop(op, a, b) = ...;
```

This is minimal and keeps models theory-agnostic.

---

## 3) Concrete implementation specification

This section is written to the coding agent; implement exactly this.

### 3.1 New module: `Strat/Poly/Attr.hs`

Create a new module to centralize attribute logic.

```haskell
newtype AttrSort = AttrSort Text
  deriving (Eq, Ord, Show)

data AttrLitKind = LKInt | LKString | LKBool
  deriving (Eq, Ord, Show)

data AttrSortDecl = AttrSortDecl
  { asName    :: AttrSort
  , asLitKind :: Maybe AttrLitKind
  } deriving (Eq, Show)

data AttrVar = AttrVar
  { avName :: Text
  , avSort :: AttrSort
  } deriving (Eq, Ord, Show)

data AttrLit
  = ALInt Int
  | ALString Text
  | ALBool Bool
  deriving (Eq, Ord, Show)

data AttrTerm
  = ATVar AttrVar
  | ATLit AttrLit
  deriving (Eq, Ord, Show)

type AttrSubst = M.Map AttrVar AttrTerm
type AttrName  = Text
type AttrMap   = M.Map AttrName AttrTerm
```

Provide functions:

* `freeAttrVarsTerm :: AttrTerm -> Set AttrVar`
* `freeAttrVarsMap  :: AttrMap -> Set AttrVar`
* `applyAttrSubstTerm :: AttrSubst -> AttrTerm -> AttrTerm`
* `applyAttrSubstMap  :: AttrSubst -> AttrMap -> AttrMap`
* `composeAttrSubst :: AttrSubst -> AttrSubst -> AttrSubst`

  * same directionality as `composeSubst` in `UnifyTy`
* `unifyAttrFlex :: Set AttrVar -> AttrSubst -> AttrTerm -> AttrTerm -> Either Text AttrSubst`

  * variable-only unification:

    * literal vs literal: must be equal
    * var vs term:

      * if var in `flex`: bind (sort must match)
      * if var not in `flex`: only succeeds if term is the same var
    * term vs var: symmetric
  * no occurs check needed (no function symbols)

Also add rendering:

* `renderAttrSort`, `renderAttrVar`, `renderAttrTerm`

### 3.2 Extend `Strat/Poly/Doctrine.hs`

Add:

* `dAttrSorts :: M.Map AttrSort AttrSortDecl`

Extend `GenDecl`:

```haskell
data GenDecl = GenDecl
  { gdName   :: GenName
  , gdMode   :: ModeName
  , gdTyVars :: [TyVar]
  , gdDom    :: Context
  , gdCod    :: Context
  , gdAttrs  :: [(AttrName, AttrSort)]  -- ordered, names unique
  }
```

Update:

* `seedDoctrine` to copy `dAttrSorts` from base doctrines
* `validateDoctrine`:

  * check attribute sort decl uniqueness
  * check generator attr fields:

    * name uniqueness per generator
    * referenced sorts exist
  * (no further global constraints)

### 3.3 Extend edge payload everywhere

Change `EdgePayload` in `Strat/Poly/Graph.hs` (or wherever it lives) from:

* `PGen GenName`
  to:
* `PGen GenName AttrMap`

Update:

* constructors like `genD` / `genDWithPorts` to accept attrs (or default empty)
* all pattern matches on `PGen` across the codebase

### 3.4 Diagram utilities: apply attribute substitution and collect free vars

In `Strat/Poly/Diagram.hs` add:

* `freeAttrVarsDiagram :: Diagram -> Set AttrVar`

  * traverse edges; include nested boxes
* `applyAttrSubstDiagram :: AttrSubst -> Diagram -> Diagram`

  * map each `PGen name attrs` to `PGen name (applyAttrSubstMap subst attrs)`
  * recurse into boxes

Keep existing `applySubstDiagram :: TySubst -> Diagram -> Diagram` unchanged.

### 3.5 DSL AST changes: `Strat/Poly/DSL/AST.hs`

Add new raw items:

```haskell
data RawPolyItem
  = ...
  | RPAttrSort RawAttrSortDecl

data RawAttrSortDecl = RawAttrSortDecl
  { rasName :: Text
  , rasKind :: Maybe Text -- "int"|"string"|"bool"
  }
```

Extend raw generator decl:

```haskell
data RawPolyGenDecl = RawPolyGenDecl
  { rpgName  :: Text
  , rpgVars  :: [RawTyVarDecl]
  , rpgAttrs :: [(Text, Text)]   -- (fieldName, sortName)
  , rpgDom   :: [RawPolyTypeExpr]
  , rpgCod   :: [RawPolyTypeExpr]
  , rpgMode  :: Text
  }
```

Extend `RawDiagExpr` generator node:

```haskell
data RawDiagExpr
  = ...
  | RDGen Text (Maybe [RawPolyTypeExpr]) (Maybe [RawAttrArg])

data RawAttrArg
  = RAName Text RawAttrTerm
  | RAPos  RawAttrTerm

data RawAttrTerm
  = RATVar Text
  | RATInt Int
  | RATString Text
  | RATBool Bool
```

### 3.6 Parser changes: `Strat/DSL/Parse.hs`

Implement:

#### Doctrine

* Parse `attrsort` item:

  * `attrsort` `<Ident>` (`=` (`int`|`string`|`bool`))? `;`

* Parse generator attr fields:

  * after name and tyvars: optional `{ field: Sort, ... }`
  * field and sort are identifiers

#### Diagram expressions

Update `polyGenTerm`:

* parse ident
* optional type args `{...}` as before
* optional attr args `(...)`:

  * comma-separated args
  * each arg is either `name = term` or `term`
  * enforce “all named or all positional”

Parse `RawAttrTerm`:

* int literal: decimal
* string literal: existing `stringLit`
* bool literal: keywords `true`/`false`
* ident: variable

### 3.7 Poly elaboration changes: `Strat/Poly/DSL/Elab.hs`

Extend `elabPolyItem`:

* `RPAttrSort` inserts into `dAttrSorts`

  * translate kind strings to `AttrLitKind`

Extend `RPGen` elaboration:

* elaborate `rpgAttrs`:

  * resolve sort names via `dAttrSorts`
  * store ordered list into `gdAttrs`

Extend diagram elaboration (where generator nodes are elaborated):

* when elaborating a generator instance:

  1. look up gen decl
  2. process type args as before
  3. process attributes:

     * if `gdAttrs` empty:

       * require no attr args; attrs map = empty
     * else:

       * require attr args present and cover exactly the fields
       * build `AttrMap`
       * elaborate each raw attr term into typed `AttrTerm` using expected field sort:

         * literal kind check: the sort’s `asLitKind` must match
         * variable: create `AttrVar name expectedSort`
         * maintain a local `Map Text AttrSort` to ensure same var name never used at two different sorts within the same elaboration; if conflict, error
  4. build the diagram edge as `PGen genName attrs`

### 3.8 Pretty printing: `Strat/Poly/Pretty.hs`

When rendering a generator edge:

* render as:

  * `Gen{TyArgs}(attrArgs)` if both present
  * `Gen(attrArgs)` if attrs present and no ty args
  * `Gen{TyArgs}` if ty args present and no attrs
  * `Gen` otherwise

Attribute args printed named, in generator field order:

* `field=value`
* value:

  * ints as decimal
  * strings quoted
  * bool as `true/false`
  * vars as their name (no sort printing inline)

### 3.9 Surface changes

#### 3.9.1 `Strat/Poly/Surface/Spec.hs`

Extend:

* `PatItem` with:

  * `PatInt`
  * `PatString`
  * `PatBool`

Extend `SurfaceAST` with:

* `SALit AttrLit` (reuse `AttrLit` type; keep it central)

Add template attribute support:

* Change `TGen` to carry optional attribute args:

  * `TGen Text (Maybe [RawPolyTypeExpr]) (Maybe [TemplateAttrArg])`

Define:

```haskell
data TemplateAttrArg
  = TAName Text AttrTemplate
  | TAPos  AttrTemplate

data AttrTemplate
  = ATLIT AttrLit
  | ATHole Text     -- #name
  | ATVar Text      -- attribute variable (rare but allowed)
```

#### 3.9.2 `Strat/Poly/Surface/Parse.hs`

* Add parsing for pattern items:

  * keyword `int` → `PatInt`
  * keyword `string` → `PatString`
  * keyword `bool` → `PatBool`

* Extend `parsePatItem` and `parsePat` accordingly.

* In `parseTerm`, these are matched directly with `integer`, `stringLit`, `keyword "true"/"false"`.

* Extend captures:

  * add `CapLit AttrLit`
  * `capToAst` maps to `SALit`

* Extend template parsing:

  * parse generator calls with optional type args and optional attr args `(...)`
  * attr arg parsing uses an attribute template parser:

    * `#ident` → `ATHole ident`
    * int/string/bool literals → `ATLIT`
    * ident → `ATVar` (attribute variable)

#### 3.9.3 `Strat/Poly/Surface/Elab.hs`

In `evalTemplate` handling of `TGen`:

* look up gen decl
* build attribute map exactly as poly elaboration does, but attribute terms come from `AttrTemplate`:

  * `ATLIT lit` → `ATLit lit` (after kind check)
  * `ATHole name` → read from `paramMap[name]` and convert:

    * `SALit lit` → `ATLit lit`
    * `SAIdent x` → `ATLit (ALString x)`
    * otherwise → error
  * `ATVar x` → `ATVar (AttrVar x expectedSort)` (sort from the field)

Then create edge payload `PGen genName attrs`.

No other surface elaboration logic changes.

### 3.10 Matching and rewriting

#### 3.10.1 `Strat/Poly/Match.hs`

Extend:

```haskell
data Match = Match
  { ...
  , mTySub   :: Subst
  , mAttrSub :: AttrSubst
  }
```

Update:

* initial match has empty attr subst
* `payloadSubsts` for `PGen`:

  * gen names must equal
  * unify attribute maps fieldwise:

    * for each field `f`, unify `patternAttrs[f]` with `hostAttrs[f]`
    * use `unifyAttrFlex` with flex = free vars of pattern attr terms (or simpler: collect all vars in pattern diagram once and pass through)
  * return extended substitutions list
* `PBox` branch: iso matching must now also return attr substitutions (see next)

#### 3.10.2 `Strat/Poly/Graph.hs` iso matching

Replace `diagramIsoMatchWithTyVars :: Set TyVar -> Diagram -> Diagram -> Either Text [Subst]`

with:

```haskell
diagramIsoMatchWithVars
  :: Set TyVar
  -> Set AttrVar
  -> Diagram -> Diagram
  -> Either Text [(Subst, AttrSubst)]
```

* Whenever unifying port types: use `unifyTyFlex`
* Whenever comparing `PGen` payloads: unify attrs using `unifyAttrFlex` with attr-flex set
* Compose both substitutions throughout the search

This is required because boxes may contain literals/attr-vars.

#### 3.10.3 `Strat/Poly/Rewrite.hs`

When applying a match to RHS:

* apply type subst as before
* additionally apply attribute subst:

  * `rhs' = applyAttrSubstDiagram (mAttrSub match) (applySubstDiagram (mTySub match) rhs)`

### 3.11 Critical pairs / coherence

Update `Strat/Poly/CriticalPairs.hs` analogously:

* its `PartialIso` must carry both substitutions
* overlap extension must unify payload attributes when deciding compatibility
* rule instantiation in critical pairs must apply both substitutions

This is not optional: otherwise coherence is unsound once literals exist.

### 3.12 Morphisms

#### 3.12.1 Extend morphism signature

In `Strat/Poly/Morphism.hs`:

Add:

* `morAttrSortMap :: Map AttrSort AttrSort`

and add mapping validation:

* every attr sort used in `morSrc` that appears in generator attributes of mapped generators must be mapped
* target sorts must exist in `morTgt`

DSL: add morphism item:

```
attrsort <SrcSort> -> <TgtSort>;
```

#### 3.12.2 Apply morphism to attribute terms

Add:

* `applyMorphismAttrTerm :: Morphism -> AttrTerm -> Either Text AttrTerm`

  * literals unchanged
  * vars: rename sort via `morAttrSortMap`

#### 3.12.3 Morphism application on edges

In `applyMorphismDiagram`, for a `PGen genName attrsSrc`:

* compute `tySubstSrc` via existing `instantiateGen`
* map to `tySubstTgt` via existing `mapSubst`
* look up generator mapping diagram `image`

Then compute attribute instantiation:

* let source generator decl `genDecl` have attribute fields `[(f1,s1),...,(fk,sk)]`
* map sorts via `morAttrSortMap` to `s1',...,sk'`
* define “formal variables” in the target:

  * `vi = AttrVar fi s'i`
* map the *edge’s* attribute terms into target sorts:

  * `attrsSrcTgt = Map.map (applyMorphismAttrTerm mor) attrsSrc`
* unify each `vi` with the corresponding `attrsSrcTgt[fi]`, producing `attrSubst`

  * flex set = `{v1,...,vk}` (only these bind)

Instantiate image:

* `instImage0 = applySubstDiagram tySubstTgt image`
* `instImage  = applyAttrSubstDiagram attrSubst instImage0`

Splice as before.

#### 3.12.4 Generated coercions (`extends`, `pushout`, `coproduct`)

Update the auto-generated generator maps:

* mapping “generator to itself” must now include attribute pass-through:

If `g` has fields `{f1:s1,...,fk:sk}` then its auto-map is:

* `g(f1=f1, ..., fk=fk)` (variables)

This must be generated in:

* extends coercion
* pushout glue morphisms
* coproduct inl/inr morphisms

Also update pushout’s “single generator image” check to require:

* image diagram contains exactly one `PGen`
* and every target attribute field is a variable named exactly as the source field (after mapping)
* and no literals appear in those attribute positions

This keeps pushout in the “renaming/inclusion” fragment.

### 3.13 Evaluation (`Strat/Poly/Eval.hs`)

Update edge evaluation:

* `PGen name attrs`:

  * look up generator decl to know attribute field order
  * compute `attrVals` in that order by converting `AttrTerm -> Value`:

Conversion:

* `ATLit (ALInt n)` → `VInt n`
* `ATLit (ALString s)` → `VString s`
* `ATLit (ALBool b)` → `VBool b`
* `ATVar v` → `VAtom (renderAttrVar v)` (symbolic)

Call model interpreter with:

* `pmInterp model name (attrVals ++ wireArgs)`

Update default symbolic behavior to include attrVals too:

* `VList (VAtom (renderGen name <> "#i") : attrVals ++ args)`

No other evaluation changes.

Also update `evalCyclic` to pass attrs for `PGen`.

### 3.14 Model language enhancement needed for examples: list concatenation

In `Strat/Model/Spec.hs` / evaluation of `MBinOp`:

* extend `"++"`:

  * string++string as before
  * list++list concatenation

This is required to build token streams for RPN/prefix/infix in models without adding new syntax.

---

## 4) Tests

Add a new test module: `test/Test/Poly/Literals.hs` and update existing tests that pattern match on `PGen`.

### 4.1 Parsing and elaboration: generator attributes

Test: diagram expression parses and elaborates.

Input doctrine:

* mode `M`
* attrsort `Int = int`
* type `A @M`
* gen `Lit {n:Int} : [] -> [A] @M`

Assert:

* parsing `Lit(n=42)` yields a diagram with one edge:

  * payload `PGen "Lit" (Map.fromList [("n", ATLit (ALInt 42))])`

Also test positional:

* `Lit(42)` accepted and equals named form.

### 4.2 Surface literal capture + `#` injection

Define a minimal surface:

* lexer with symbols `()`
* expr atom: `int => LIT(n)`
* elaborate: `LIT(n) => Lit(n=#n)`

Run surface parse on `42` and check elaborated diagram has the same attribute payload as above.

### 4.3 Rewrite substitution uses attribute match

Doctrine:

* `IdLit {n:Int} : [] -> [A]`
* `Lit {n:Int} : [] -> [A]`
  Rule:
* `IdLit(n) == Lit(n)`

Build diagram `IdLit(7)` and normalize; expect result contains `Lit(7)` (attribute preserved).

This test forces:

* matching binds `n=7`
* RHS instantiation substitutes `n` correctly

### 4.4 Morphism attribute instantiation

Source doctrine:

* `Lit {n:Int} : [] -> [A]`

Target doctrine:

* `Lit2 {n:Int} : [] -> [B]`

Morphism maps:

* mode identity
* type map as needed
* gen map:

  * `Lit @M -> Lit2(n=n)`

Apply morphism to diagram `Lit(5)`, assert result is `Lit2(5)`.

### 4.5 Evaluation reads attribute args

Model:

* `op Lit(n) = n;`

Evaluate closed diagram `Lit(13)` and expect `VInt 13`.

### 4.6 Coherence/critical pairs regression guard

Add a tiny overlap test where two rules match only if attributes unify:

* two rules on `IdLit(n)` etc.
  The test is just “critical pairs computation does not crash and respects attr unification”. (You can assert count or joinability; minimal is enough.)

---

## 5) Minimal examples (showcase)

Create a new example library file:

### `examples/lib/codegen/arith_literals.llang`

```llang
doctrine Arith where {
  mode M;

  attrsort Int = int;

  type Code @M;

  gen lit {n:Int} : [] -> [Code] @M;
  gen add : [Code, Code] -> [Code] @M;
  gen mul : [Code, Code] -> [Code] @M;
}

surface ArithInfix where {
  doctrine Arith;
  mode M;

  lexer {
    keywords: ;
    symbols: "(", ")", "+", "*";
  }

  expr {
    atom:
      int => LIT(n)
    | "(" <expr> ")" => <expr>
    ;

    infixl 20 "*" => MUL(lhs, rhs);
    infixl 10 "+" => ADD(lhs, rhs);
  }

  elaborate {
    LIT(n) => lit(n=#n);;
    MUL(a,b) => ($1 * $2) ; mul;;
    ADD(a,b) => ($1 * $2) ; add;;
  }
}

model Eval : Arith where {
  default error "missing op";
  op lit(n) = n;
  op add(a,b) = a + b;
  op mul(a,b) = a * b;
}

model RPN : Arith where {
  default error "missing op";
  op lit(n) = [n];
  op add(a,b) = a ++ b ++ ["+"];
  op mul(a,b) = a ++ b ++ ["*"];
}

model Prefix : Arith where {
  default error "missing op";
  op lit(n) = [n];
  op add(a,b) = ["+"] ++ a ++ b;
  op mul(a,b) = ["*"] ++ a ++ b;
}

model Infix : Arith where {
  default error "missing op";
  op lit(n) = [n];
  op add(a,b) = ["("] ++ a ++ ["+"] ++ b ++ [")"];
  op mul(a,b) = ["("] ++ a ++ ["*"] ++ b ++ [")"];
}

model Lisp : Arith where {
  default error "missing op";
  op lit(n) = [n];
  op add(a,b) = ["("] ++ ["+"] ++ a ++ b ++ [")"];
  op mul(a,b) = ["("] ++ ["*"] ++ a ++ b ++ [")"];
}
```

### `examples/run/codegen/arith_literals.run.llang`

```llang
import "../../lib/codegen/arith_literals.llang";

run_spec Base where {
  doctrine Arith;
  mode M;
  surface ArithInfix;
  show value;
}

run eval using Base where { model Eval; }
---
2 + 3 * 4
---

run rpn using Base where { model RPN; }
---
2 + 3 * 4
---

run prefix using Base where { model Prefix; }
---
2 + 3 * 4
---

run infix using Base where { model Infix; }
---
2 + 3 * 4
---

run lisp using Base where { model Lisp; }
---
2 + 3 * 4
---
```

Expected outputs:

* Eval: `14`
* RPN: `[2, 3, 4, "*", "+"]`
* Prefix: `["+", 2, "*", 3, 4]`
* Infix: `["(", 2, "+", "(", 3, "*", 4, ")", ")"]`
* Lisp: `["(", "+", 2, "(", "*", 3, 4, ")", ")"]`

This demonstrates:

* surface integer literals
* attribute injection (`#n`)
* attribute passing through evaluation
* multiple “compilation targets” as models

---

## 6) Notes on theoretical fit and invariants

* This is exactly the **VarACSet** pattern: a diagram is a C-set instance of a hypergraph schema; edge attributes are additional components; attribute variables live in a term language; matching returns a unifier.
* No underlying theory assumptions:

  * attributes are uninterpreted except for literal decoding
  * models decide semantics
  * rewrite is syntactic + unification only
* No special-casing in the kernel beyond:

  * adding the attribute layer
  * adding literal token kinds (int/string/bool) as language primitives
* Future-ready:

  * adding `attrfun` later is a local extension of `AttrTerm` and `unifyAttrFlex`
  * adding computed rewrite conditions becomes possible without re-architecting diagrams

---

## 7) Implementation order (do this in sequence)

1. Add `Strat/Poly/Attr.hs` + unit tests for unify/subst.
2. Change `EdgePayload` to carry `AttrMap` and mechanically fix compile errors.
3. Extend doctrine with `dAttrSorts` + `gdAttrs`; update `validateDoctrine`.
4. Extend poly DSL AST + parser (`attrsort`, gen attrs, gen call attrs).
5. Extend poly elaboration to type-check/elaborate attribute args.
6. Add diagram-level utilities: `freeAttrVarsDiagram`, `applyAttrSubstDiagram`.
7. Update Pretty printer to render attrs.
8. Update Eval to pass attrs into models; extend `"++"` to list concat.
9. Update Match/Rewrite/Graph iso to unify attributes.
10. Update CriticalPairs/coherence to include attributes.
11. Update Morphism with `morAttrSortMap` and attribute instantiation; update generated morphisms.
12. Extend Surface parse/spec/elab with `int/string/bool` captures and `#name` injection.
13. Add example `arith_literals` files and wire into example runner (if you have CI/golden).

No backward-compat constraints: if you need to adjust existing examples or tests, update them to use the new rendered generator syntax (notably when a generator now prints as `g()` vs `g` only if you choose to print empty attr lists; do **not** print empty attr lists to minimize churn).

---

If anything in the current codebase conflicts with this design, the design wins. The only acceptable deviation is a purely mechanical refactor to reduce churn (e.g., naming or file splitting), but the semantics and syntax described above must be implemented exactly.
