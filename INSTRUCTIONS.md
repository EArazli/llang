# Implementation plan: Native types + pushout-based doctrine composition + model/doctrine interoperability

This plan assumes **no backward compatibility**. It replaces the current “doctrine expression” combinators (`&`, `rename`, `share`, `include`, `@`) with a single coherent mechanism centered on:

* **Doctrines = presentations** (sorts, operations, equations/rewrite rules).
* **Morphism = interpretation** from one doctrine into another (already exists).
* **Pushout = automatic doctrine composition** along a shared interface, producing a combined doctrine **and** canonical injection morphisms.
* **Interoperability** is “terms transport along morphisms”; a term in a smaller doctrine is usable in a larger one via the injection morphism.
* **Models are contravariant in doctrines**: a model for a larger doctrine can be restricted to a smaller doctrine using a morphism (implemented by term transport + evaluation).

Tensor is explicitly out of scope.

---

## 0) Target outcome (what must exist when done)

### Language-user capabilities

1. **Native types** are available as *standard library doctrines* (initially `Nat`, `Bool`) and users can extend them.
2. Users can write doctrines as:

   * **Atomic** doctrines (`doctrine X where { ... }`)
   * **Extensions** of a base doctrine (`doctrine X extends Y where { ... }`) — but implemented without `include`.
   * **Pushouts** (`doctrine X = pushout f g;`) which:

     * compute the combined doctrine presentation,
     * automatically generate injection morphisms `X.inl`, `X.inr`,
     * and generate a “glue” morphism `X.glue` from the common interface into `X`.
3. **Interoperability**:

   * If `Dsmall -> Dlarge` exists (inclusion/injection morphism), then any term in `Dsmall` can be used in `Dlarge` automatically by transporting it through the morphism.
4. **Models integrated with doctrine morphisms**:

   * A model declared for `Dlarge` can be used when running code in `Dsmall` if there exists a morphism `Dsmall -> Dlarge`. The system transports the term to `Dlarge` and evaluates it using the model.

### Engineering invariants

* The **only** doctrine composition primitive exposed in the surface language is **pushout** (and `extends` as sugar that expands into a copy+merge).
* All old doctrine combinators (`&`, `rename`, `share`, `include`, `@`) are removed from:

  * the parser,
  * the AST,
  * the spec,
  * and the tests.
* Existing kernel notions of:

  * `Presentation`, `Signature`, `Equation`, `Term`, `Morphism`
    remain valid and are reused.

---

## 1) High-level approach (the coherent “theory”, in engineer terms)

### 1.1 Doctrines

A doctrine is just a `Presentation`:

* Sort constructors: `sort S (x:...) ...;`
* Ops: `op f : (...) -> ...;`
* Equations (rewrite rules) used operationally: `computational ruleName : (...) |- lhs -> rhs;`

### 1.2 Morphisms (already in code)

A morphism `m : A -> B`:

* maps each sort name in `A` to a sort name in `B`
* maps each op in `A` to a **term** in `B` (already supported)

### 1.3 Pushout (the new composition engine)

Given morphisms with the **same source** (interface) `A`:

* `f : A -> B`
* `g : A -> C`

The pushout constructs `P = B ⊔_A C` such that:

* `P` contains all of `B` and `C`
* the “copies” of `A` inside `B` and `C` are **identified**
* the system generates canonical injections:

  * `P.inl : B -> P`
  * `P.inr : C -> P`
* and a glue embedding:

  * `P.glue : A -> P`

### 1.4 Interoperability

If you have a morphism `m : D1 -> D2` then:

* you can transport a term `t : D1` into `D2` as `applyMorphismTerm m t`
* this is the only mechanism needed for:

  * “term in `CCC+Bool` works in `CCC+Bool+Nat`”
  * surface requirements resolution
  * restricting models (see next)

### 1.5 Models: restriction along morphisms

A model is an evaluator for a particular doctrine `D` (you already have `ModelSpec` → `Model`).

Key new rule:

* If you have:

  * a model `M` for `Dlarge`
  * and a morphism `i : Dsmall -> Dlarge`
* then you can evaluate terms from `Dsmall` by:

  1. transporting term `t` into `Dlarge`: `t' = applyMorphismTerm i t`
  2. evaluating in `Dlarge` using `M`

This achieves “model for larger doctrine should be valid for smaller doctrine” with **zero extra user work** as long as the injection morphisms exist (which pushout generates).

---

## 2) Milestones (implement in this order)

1. **Kernel refactor**: Extract rename/merge utilities out of `DoctrineExpr` into reusable modules.
2. **Pushout engine**: Implement pushout computation + automatic injection/glue morphisms.
3. **Frontend/DSL changes**: Remove old doctrine combinators; add `pushout` doctrine declaration; update AST/parser/elaborator.
4. **Interop plumbing**: Ensure generated morphisms are registered so surface/run resolution uses them.
5. **Model restriction**: Allow runs to use models for super-doctrines by term-transport.
6. **Native types**: Ship `Nat`, `Bool` doctrines + models as stdlib; add a pushout demo using them.
7. **Spec update + test suite rewrite**: Remove obsolete spec parts; add pushout + model restriction tests.

---

## 3) Kernel refactor: remove `DoctrineExpr` and keep only needed functionality

### 3.1 Delete / deprecate

* Remove module: `src/Strat/Kernel/DoctrineExpr.hs`
* Remove tests: `test/Test/Kernel/DoctrineExpr.hs`, `test/Test/Kernel/Include.hs`
* Remove any `DocExpr` references from `Frontend.Env`, `DSL.AST`, `DSL.Parse`, `DSL.Elab`, and `Frontend.Run`.

### 3.2 Create new modules (pure refactor)

Create:

1. `src/Strat/Kernel/Presentation/Rename.hs`

   * Move and export:

     * `qualifyPresentation`
     * `renameSortsPresentation`
     * `renameOpsPresentation`
     * `renameEqsPresentation`
     * `mapPresentationOps` helpers if needed
   * Ensure the renamers correctly update:

     * sort/op names
     * term nodes
     * binder scopes (`ScopeId`s) (existing code already does for ops/sorts; preserve this).

2. `src/Strat/Kernel/Presentation/Merge.hs`

   * Move and export:

     * `mergePresentations`
     * signature merge helpers (sort ctor merge, op decl merge)
     * equation merge behavior (dedupe by alpha-equivalence)

These are currently embedded in `DoctrineExpr.hs` and are required for pushout.

### 3.3 Add morphism utilities

Create `src/Strat/Kernel/Morphism/Util.hs`:

* `identityMorphism :: Presentation -> Morphism`
* `symbolMapMorphism :: Presentation -> Presentation -> Map SortName SortName -> Map OpName OpName -> Either Text Morphism`

  * constructs a morphism where each op maps to `op'(vars...)` in order
* `composeMorphism :: Morphism -> Morphism -> Either Text Morphism`

  * required for later extensions; for now pushout injections can be directly built as symbol maps
* `isSymbolMap :: Morphism -> Either Text (Map OpName OpName)`

  * verifies each `oiRhs` is `TOp op' [TVar v0, ..., TVar vn-1]`

You already have the term machinery to do this check, since `TermNode` is available.

---

## 4) Pushout implementation

### 4.1 Restrictions (explicitly enforced)

Implement pushout **only** for morphisms that behave like *signature embeddings/renamings* (“symbol maps”), i.e.:

* Same source doctrine: `morSrc f == morSrc g`
* For every source op `o`, `f(o)` and `g(o)` are direct applications of a single op symbol to the parameters:

  * `f(o)(x0..xn-1) = oB(x0..xn-1)`
  * `g(o)(x0..xn-1) = oC(x0..xn-1)`
* Additionally enforce injectivity on the interface image:

  * the sort mapping restricted to interface sorts is injective
  * the extracted op-symbol mapping restricted to interface ops is injective

If these fail, error message should say:

* “pushout currently requires symbol-map morphisms (op ↦ op(args…)); got general term interpretation for op …”

This restriction is important because you want **rewrite-rule composability**: after pushout, both sides’ rules should rewrite the **same** shared operations, not merely be provably equal.

### 4.2 API

Create `src/Strat/Kernel/Pushout.hs`:

```haskell
data PushoutResult = PushoutResult
  { poPres  :: Presentation
  , poInl   :: Morphism   -- B -> P
  , poInr   :: Morphism   -- C -> P
  , poGlue  :: Morphism   -- A -> P
  }
```

Expose:

```haskell
computePushout :: Text -> Morphism -> Morphism -> Either Text PushoutResult
```

`Text` is the *name* of the resulting doctrine (used as `presName`), but symbol names inside remain namespaced from their origin doctrines (except interface symbols unified to the interface names).

### 4.3 Algorithm (step-by-step)

Inputs: `f : A -> B`, `g : A -> C`

1. **Validate preconditions**

   * same source `A`
   * `isSymbolMap f`, `isSymbolMap g` (extract op name maps)
   * check injectivity of:

     * `morSortMap f` on `sigSortCtors(A)`
     * `morSortMap g` on `sigSortCtors(A)`
     * extracted `opMapF` on `sigOps(A)`
     * extracted `opMapG` on `sigOps(A)`

2. **Build renaming maps to unify interface symbols**

   * For each sort `sA` in `A`:

     * `sB = morSortMap f ! sA`
     * `sC = morSortMap g ! sA`
     * rename **both** `sB` and `sC` to the interface name `sA`

       * `renameSortB[sB] = sA`
       * `renameSortC[sC] = sA`
   * For each op `oA` in `A`:

     * `oB = opMapF[oA]`
     * `oC = opMapG[oA]`
     * rename **both** `oB` and `oC` to the interface name `oA`

       * `renameOpB[oB] = oA`
       * `renameOpC[oC] = oA`

3. **Apply renamings**

   * `B' = renameOpsPresentation renameOpB (renameSortsPresentation renameSortB B)`
   * `C' = renameOpsPresentation renameOpC (renameSortsPresentation renameSortC C)`

4. **Merge `A`, `B'`, and `C'` into the pushout presentation**

   * `P0 = mergePresentations [A, B', C']`

     * (implementation detail: merge is binary, but merge list is fine)
   * Set `presName = pushoutName` for the resulting `Presentation`

     * do **not** re-qualify all symbols; keep existing namespaces

5. **Generate morphisms**

   * `poGlue : A -> P` should be an *inclusion* (identity-on-symbols), since interface symbols in `P` are exactly those of `A`.

     * build via `symbolMapMorphism` with identity sort/op maps
   * `poInl : B -> P`:

     * sort map: for each sort in `B`, map using `renameSortB` if present else identity
     * op map: for each op in `B`, map using `renameOpB` if present else identity
     * build via `symbolMapMorphism B P sortMap opMap`
   * `poInr : C -> P` similarly
   * Run `checkMorphism` on all generated morphisms; failure indicates a bug in renaming/merge.

6. Return `PushoutResult`

### 4.4 What this buys you (verify with tests)

Because interface ops are renamed to interface op names:

* A rewrite rule from `B` targeting its copy of an interface op will, after pushout, target the **same** op symbol as a rewrite rule from `C` targeting its copy.
* So rewrite rules compose “a la carte” without manual `share` combinators.

---

## 5) Frontend/DSL rewrite (remove old doctrine expressions; add pushout decl)

### 5.1 Remove from surface language (parser + spec)

Completely delete these constructs:

* Doctrine expressions:

  * `a & b`
  * `rename ... in ...`
  * `share ... in ...`
  * `X@Y`
* Within `doctrine ... where { ... }`:

  * `include ...`

### 5.2 New surface syntax (minimal set)

#### Doctrines

1. Atomic doctrine:

```llang
doctrine Category where {
  sort Obj;
  op a : Obj;
  op f : (x:Obj) -> Obj;

  computational r_id : (x:Obj) |- f(?x) -> ?x;
}
```

2. Extension (sugar; no `include`)

```llang
doctrine BoolExt extends Category where {
  op g : (x:Obj) -> Obj;
  computational r_bool : (x:Obj) |- f(?x) -> g(?x);
}
```

**Semantics**: `extends` means “copy base doctrine’s raw declarations into this doctrine before qualifying”, same as old `extends` but without exposing `include`.

3. Pushout doctrine:

```llang
doctrine Both = pushout BoolExt.fromBase NatExt.fromBase;
```

Where `BoolExt.fromBase` and `NatExt.fromBase` are morphisms `Category -> BoolExt` and `Category -> NatExt`.

#### Morphisms

Keep the existing morphism block syntax, but also add an **auto-generated** morphism for `extends` and for `pushout` outputs.

* For every `doctrine X extends Y`, automatically generate:

  * `morphism X.fromBase : Y -> X` (name fixed; see below)

* For every `doctrine P = pushout f g`, automatically generate:

  * `morphism P.inl : (tgt f) -> P`
  * `morphism P.inr : (tgt g) -> P`
  * `morphism P.glue : (src f) -> P`

#### Naming conventions (must be deterministic)

Pick exactly these names (so tests can rely on them):

* `X.fromBase` for `extends`
* `P.inl`, `P.inr`, `P.glue` for pushouts

### 5.3 AST changes (`src/Strat/Kernel/DSL/AST.hs`)

* Delete `RawExpr` entirely.
* Replace doctrine decls with:

```haskell
data RawDecl
  = DeclDoctrineWhere Text (Maybe Text) [RawItem]          -- name, maybe extends base, items
  | DeclDoctrinePushout Text Text Text                     -- name, morphismLeft, morphismRight
  | DeclMorphism Text Text Text [RawMorphismItem] (Maybe RawCheckSpec)
  | ... (surface/syntax/model decls as needed)
```

* Remove:

  * `DeclExpr`
  * `ItemInclude`
  * all `EAnd/ERename*/EShare*/EInst`

Update all users of these types accordingly.

### 5.4 Parser changes (`src/Strat/Kernel/DSL/Parse.hs`)

* Remove expression grammar for doctrines.

* Implement:

* `doctrine Name where { ... }`

* `doctrine Name extends Base where { ... }`

* `doctrine Name = pushout morph1 morph2;`

Also remove parsing for:

* `&`, `rename`, `share`, `@`, `include`

### 5.5 Elaboration changes (`src/Strat/Kernel/DSL/Elab.hs` and `src/Strat/Frontend/Loader.hs`)

You want the module env to contain **fully elaborated** doctrines (presentations), not doc expressions.

Update `ModuleEnv`:

* Replace `meDoctrines :: Map Text DocExpr` with:

  * `meDoctrines :: Map Text Presentation`
* Remove `mePresentations` if it only existed to support `@` and `include`.

  * If you still need raw presentations for `extends`, keep:

    * `meRawDoctrines :: Map Text Presentation` (unqualified raw) to clone into extension.

Elaboration steps in load order:

1. For `DeclDoctrineWhere`:

   * elaborate raw presentation from items
   * if `extends Base`, merge raw(Base) into raw(Name) before qualifying
   * qualify the combined raw presentation by `Name` (reuse `qualifyPresentation`)
   * validate
   * store:

     * raw under `meRawDoctrines[Name]`
     * qualified under `meDoctrines[Name]`
   * generate morphism `Name.fromBase : Base -> Name`

     * This is a symbol-map morphism built by prefix-renaming:

       * `Base.SortX` ↦ `Name.SortX`
       * `Base.opY` ↦ `Name.opY`
     * Run `checkMorphism` and store in `meMorphisms`

2. For `DeclDoctrinePushout`:

   * look up morphisms `f` and `g`
   * call `computePushout Name f g`
   * store `poPres` under `meDoctrines[Name]`
   * store generated morphisms:

     * `Name.inl`, `Name.inr`, `Name.glue` into `meMorphisms`

---

## 6) Interoperability changes (term transport & requirement resolution)

### 6.1 Ensure surface “requires” uses morphisms

Wherever the system currently resolves a required doctrine into the run doctrine via defaults, keep that strategy, but make sure:

* pushout-generated morphisms are present, so the resolver finds them.
* if multiple morphisms exist, error out with a clear message listing candidates.

### 6.2 Make transports explicit in runtime

When compiling/evaluating:

* If a term originates in doctrine `D1` but the evaluator is in doctrine `D2`,

  * require a morphism `m : D1 -> D2`,
  * transport with `applyMorphismTerm m`.

This should be used in:

* surface elaboration when embedding core terms into run doctrine
* model restriction (next section)

---

## 7) Models: integrate with doctrine morphisms (restriction)

### 7.1 Keep `ModelSpec` (initially)

Do not redesign the model language yet. Instead, make it “mesh nicely” by adding **automatic restriction**.

### 7.2 New capability: run can use a super-doctrine model

Update `Frontend.Run` logic:

Current state (approx):

* run selects doctrine `D`
* instantiates model for `D`
* evaluates

New state:

1. Let run doctrine be `Drun`.
2. Let selected model be declared against doctrine `Dmodel` (store this association in env).
3. Cases:

   * If `Dmodel == Drun`: evaluate normally.
   * Else if there exists a morphism `m : Drun -> Dmodel`:

     * transport normalized term: `t' = applyMorphismTerm m t`
     * evaluate `t'` in model `Mmodel`
   * Else: error:

     * “Model M expects doctrine Dmodel, but run doctrine is Drun; no morphism Drun -> Dmodel found.”

This implements “model for larger doctrine valid for smaller doctrine”.

### 7.3 Needed env change

In `ModuleEnv`, store models with their doctrine:

```haskell
meModels :: Map Text (Text {-doctrine name-}, ModelSpec)
```

When instantiating, lookup the doctrine presentation for the model’s doctrine name.

---

## 8) Native types (stdlib doctrines + models)

### 8.1 Provide doctrine fragments

Create stdlib files (or embed them in `stdlib/std.llang`):

`stdlib/nat.llang`:

```llang
doctrine Nat where {
  sort Nat;
  op Z : Nat;
  op S : (n:Nat) -> Nat;

  op add : (a:Nat)(b:Nat) -> Nat;
  computational addZ : (b:Nat) |- add(Z, ?b) -> ?b;
  computational addS : (a:Nat)(b:Nat) |- add(S(?a), ?b) -> S(add(?a, ?b));
}
```

`stdlib/bool.llang`:

```llang
doctrine Bool where {
  sort Bool;
  op T : Bool;
  op F : Bool;

  op if : (c:Bool)(x:Bool)(y:Bool) -> Bool;
  computational ifT : (x:Bool)(y:Bool) |- if(T, ?x, ?y) -> ?x;
  computational ifF : (x:Bool)(y:Bool) |- if(F, ?x, ?y) -> ?y;
}
```

These are “native” because you’ll ship default models for them.

### 8.2 Provide models for native types

`stdlib/native.models.llang`:

```llang
model NatAsInt : Nat where {
  op Z() = 0;
  op S(n) = n + 1;
  op add(a,b) = a + b;
}

model BoolAsBool : Bool where {
  op T() = true;
  op F() = false;
  op if(c,x,y) = if c then x else y;
}
```

(Use whatever expression language your current model spec supports; the example mirrors existing `examples/peano.models.llang`.)

### 8.3 (Optional, recommended) Add a model “overlay” mechanism later

Not required now. The minimal path is:

* user defines a model for a combined doctrine that extends existing nat/bool models, or
* you allow selecting a model for a super doctrine and restricting.

---

## 9) Examples to add (and expected behavior)

### 9.1 Pushout example (new file `examples/pushout_basic.llang`)

```llang
doctrine Category where {
  sort Obj;
  op a : Obj;
  op f : (x:Obj) -> Obj;
}

doctrine BoolExt extends Category where {
  op g : (x:Obj) -> Obj;
  computational rB : (x:Obj) |- f(?x) -> g(?x);
}

doctrine NatExt extends Category where {
  op h : (x:Obj) -> Obj;
  computational rN : (x:Obj) |- f(?x) -> h(?x);
}

doctrine Both = pushout BoolExt.fromBase NatExt.fromBase;
```

**Manual verification checklist** (agent should add to a CLI test or REPL test):

* In `Both`, the shared op should be `Category.f` (not `BoolExt.f` and not `NatExt.f`).
* Rewriting `Category.f(Category.a)` should allow either rule `BoolExt.rB` or `NatExt.rN` to fire.

### 9.2 Native types via pushout (new file `examples/native_pushout.llang`)

Show how to combine a base doctrine with Nat and Bool by pushout over an interface; simplest is coproduct-over-empty, but since “tensor out of scope” and you removed `&`, use a small `Empty` interface:

```llang
doctrine Empty where { }

morphism emptyToNat : Empty -> Nat where { }   -- should default or be auto-generated; otherwise write explicit
morphism emptyToBool : Empty -> Bool where { }

doctrine NatBool = pushout emptyToNat emptyToBool;
```

If you don’t want to support empty morphisms, you can skip this example and focus on pushout over shared interfaces instead.

---

## 10) Test plan (must be implemented; remove obsolete tests)

### 10.1 Unit tests: `test/Test/Kernel/Pushout.hs`

Write tests that construct minimal `Presentation`s and `Morphism`s directly (no parsing) and assert:

1. **Happy path**: pushout unifies interface symbols

   * Define `A` with sort `A.Obj`, op `A.f`.
   * Define `B` that contains `B.Obj`, `B.f` and rule `B.rB` on `B.f`.
   * Define `C` similarly.
   * Define morphisms `f : A -> B`, `g : A -> C` mapping `A.Obj ↦ B.Obj`, `A.f ↦ B.f`, etc.
   * Pushout should produce `P` containing `A.Obj`, `A.f`.
   * In `P`, both rewrite rules should rewrite `A.f(...)`.

2. **Generated injections are valid morphisms**

   * `checkMorphism poInl`, `checkMorphism poInr`, `checkMorphism poGlue` succeed.

3. **Failure: not a symbol map**

   * Define a morphism where an op maps to a non-trivial term (`g(g(x))`).
   * `computePushout` must fail with a clear error.

4. **Failure: non-injective interface image**

   * Map two different interface ops to the same target op.
   * Must fail before attempting merge.

### 10.2 Frontend parser/elaborator tests: update `test/Test/Kernel/DSL.hs`

Add a test file string that uses the new syntax:

* `doctrine Both = pushout ...`
* Ensure it elaborates and `Both` exists in env
* Ensure `Both.inl`, `Both.inr`, `Both.glue` exist in env morphisms.

### 10.3 Model restriction test: new `test/Test/Frontend/ModelRestriction.hs`

* Build doctrines:

  * `Category`, `BoolExt`, `NatExt`, `Both = pushout ...`
* Declare a model for `Both` that gives an interpretation for `Category.a` and `Category.f` (e.g., symbolic or integer)
* Run evaluation **in doctrine `Category`** using the `Both` model.
* Assert:

  * The run succeeds (i.e., the system found a morphism `Category -> Both` and transported the term).
  * The evaluated result matches evaluating the transported term in `Both`.

### 10.4 Update `test/Spec.hs`

* Remove imports:

  * `Test.Kernel.DoctrineExpr`
  * `Test.Kernel.Include`
* Add import and include:

  * `Test.Kernel.Pushout`
  * `Test.Frontend.ModelRestriction` (if added)

---

## 11) SPEC.md update (required; remove obsolete sections)

### 11.1 Delete/replace these spec parts

Remove the current section that describes doctrine expressions and combinators:

* `&` / conjunction
* `rename` combinators
* `share` combinators
* `include`
* instantiation `@`

Also remove any grammar productions mentioning them.

### 11.2 Add a new “Doctrine assembly” section

Add a crisp section describing:

1. **Atomic doctrine definition** (`doctrine X where { ... }`)
2. **Extension** (`doctrine X extends Y where { ... }`)

   * semantics: clone `Y` into `X` namespace, then add declarations
   * generated morphism: `X.fromBase : Y -> X`
3. **Pushout** (`doctrine P = pushout f g;`)

   * preconditions: `f` and `g` share source, are symbol maps, injective on interface
   * outputs:

     * doctrine `P`
     * morphisms `P.inl`, `P.inr`, `P.glue`
4. **Interoperability rule**:

   * “If there is a morphism `m : D1 -> D2`, terms from `D1` can be transported into `D2`.”
5. **Model restriction rule**:

   * “A model for `Dlarge` can be used for `Dsmall` if `Dsmall -> Dlarge` exists; evaluation proceeds by transport then evaluation.”

### 11.3 Update the “Models” section to reflect restriction

* Keep your current model language description if you are not redesigning it.
* Add the new compatibility rule and explain it operationally.

### 11.4 Update/remove examples in SPEC.md

Any examples using `&`, `include`, `share`, `rename`, `@` must be rewritten using:

* `extends`
* `pushout`
* generated morphisms (`.fromBase`, `.inl`, `.inr`, `.glue`)

---

## 12) Explicit removal list (so nothing obsolete lingers)

The agent must remove all user-facing support for:

* `&` doctrine composition
* `rename ... in ...`
* `share ... in ...`
* `include ...` inside doctrine blocks
* `@` instantiation

This includes:

* Parser rules
* AST constructors
* Elaboration paths
* Spec documentation
* Tests that mention them
* Examples that use them

Internal helpers for renaming/merging may remain (moved modules), but the language should not expose the old combinators.

---

## 13) Post-implementation acceptance checklist

The implementation is considered correct when all of these are true:

1. `SPEC.md` contains **no** mention of `&`, `include`, `rename`, `share`, `@`.
2. A user can define `Category`, `BoolExt extends Category`, `NatExt extends Category`, and then:

   * `doctrine Both = pushout BoolExt.fromBase NatExt.fromBase;`
3. `Both` automatically has morphisms:

   * `Both.inl : BoolExt -> Both`
   * `Both.inr : NatExt -> Both`
   * `Both.glue : Category -> Both`
4. In `Both`, rewrite rules from both extensions apply to the **same** shared `Category` operations (proof by unit test on rewriting).
5. Running with doctrine `Category` and a model declared for `Both` works (transport + evaluate).
6. All tests pass after deleting/replacing the old doctrine expression test suite.
