## Phase 0 — Lock baseline, add scaffolding

### Goal

Create a “known-good” checkpoint so Phase 1 refactors don’t silently break things, and establish a place for new mode/type tests and migration notes.

### Implementation steps

#### 0.1 Baseline checkpoint

1. **Create a dedicated checkpoint commit** (single commit).
2. Verify baseline is green:

   * Run: `stack test`
   * If anything fails, fix it *inside this checkpoint commit* (don’t proceed to Phase 1 with a failing baseline).

#### 0.2 Add placeholder test module

1. Create file: `test/Test/Poly/TypeModes.hs`

2. Add a `tests :: TestTree` export, with an **empty** test group (no assertions yet), e.g.:

   * Module name should match project conventions: `Test.Poly.TypeModes`
   * Use `Test.Tasty` and return `testGroup "Poly.TypeModes" []`

3. Wire it into the test suite:

   * Edit `test/Spec.hs`

     * Add `import qualified Test.Poly.TypeModes`
     * Add `Test.Poly.TypeModes.tests` into the `testGroup` list

This ensures the module compiles and is part of the suite from now on.

#### 0.3 Add migration doc

1. Create file: `docs/MIGRATION.md`
2. Minimal initial content:

   * Title + short purpose
   * A section for Phase 1 changes (can be empty placeholders for now)

Example skeleton:

```md
# MIGRATION

This document records user-facing syntax and behavior changes.

## Phase 1 — Mode-signatured type constructors + modeful type expressions
(TODO: filled during Phase 1 implementation)
```

### Acceptance criteria

* `stack test` passes.
* `docs/MIGRATION.md` exists.
* `test/Test/Poly/TypeModes.hs` exists and is compiled by the test suite.

---

## Phase 1 — Mode-signatured type constructors + modeful type expressions

### Goal

Implement mode-aware kernel types end-to-end:

* Type constructors have **mode signatures** `(m1,…,mk) → m`.
* Type expressions can include constructors from different modes (nested).
* Type variables are **mode-indexed**.
* Parsing/elaboration/validation/unification/pretty-printing/stdlib/tests all updated.

### Critical sanity constraints (must enforce)

These are easy to miss and will create ambiguous programs if not enforced:

1. **TyVar binder names must be unique by name (tvName), not by (tvName,tvMode).**
   Otherwise you can bind `a@C` and `a@V` and then the reference `a` in type expressions becomes ambiguous (there is no planned `a@C` syntax inside type expressions).
2. **Any operation that traverses a `TypeExpr` must use the constructor’s own mode (`trMode`)** rather than an ambient “current mode”.
   This affects morphism application and pushout renaming in particular: nested constructors may be from different modes.

---

# 1.1 Kernel data structure changes

### 1.1.1 Update `TypeExpr` to carry mode-qualified constructors and mode-indexed tyvars

**File:** `src/Strat/Poly/TypeExpr.hs`

Replace the current definitions:

* Old:

  * `TyVar = TyVar Text`
  * `TypeExpr = TVar TyVar | TCon TypeName [TypeExpr]`

* New (per plan):

  * `data TypeRef = TypeRef { trMode :: ModeName, trName :: TypeName }`
  * `data TyVar  = TyVar  { tvName :: Text,    tvMode :: ModeName }`
  * `data TypeExpr = TVar TyVar | TCon TypeRef [TypeExpr]`

Also add the kernel-wide helper:

* `typeMode :: TypeExpr -> ModeName`

  * `typeMode (TVar v) = tvMode v`
  * `typeMode (TCon r _) = trMode r`

Notes:

* Derive `Eq`, `Ord`, `Show` for all new types so existing `Map/Set` usage works.
* Update any utility functions or pattern matches across the repo that assumed `TyVar` was a `newtype`.

### 1.1.2 Update the doctrine type table to store signatures

**File:** `src/Strat/Poly/Doctrine.hs`

Introduce:

```haskell
data TypeSig = TypeSig { tsParams :: [ModeName] }
```

Change doctrine field:

* Old:

  * `dTypes :: Map ModeName (Map TypeName Int)`
* New:

  * `dTypes :: Map ModeName (Map TypeName TypeSig)`

Add helper:

* `lookupTypeSig :: Doctrine -> TypeRef -> Either Text TypeSig`

  * lookup by `trMode` then `trName`
  * good error messages: unknown mode, unknown type, etc.

### 1.1.3 Update pretty-printing of types

**File:** `src/Strat/Poly/Pretty.hs` (and any other renderers)

Update `renderType`:

* Constructors print as:

  * `Mode.TypeName` for 0 args
  * `Mode.TypeName(arg1, arg2)` for args
* Decide how to print tyvars:

  * Recommended for unambiguous debugging: `name@Mode` (even if surface syntax doesn’t require it)
  * If you keep printing just `name`, you lose mode information in debug output; that will make diagnosing mode bugs much harder.

This will require updating CLI golden outputs.

---

# 1.2 Concrete syntax + AST changes (poly DSL + surfaces)

## 1.2.1 Represent qualified constructors and mode-annotated tyvar binders in the raw AST

### Poly raw AST

**File:** `src/Strat/Poly/DSL/AST.hs`

Add raw representations:

* `RawTypeRef` that can be qualified or unqualified, e.g.

  * `data RawTypeRef = RawTypeRef { rtrMode :: Maybe Text, rtrName :: Text }`
* `RawTyVarDecl` for binders:

  * `data RawTyVarDecl = RawTyVarDecl { rtvName :: Text, rtvMode :: Maybe Text }`

Then update:

* `RawPolyTypeExpr`:

  * From: `RPTCon Text [RawPolyTypeExpr]`
  * To: `RPTCon RawTypeRef [RawPolyTypeExpr]`
    (`RPTVar Text` remains)
* `RawPolyTypeDecl`, `RawPolyGenDecl`, `RawPolyRuleDecl`:

  * Replace `[Text]` binder lists with `[RawTyVarDecl]`

### Top-level morphism AST

**File:** `src/Strat/DSL/AST.hs`

Update `RawPolyTypeMap` binder params:

* From: `[Text]`
* To: `[RawTyVarDecl]` (or reuse the same type via import if layering allows)

Reason: type map binders may need mode annotations and must ultimately align to the source `TypeSig.tsParams`.

## 1.2.2 Update parsers

### Update poly doctrine parsing in the top-level DSL parser

**File:** `src/Strat/DSL/Parse.hs`

#### Type declarations

Support both:

* Canonical:

  * `type Thunk (a@C) @V;`
  * `type Pair (a@V, b@V) @V;`
* Sugar:

  * `type T a b @M;` (interpreted as `(M,M)->M`)

Implementation details:

* Parse binder list as either:

  * Parenthesized, comma-separated: `(` binder `,` binder ... `)`
  * Or legacy whitespace list: `binder binder binder ...`
* Binder parser: `ident` then optional `@ ident` (no whitespace required).

#### Generator/rule binders

Support annotated binders:

* `gen force (a@C) : ... @V;`
* Default binder mode: declaration mode (generator/rule’s `@Mode`) when omitted

#### Type expressions

Update `polyTypeExpr` parser to support qualified constructors:

* Unqualified constructor: `T(...)`
* Qualified constructor: `V.Thunk(C.A)`
* Qualified nullary: `C.A`

Parsing approach:

* Parse `seg1 <- identRaw`
* If next char is `.`, parse `seg2 <- identRaw` and treat as qualified constructor ref.
* Then optional args `( ... )`.
* Variable-vs-constructor decision:

  * If qualified: always constructor.
  * Else if args exist: constructor.
  * Else if first char is lower: variable.
  * Else: constructor.

### Update poly diagram expression parser (poly-only module)

**File:** `src/Strat/Poly/DSL/Parse.hs`

This module duplicates `polyTypeExpr` logic. Update it consistently (or refactor a shared raw-type parser used by both parsers).

### Update surface parsing

**File:** `src/Strat/Poly/Surface/Parse.hs`

You must update surface type parsing to accept `Mode.Type` qualified constructors and the new raw AST shapes.

Recommended architecture change (because surfaces do not have doctrine info at parse time):

* Make the surface parser produce **raw type expressions** (the same `RawPolyTypeExpr`), not kernel `TypeExpr`.
* This implies updating `SurfaceSpec`, `TemplateExpr`, and `SurfaceAST` to carry raw type expressions in place of `TypeExpr` (details below in §1.3 Surface changes).

---

# 1.3 Elaboration + validation changes

## 1.3.1 Elaboration of type expressions

**File:** `src/Strat/Poly/DSL/Elab.hs`

Update `elabTypeExpr` to:

1. Resolve constructor reference:

   * If raw ref is qualified `Mode.Type`, use that mode.
   * If unqualified, find **all** modes in the doctrine where `TypeName` exists:

     * 0 → error unknown type constructor
     * 1 → choose it
     * > 1 → error ambiguous; require `Mode.` qualification
2. Lookup `TypeSig` and check arity.
3. Elaborate each argument recursively.
4. Check each argument mode matches `TypeSig.tsParams[i]`.
5. Return modeful `TypeExpr` using `TypeRef`.

Implementation notes:

* Elaboration environment for type variables must now map by **name** to a `TyVar` that includes mode.
* Ensure binder tyvar names are unique by `tvName` at binder construction time.

## 1.3.2 Elaboration of type decls and binders

**File:** `src/Strat/Poly/DSL/Elab.hs`

### Type declarations

When elaborating `type Name (binders) @ResultMode;`:

* Compute `TypeSig.tsParams`:

  * For each binder:

    * if `binder` has explicit `@Mode`, use it
    * else default to **ResultMode**
* Store the signature at:

  * `dTypes[ResultMode][Name] = TypeSig tsParams`

### Generator/rule tyvar binders

For `gen` / `rule` binder lists:

* Each binder with no explicit mode defaults to the declaration’s `@Mode` (generator/rule mode).

## 1.3.3 Context elaboration + boundary-mode enforcement

**File:** `src/Strat/Poly/DSL/Elab.hs`

Update `elabContext` to:

* Elaborate each raw type expr to `TypeExpr`
* Enforce: `typeMode t == expectedBoundaryMode` for each boundary type
  (nested types can differ; only top-level mode matters)

Do this for:

* generator dom/cod
* rule dom/cod
* `id [ ... ]` contexts in diagram expressions

## 1.3.4 Doctrine validation

**File:** `src/Strat/Poly/Doctrine.hs`

Update `validateDoctrine` checks:

1. **Modes exist**

   * Every `TypeRef.trMode`
   * Every `TyVar.tvMode`
   * Every `TypeSig.tsParams[i]`

2. **Type expressions well-formed**

   * For every `TCon ref args`:

     * `lookupTypeSig doc ref` succeeds
     * arg count matches
     * each argument’s `typeMode` matches the corresponding signature mode

3. **Generator boundaries in generator mode**

   * For each boundary type `t` in `gdDom` and `gdCod`:

     * `typeMode t == gdMode`

4. **Binder uniqueness**

   * In `gdTyVars` and `c2TyVars`: reject duplicates by `tvName`
   * Same for morphism `TypeTemplate.ttParams` (see below)

This is required to avoid ambiguous variable references in type expressions.

---

# 1.4 Unification changes

**File:** `src/Strat/Poly/UnifyTy.hs`

Implement mode-respecting unification:

1. `TVar v` can only bind/unify with a type `t` if:

   * `tvMode v == typeMode t`

2. `TCon r ...` only unifies with `TCon r ...` where:

   * `r` is exactly equal (includes mode + name)

Where to enforce:

* In both `unifyTyFlex` and `unifyTy`, in the `unifyVar` / `bindVar` logic:

  * Before binding `v := t`, check mode equality; else error.

Update `renderTy` used in error messages to print the new type form (mode-qualified) so failures are diagnosable.

---

# 1.5 Mechanical fallout: morphisms, pushouts, surfaces, stdlib, tests

Even though Phase 1’s headline is “types”, this refactor will break any module that assumes “ambient mode determines type constructor mode”. Fix these now so Phase 1 ends in a buildable system.

## 1.5.1 Morphism application must traverse by constructor mode

**File:** `src/Strat/Poly/Morphism.hs`

Key updates:

* Any function currently taking an ambient `mode` to rename or map a `TypeExpr` must be changed to use `trMode` from each encountered `TypeRef`.

Specifically:

* `applyTypeMapTy` currently uses `(mode, name)` for lookups. That is wrong once nested constructors can be from other modes.

  * Change the type map key to `TypeRef` (recommended), or compute `(trMode,trName)` at each node.
* Update `renameTypeExpr` similarly.

Also update:

* `checkTypeMapTypes` / `checkGenMapping` if they pattern match on old constructors.

## 1.5.2 Pushout code must be updated to `TypeSig` and modeful constructors

**File:** `src/Strat/Poly/Pushout.hs`

Mechanical changes:

* Replace all uses of arity `Int` with `TypeSig`:

  * arity = `length tsParams`
* Update merging logic:

  * When merging type tables, type equality must include `TypeSig` equality, not just arity.
* Update `renameTypeExpr` to use the type’s own `trMode` for `(mode,name)` lookups.
* Ensure any permutation logic still works with modeful tyvars; keep binder uniqueness by name.

This is large but mostly mechanical.

## 1.5.3 Surface changes required for Phase 1 correctness

### Data structure change (recommended)

Because surface parsing occurs before doctrine elaboration, the surface parser cannot enforce the “unqualified must be unique across all modes” rule. So surfaces should carry **raw** type expressions and elaborate them later given the doctrine.

Update:

* `src/Strat/Poly/Surface/Spec.hs`

  * Replace `TypeExpr` occurrences with raw type expr (reuse `Strat.Poly.DSL.AST.RawPolyTypeExpr`)
  * Affected fields:

    * `ssContext :: Maybe (Text, RawPolyTypeExpr)`
    * `TemplateExpr` type lists
    * `SurfaceAST`’s `SAType`

Update:

* `src/Strat/Poly/Surface/Parse.hs`

  * Parse `<type>` into `RawPolyTypeExpr` using the new qualified constructor syntax.
  * Parse templates similarly.

Update:

* `src/Strat/Poly/Surface/Elab.hs`

  * Before using any `SAType rawTy`, elaborate it to kernel `TypeExpr` using the doctrine and the same resolution rules as poly DSL:

    * unqualified constructor must be unique across all doctrine modes
    * argument modes must match signatures
  * Update `initEnv` to build a modeful `TyVar` for the context variable:

    * `TyVar { tvName = ctxName, tvMode = surfaceMode }`
  * Update all hard-coded `TypeName "prod"` / `TypeName "Hom"` constructors and matchers to include `TypeRef surfaceMode (...)`.

This keeps existing surface behavior but makes it compatible with Phase 1 types.

## 1.5.4 Update stdlib and examples to new syntax

Update all `stdlib/*.llang` and `examples/*.llang`:

* Type decls:

  * Prefer canonical `type T (a@M, b@M) @M;`
  * Nullary stays `type Bool @M;`
* Gen/rule binders:

  * Prefer `gen dup (a@M) : ... @M;`
  * Prefer `rule ... (a@M, b@M) : ... @M = ...;`

Type expressions inside contexts can remain unqualified as long as each type constructor name is unique across modes (all current single-mode examples will pass). You do *not* need to add `M.` everywhere unless you want maximum explicitness.

## 1.5.5 Update and add tests

### Update all existing test constructions

Most tests manually build `Doctrine`, `GenDecl`, and `TypeExpr` values.
You must update them to:

* use `TypeRef` for constructors
* use `TyVar {tvName,tvMode}` instead of `TyVar "a"`
* store `TypeSig` in `dTypes`

Examples:

* `TCon (TypeName "A") []` becomes:

  * `TCon (TypeRef mode (TypeName "A")) []`
* `TyVar "a"` becomes:

  * `TyVar "a" mode`

### Fill in `Test/Poly/TypeModes.hs` with Phase 1 coverage

Add tests that directly exercise new behavior:

1. **Elaboration succeeds for cross-mode nesting**

   * doctrine with modes `C` and `V`
   * define `type A @C;`
   * define `type Thunk (a@C) @V;`
   * elaborate type expr `V.Thunk(C.A)`; assert mode is `V`

2. **Unqualified constructor ambiguity errors**

   * define `type A @C;` and `type A @V;`
   * attempt to elaborate raw `A` (as constructor) and assert error contains “ambiguous” and mentions qualifying with `Mode.`

3. **Argument mode mismatch errors**

   * same doctrine, attempt `V.Thunk(V.A)` and assert error mentions expected `C` but got `V`

4. **Unification rejects mode mismatch**

   * unify `TVar (a@C)` with `C.A` succeeds
   * unify `TVar (a@C)` with `V.SomeType` fails

### Update CLI golden outputs

**File:** `test/Test/CLI/Golden.hs`

If you change pretty-printing to show `Mode.Type` (likely), update all expected strings accordingly, e.g.:

* `A` → `M.A`
* `Hom(Unit, Bool)` → `M.Hom(M.Unit, M.Bool)` (depending on your chosen formatting)

### Run full test suite

* `stack test`

---

## Phase 1 acceptance criteria

* `stack test` passes.
* All `stdlib/*.llang` and `examples/*.llang` parse + elaborate.
* `examples/ccc_surface/*.run.llang` still work after syntax updates.
* `SPEC.md` updated in “Types” section:

  * mode-qualified constructors
  * mode signatures
  * mode-indexed tyvars
* `docs/MIGRATION.md` updated with concrete Phase 1 user-visible changes.

---

## Suggested implementation order inside Phase 1 (keeps build breaks localized)

1. Kernel: `TypeExpr` + `Doctrine` type table + `UnifyTy` + `Pretty`
2. Fix compile errors across kernel users (`Diagram`, `Rewrite`, etc.)
3. Update morphism traversal (`Morphism.hs`) and pushout (`Pushout.hs`)
4. Update parsers + raw AST (top-level + poly + surface)
5. Update elaboration (`Poly/DSL/Elab.hs`) and doctrine validation
6. Surface pipeline update (raw types → elaborate with doctrine; update prod/Hom usage)
7. Migrate stdlib/examples
8. Update tests + CLI goldens, then `stack test`

This order prevents getting stuck in a state where parsing and elaboration are both broken simultaneously.
