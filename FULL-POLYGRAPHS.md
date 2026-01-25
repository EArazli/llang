### What is still *not* the end-state polygraph kernel (expected at this point)

These are not “bugs” relative to Phase 0–3, but they are the core reasons you are not yet “fully migrated”:

* `Strat.Poly.Diagram` is still a **syntactic** composition/tensor tree, not a hypergraph.
* `Strat.Poly.Normalize` still normalizes by **round-tripping through old term rewriting** (diagram→term→old normalize→term→diagram).
* Structural operations are still partially special-cased (`GLDup/GLDrop/GLSwap`) rather than being ordinary doctrine generators + equations.

That’s exactly what the next stage must replace.

---

# Agent instructions: full migration to the polygraph kernel (correct + elegant; compatibility not prioritized)

Below is a concrete, no-fork plan that makes **polygraphs + mode theory** the real kernel, and moves the current term kernel to *legacy* status (kept only as an optional surface if you decide to keep it at all).

The guiding constraints you must enforce in code (kernel invariants):

1. **No implicit cartesianness** anywhere. Dup/drop/swap exist only if declared/imported as generators + equations.
2. **Diagrams are graphs** (open hypergraphs with ordered boundary), not op-trees.
3. Rewriting is **subdiagram rewriting** (DPO-style replacement with a dangling check), not “rewrite this AST node”.
4. Normalization strategy is deterministic (fuel-bounded), but correctness comes first.

---

## Milestone 1 — Replace `Diagram` with a real open hypergraph

### Goal

Make diagram composition/tensor definitional “by construction”, and make “occurrence of LHS inside G” a literal **subgraph match**, not a subtree.

### Hard decision (fixed)

Use an **open directed hypergraph with ports as vertices** and generator instances as hyperedges:

* Vertices = *ports* (wire endpoints).
* Hyperedge = one generator instance with ordered input port list and ordered output port list.
* Boundary = ordered list of input ports + ordered list of output ports.
* Linearity invariant: every port has **≤ 1 producer** and **≤ 1 consumer** edge. (Duplication requires explicit edges that produce multiple output ports.)

### Implementation steps

#### 1.1 Add a new module and types

Create:

`src/Strat/Poly/Graph.hs`

Define:

```haskell
newtype PortId = PortId Int deriving (Eq, Ord, Show)
newtype EdgeId = EdgeId Int deriving (Eq, Ord, Show)

data Edge = Edge
  { eId    :: EdgeId
  , eGen   :: GenName          -- generator symbol name
  , eIns   :: [PortId]         -- ordered
  , eOuts  :: [PortId]         -- ordered
  } deriving (Eq, Show)

data Diagram = Diagram
  { dMode     :: ModeName
  , dIn       :: [PortId]
  , dOut      :: [PortId]
  , dPortTy   :: IntMap TypeExpr
  , dProd     :: IntMap (Maybe EdgeId)   -- port -> producer
  , dCons     :: IntMap (Maybe EdgeId)   -- port -> consumer
  , dEdges    :: IntMap Edge
  , dNextPort :: Int
  , dNextEdge :: Int
  } deriving (Eq, Show)
```

Also define `validateDiagram :: Diagram -> Either Text ()` that checks:

* every `PortId` in `dIn/dOut` exists in `dPortTy`
* every edge’s ports exist
* `dProd/dCons` agree with `dEdges` incidence
* linearity (≤1 prod, ≤1 cons)
* mode consistency (all edges interpreted in `dMode`)

You must call `validateDiagram`:

* after `compose`
* after `tensor`
* after `rewriteStep`
* after `applyMorphism`

Fail fast with actionable errors.

#### 1.2 Replace `Strat.Poly.Diagram` exports

You currently have `Strat.Poly.Diagram` as an AST. Do this:

* Keep the module name `Strat.Poly.Diagram` (so import churn is manageable),
* Replace its internals to re-export the new `Diagram` from `Strat.Poly.Graph` and provide smart constructors:

```haskell
idD     :: ModeName -> Context -> Diagram
genD    :: Doctrine -> ModeName -> GenName -> Either Text Diagram
compD   :: Diagram -> Diagram -> Either Text Diagram
tensorD :: Diagram -> Diagram -> Either Text Diagram
diagramDom :: Diagram -> Context
diagramCod :: Diagram -> Context
```

**Fixed behavior:**

* `idD mode [A1..Ak]` creates fresh ports p1..pk, sets `dIn = [p1..pk]`, `dOut = [p1..pk]`, no edges.
* `genD` constructs an atomic edge with fresh ports for dom/cod, typed from the generator declaration.
* `tensorD` is disjoint union with boundary concatenation.
* `compD g f`:

  * require same mode
  * require `diagramCod f` and `diagramDom g` unify *exactly* (see Milestone 2 for type vars/unification)
  * glue outputs of `f` to inputs of `g` by port identification (port merge)

**Port identification (no ambiguity):**

* Do not “delete and redirect IDs”.
* Implement a `mergePorts :: Diagram -> PortId -> PortId -> Either Text Diagram` that:

  * checks same type
  * checks that combining incidences won’t violate linearity
  * replaces all occurrences of the “loser” PortId in `dIn/dOut` and in every edge incidence
  * merges `dPortTy`, `dProd`, `dCons`

Composition glues each `fOut[i]` with `gIn[i]` for i=0..n-1 using `mergePorts`.

---

## Milestone 2 — Make types first-class in the polygraph kernel (no Sort embedding)

### Goal

Eliminate `TySort Sort` as the kernel-level type universe. Types must be **mode-indexed objects**, not GAT sorts.

### Hard decision (fixed)

Implement a first-order type language with variables and constructors:

`src/Strat/Poly/TypeExpr.hs` becomes:

```haskell
newtype TyVar = TyVar Text deriving (Eq, Ord, Show)
newtype TypeName = TypeName Text deriving (Eq, Ord, Show)

data TypeExpr
  = TVar TyVar
  | TCon TypeName [TypeExpr]
  deriving (Eq, Ord, Show)

type Context = [TypeExpr]
```

You will still *optionally* keep the old GAT kernel later as a **surface** that elaborates to diagrams in a cartesian mode, but the core kernel must not embed it.

### Required new machinery: type unification

Add:

`src/Strat/Poly/UnifyTy.hs`

Implement:

```haskell
type Subst = Map TyVar TypeExpr

unifyTy  :: TypeExpr -> TypeExpr -> Either Text Subst
unifyCtx :: Context -> Context -> Either Text Subst
applySubstTy  :: Subst -> TypeExpr -> TypeExpr
applySubstCtx :: Subst -> Context -> Context
composeSubst   :: Subst -> Subst -> Subst
```

Rules:

* occurs check required (`a ~ TCon ... a ...` is rejected)
* deterministic error messages include the two types that failed

This unifier is used by:

* generator instantiation in diagram elaboration
* composition boundary checks
* rule matching (schematic rules)

---

## Milestone 3 — Redefine Doctrine as a multimodal polygraphic presentation

### Goal

A doctrine is not a GAT signature; it is:

* mode theory
* types per mode
* generators per mode (`Γ → Δ`)
* 2-cells between diagrams (rewrite/equations)
* optional 3-cells (later)

### Implementation steps

#### 3.1 Replace `Strat.Poly.Doctrine`

Make `Doctrine` the real one (stop calling it `Doctrine2`):

```haskell
data GenDecl = GenDecl
  { gdName    :: GenName
  , gdMode    :: ModeName
  , gdTyVars  :: [TyVar]     -- optional polymorphism
  , gdDom     :: Context
  , gdCod     :: Context
  }

data Cell2 = Cell2
  { c2Name   :: Text
  , c2Class  :: RuleClass
  , c2Orient :: Orientation
  , c2TyVars :: [TyVar]
  , c2LHS    :: Diagram
  , c2RHS    :: Diagram
  }

data Doctrine = Doctrine
  { dName       :: Text
  , dModes      :: ModeTheory
  , dTypes      :: Map ModeName (Map TypeName Int)  -- arity only
  , dGens       :: Map ModeName (Map GenName GenDecl)
  , dCells2     :: [Cell2]
  -- dCells3 later
  }
```

Validation function:

```haskell
validateDoctrine :: Doctrine -> Either Text ()
```

Checks:

* every referenced mode exists
* every type constructor exists and arities match
* every generator’s dom/cod types are well-formed
* every 2-cell has:

  * same mode on LHS/RHS
  * identical boundary contexts (up to alpha-renaming of type variables inside the cell’s scope)
  * LHS/RHS diagrams individually validate

#### 3.2 Structural libraries are ordinary doctrine modules

Remove `StructuralLib` enum and all special casing.

Create new stdlib doctrine files (these will become core “showcase” content):

* `stdlib/struct.planar.llang` (empty; the default discipline)
* `stdlib/struct.symmetric.llang` (declares `swap` + braid/symmetry equations)
* `stdlib/struct.cartesian.llang` (declares `dup`, `drop`, `swap` + commutative comonoid laws)

**Important:** these must be written using type variables so they apply generically.

Example generator declarations in cartesian library (syntax to be implemented in Milestone 6):

* `dup{a}  : [a] -> [a,a]`
* `drop{a} : [a] -> []`
* `swap{a,b}: [a,b] -> [b,a]`

Equations are 2-cells using diagram expressions.

---

## Milestone 4 — Implement real diagram rewriting (DPO-style) and normalization

This is the kernel centerpiece.

### Hard decision (fixed)

Implement rewrite steps as **open hypergraph replacement with boundary interface**:

A directed 2-cell `L -> R` rewrites `G` by:

1. finding a match of `L` into `G`
2. checking dangling condition
3. deleting the image of L’s internal edges/ports
4. gluing in a fresh copy of `R`’s internal edges/ports, identifying R’s boundary ports with the matched boundary ports

### 4.1 Pattern matching and match representation

Add:

`src/Strat/Poly/Match.hs`

Define:

```haskell
data Match = Match
  { mPorts :: Map PortId PortId    -- ports of LHS -> ports of G
  , mEdges :: Map EdgeId EdgeId    -- edges of LHS -> edges of G
  , mTySub :: Subst                -- type instantiation for schematic rules
  }
```

Implement:

```haskell
findFirstMatch
  :: Doctrine
  -> Diagram   -- lhs pattern (may have type variables)
  -> Diagram   -- host
  -> Either Text (Maybe Match)
```

Deterministic enumeration (fixed):

* Enumerate host edges by increasing `EdgeId` (insertion order).
* Enumerate pattern edges by increasing `EdgeId`.
* Pick the first pattern edge `e0`.
* Candidate host edges are those with the same generator name and same arities.
* For each candidate, attempt to extend to a full match via backtracking, always choosing:

  * the smallest unmapped adjacent edge next
  * the smallest compatible host edge for that next edge

Matching constraints:

* edge labels must match (`eGen`)
* incidence list lengths must match
* ordered incidence must match (this is planar strict, no implicit swapping)
* type constraints unify:

  * unify every pattern port type with host port type under accumulating substitution
  * apply substitution as you go

Dangling condition (fixed):

* Let `L_intPorts` = ports of L not in its boundary (`dIn` ∪ `dOut`).
* For each `p` in `L_intPorts`, let `p' = mPorts(p)` in host.
* Every incident edge of `p'` in host must be in the matched edge image:

  * producer edge (if any) must be matched
  * consumer edge (if any) must be matched
    If violated, the match is rejected.

### 4.2 Rewrite step application

Add:

`src/Strat/Poly/Rewrite.hs`

Implement:

```haskell
data RewriteRule = RewriteRule
  { rrName :: Text
  , rrLHS  :: Diagram
  , rrRHS  :: Diagram
  , rrTyVars :: [TyVar]
  }

rewriteOnce
  :: [RewriteRule]
  -> Diagram
  -> Either Text (Maybe Diagram)
```

Deterministic strategy (fixed):

* Iterate rules in the list order.
* For each rule, call `findFirstMatch`.
* Apply the first found match; return immediately.

Apply match:

1. Compute the host boundary ports corresponding to LHS boundary ports:

   * LHS boundary is `lhsIn ++ lhsOut` in order (store both separately)
2. Delete matched edges from host (`mEdges` image).
3. Delete matched internal ports (only those that are not in LHS boundary).
4. Instantiate RHS types using `mTySub` (apply substitution to RHS diagram port types).
5. Add RHS internal ports/edges with fresh IDs.
6. Identify RHS boundary ports with the matched boundary ports in host by boundary index.

Finally `validateDiagram` on result.

### 4.3 Normalization and joinability

Replace `Strat.Poly.Normalize` (wrapper) with real implementations:

```haskell
normalize
  :: Int              -- fuel
  -> [RewriteRule]
  -> Diagram
  -> Either Text (NormalizationStatus Diagram)

joinableWithin
  :: Int
  -> [RewriteRule]
  -> Diagram
  -> Diagram
  -> Either Text Bool
```

Normalization strategy (fixed):

* Repeat `rewriteOnce` until:

  * no rewrite applies → `Finished`
  * fuel hits 0 → `OutOfFuel` with current diagram

Joinability (fixed):

* BFS over diagrams, depth limited by fuel.
* At each node, generate all one-step rewrites by:

  * iterating rules
  * iterating matches in deterministic order and collecting up to a capped branching factor (set cap = 50 to prevent blowups; make it a constant and document it)
* Return true if you encounter a common diagram.

### 4.4 Test suite additions (mandatory)

Add a new test module:

`test/Test/Poly/Rewrite.hs`

Tests must include:

1. **Simple local rewrite:** monoid associativity reduces one step where applicable.
2. **Subdiagram rewrite not aligned to AST:** build a host diagram by composing/tensoring in a way where the LHS occurrence spans across previous composition boundaries; ensure it still matches (this proves you’re not doing subtree rewriting).
3. **Dangling rejection:** craft a host where an internal matched port has an external incidence; ensure match is rejected.
4. **Determinism:** run `normalize` twice and assert diagrams are structurally identical (including printed canonical form).

---

## Milestone 5 — Make the run pipeline operate on diagrams as the primary term

### Goal

Stop producing/consuming `Strat.Kernel.Syntax.Term` in the pipeline. The kernel term is now `Diagram`.

### Steps

1. Introduce:

`src/Strat/Frontend/RunPoly.hs`

Parallel to the old run module at first.

2. Define a new run spec target:

* `run` blocks can specify `doctrine` and `expr`, but expression is a **diagram expression**, not a term.
* You can temporarily drop `Surface2` from “mainline” runs; keep it as legacy until you later re-elaborate it into diagrams via boxes.

3. Update CLI to prefer poly runs:

* If a file contains poly runs, run those.
* If not, fall back to legacy behavior (optional; not required).

4. Output:

* Print “normalized:” followed by a canonical textual diagram form.
* For show-off, also print `edges:` lines (sorted by edge id) in debug mode or under a `ShowDebug` flag.

Add golden tests for poly examples (see Milestone 8).

---

## Milestone 6 — Polygraph DSL: parse and elaborate doctrines + diagram expressions

### Goal

Users can define:

* modes/types/generators
* diagram 2-cells (rules)
* runs that use diagram expressions directly

### Hard decision (fixed)

Add new top-level keyword: `polydoctrine`.

Do not overload the existing `doctrine` keyword yet; this reduces churn and lets you keep legacy tests until you’re confident.

### DSL features to implement (minimum viable, unambiguous)

#### 6.1 Polydoctrine block

Grammar (concrete):

```
polydoctrine <Name> [extends <Name>] where {
  mode <ModeName>;
  type <TypeName> [<tyvar> ...] @<ModeName>;
  gen  <GenName>  [<tyvar> ...] : <Ctx> -> <Ctx> @<ModeName>;
  rule <class> <RuleName> <orient> [<tyvar> ...] : <Ctx> -> <Ctx> @<ModeName> =
    <DiagExpr> == <DiagExpr>;
}
```

Where:

* `<Ctx>` is `[<Ty>, <Ty>, ...]` or `[]`
* `<Ty>` is:

  * lowercase identifier = `TVar` (type variable)
  * uppercase identifier optionally with `(<Ty>,...)` = `TCon`
* `<DiagExpr>` is:

  * `id[<Ctx>]`
  * `<GenName>` optionally with type args `{T1,T2,...}` (if given, use to instantiate `gdTyVars`)
  * composition: `<d1> ; <d2>` meaning “first d1 then d2”
  * tensor: `<d1> * <d2>` meaning parallel
  * parentheses

#### 6.2 Elaborator responsibilities

In `Strat.Poly.DSL.Elab`:

* Build a `Doctrine` from parsed declarations.
* For each `gen` decl: store a `GenDecl`.
* For each `rule`:

  * parse and elaborate both diagram expressions into `Diagram`
  * during elaboration, **instantiate generator occurrences** by unifying their declared dom/cod with the surrounding required boundary types
  * allow rule-scoped type variables
  * ensure final LHS and RHS boundaries match the declared `Ctx -> Ctx`

This requires type inference + unification during elaboration:

* Each generator occurrence gets fresh metavariables for its type parameters.
* Composition glues boundaries and unifies port types.
* At the end, apply solved substitution; reject if unsolved metas remain in a concrete run expression.

### Test suite changes

Add `test/Test/Poly/DSL.hs`:

* parse+elab the new monoid doctrine
* validate doctrine succeeds
* normalize a known diagram expression and compare with expected canonical print

---

## Milestone 7 — Morphisms between polygraph doctrines

### Goal

Implement `F : D → E` as structure-preserving translation:

* mode map (initially: require identity to keep it small; extend later)
* type constructor map
* generator map to diagrams
* equation preservation check by normalization/joinability in target

### Fixed scope for first complete implementation

* Mode mapping must be identity (`m ↦ m`) initially.
* Type mapping supports only renaming constructors + mapping parameters structurally.
* Generator mapping maps each generator symbol to a diagram expression in the target.

You can generalize to full mode theory later, but get the kernel stable first.

### Implementation steps

1. New module:

`src/Strat/Poly/Morphism.hs`

2. Define:

```haskell
data Morphism = Morphism
  { morName   :: Text
  , morSrc    :: Doctrine
  , morTgt    :: Doctrine
  , morTypeMap :: Map TypeName TypeExpr
  , morGenMap  :: Map GenName Diagram
  , morPolicy  :: RewritePolicy
  , morFuel    :: Int
  }
```

3. Implement:

* `applyMorphismDiagram :: Morphism -> Diagram -> Either Text Diagram`

  * replace each edge by its image diagram and glue at boundary ports
  * reuse the same splice mechanism as rewriting

* `checkMorphism :: Morphism -> Either Text ()`

  * for each source 2-cell `α: L == R`:

    * compute `F(L)` and `F(R)`
    * check joinable/convertible within `morFuel` under target rewrite system compiled from `morPolicy`

4. Add tests:

* A morphism from `Monoid` to `StringMonoidModel` that maps:

  * `mul` to string concatenation generator
  * `unit` to empty string generator
* Check morphism succeeds and running a closed diagram yields expected normalized form/value (see Milestone 9 for evaluation).

---

## Milestone 8 — Update example suite to show off the new system

### Required changes

Create a new directory:

`examples/poly/`

Add a new `examples/poly/README.md` explaining what each example demonstrates (explicitly: no implicit swap/dup/drop).

### Example set (minimum)

1. **Planar monoid (no swap/dup/drop)**

   * `examples/poly/planar_monoid.poly.llang`
   * `examples/poly/planar_monoid.run.llang`

Shows:

* generators `mul, unit`
* associativity/unit rewrite rules
* run normalizing a closed diagram like:

  * `(unit * unit) ; mul` (closed)
  * `((unit * unit) ; mul * unit) ; mul` etc

2. **Cartesian monoid (imports cartesian struct library)**

   * `examples/poly/cart_monoid.poly.llang`
   * `examples/poly/cart_monoid.run.llang`

Shows:

* imports/extends `planar_monoid`
* imports `stdlib/struct.cartesian.llang`
* defines a derived diagram `square = dup{A} ; mul`
* run normalizing `square ; square` etc

3. **“You can’t do that without dup”: negative example**

   * `examples/poly/no_dup_error.run.llang`

Attempt to type-check or elaborate:

* `mul ; ...` from `[A]` without providing an extra input
  Expect a clear error: “boundary mismatch: expected [A,A], got [A]” (or similar).

Write a test that asserts this failure message (don’t put it in golden output as a normal run; make it a unit test).

4. **Subdiagram rewrite showcase**

   * `examples/poly/subdiagram_match.poly.llang`
   * includes a rule that matches a non-subtree occurrence and proves the graph matcher is real.

### Golden tests update

Update `test/Test/CLI/Golden.hs`:

* Replace or supplement existing golden runs with:

  * `examples/poly/planar_monoid.run.llang`
  * `examples/poly/cart_monoid.run.llang`

The expected outputs must include at least:

* printed normalized diagram form

If you keep value evaluation, include value output too.

---

## Milestone 9 — (Optional but recommended) Evaluation of diagrams via “model doctrine” morphisms

### Goal

Demonstrate “compiler/backend/model is just a morphism”.

Implement a simple target doctrine `Target.String` with base type `Str` and generators:

* `empty : [] -> [Str]`
* `append : [Str,Str] -> [Str]`

Then a model morphism `Monoid → Target.String` maps:

* `A ↦ Str`
* `unit ↦ empty`
* `mul ↦ append`

Evaluation becomes:

* normalize in target doctrine (optional)
* interpret distinguished generators as host functions producing `Value`

You can keep your existing `Strat.Backend.Value` machinery; just update it to work on diagrams instead of terms:

* interpret each generator as a host function `[Value] -> [Value]`
* evaluate diagram in topological order
* require closed diagram for now (empty input boundary)

This is enough to “show off” the new architecture without rewriting Surface2 yet.

---

## Milestone 10 — Boxes + hierarchical rewriting (final core feature)

Do this last; it’s the highest complexity.

### Fixed representation

Extend `Edge` with an optional box payload:

```haskell
data EdgePayload
  = PGen GenName
  | PBox BoxName Diagram   -- internal diagram + label
```

Rewriting must:

* allow matches inside boxes
* allow rules whose LHS/RHS include boxes (optional initially)

Deterministic match order:

* outer diagram edges by id
* when visiting a box edge, recursively search inside it before moving to next outer edge (“outermost-leftmost”)

Add at least one example:

* a boxed “function” diagram
* a beta-like rewrite rule that rewrites a box application

Update `SPEC.md` to include boxes at this point.

---

# Documentation requirements (must-do at each milestone)

## SPEC.md rewrite strategy (no ambiguity)

As soon as Milestone 4 is complete (real diagram rewriting), you must:

1. Move the current GAT/kernel spec to `SPEC-LEGACY.md`.
2. Rewrite `SPEC.md` to make the polygraph kernel primary:

   * Mode theory
   * types per mode
   * contexts as ordered lists
   * generators `Γ → Δ`
   * diagrams as open hypergraphs
   * 2-cells and DPO rewriting
   * normalization + joinability algorithms (with determinism strategy)
   * morphisms and their checking
   * composition (extends/pushouts) once implemented
3. Keep a short section “Legacy kernel” that states it exists only as a surface/compat layer (or has been removed).

Also update:

* `examples/README.md` to include the new `examples/poly/*` suite prominently and label older examples as legacy if you keep them.

---

# Immediate next actions for the agent (what to start coding now)

1. Implement Milestone 1 (hypergraph Diagram) + `validateDiagram`.
2. Implement Milestone 2 (new TypeExpr + unify).
3. Implement Milestone 4 (rewriteOnce + normalize + joinableWithin) **before** building the DSL—hardcode one doctrine/rule in a unit test first to validate the engine.
4. Only then implement Milestone 6 (polydoctrine DSL) and start writing the new examples.
5. Update `SPEC.md` once the rewrite engine is real; until then, keep it clearly marked as “compat wrapper”.

This sequence minimizes time spent debugging parsing/elaboration while the core rewriting semantics are still unstable.
