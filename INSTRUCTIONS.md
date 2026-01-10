# System outline (all layers)

Goal: a modular “language workbench” where any doctrine (categorical / compositional structure) can be defined as a library artifact, equipped (optionally) with rewrite orientation + coherence data, and then used by arbitrary surface syntaxes and backends. No doctrine is special-cased in the core. The core provides generic machinery; doctrines get nicer automation only when their authors provide more structure.

## Layers

### Layer M (Meta / Kernel: presented rewriting 2-theories)

What it is: a generic engine for:
- presenting theories as generators + equations, optionally oriented as rewrite rules
- rewriting, normalization (when possible)
- critical pair (branching) enumeration
- coherence obligations (join requirements), and a place to store/validate joiners
- separation of rules into “structural vs computational” for relative coherence

What it does **not** assume: CCC, STLC, lambda calculus, any particular doctrine.

### Layer D (Doctrine libraries)

A doctrine is just data built using Layer M:
- signature-ish data (optional early on)
- a set of equations/rules with metadata (orientation, structural/computational, invertible)
- optional extra: termination order, completion hints, joiners

Output: a `Presentation` that Layer M can analyze/compile into a `RewriteSystem`.

### Layer S (Surface syntaxes)

Surface ASTs, binding, contexts, elaboration:
- parameterized by a doctrine (Layer D) and a context kit (later)
- elaboration yields “core terms” (1-cells) in the doctrine’s generated language

For now: stub.

### Layer B (Backends / models)

Interpretation of doctrine generators into a concrete target:
- interpreter or codegen to Haskell, circuits, IR, etc.
- must respect the doctrine’s equations (as proofs or validated tests)

For now: stub.

---

# Haskell project scaffolding

Single Cabal package to start:

```
src/
  Strat/
    Meta/...
    Doctrine/Stub.hs
    Syntax/Stub.hs
    Model/Stub.hs

test/
  Strat/MetaSpec.hs
```

Suggested deps (keep minimal):
- base, containers, text
- optional: mtl (builder/state), prettyprinter (debug printing)
- tests: tasty, tasty-hunit

---

# Layer M (Meta) — implement now

## Design constraints (so you won’t rewrite this layer later)

1) **Term representation must be abstract.**
Rewriting/coherence algorithms must work over any term language that can supply:
- subterm positions
- substitution application
- matching (for rewriting)
- unification (for critical pairs), if available

When you later add binders / dependent structure, you implement a new `TermLike` instance (or new term type) rather than rewriting the meta engine.

2) **Rules carry metadata.**
This is where “relative coherence” and “structural vs computational” live. The meta engine uses metadata to decide which branchings produce which obligations.

3) **Outcomes are graded, not binary.**
- If a term language supplies unification, you can compute critical pairs automatically.
- If not, the engine still supports rewriting + manual joiners; critical pairs are “unknown/uncomputed”.

---

# Module map (Layer M)

## `Strat.Meta.Types`

Basic identifiers and shared types:

```hs
module Strat.Meta.Types where

import Data.Text (Text)

data RuleDir = DirLR | DirRL
  deriving (Eq, Ord, Show)

data RuleId = RuleId
  { ridEq  :: Text    -- eqName, must be unique within a Presentation
  , ridDir :: RuleDir
  } deriving (Eq, Ord, Show)

-- Tree positions: [] = root, [i,j] = child i then child j
type Pos = [Int]

data RuleClass = Structural | Computational
  deriving (Eq, Ord, Show)

data Orientation = LR | RL | Bidirectional | Unoriented
  deriving (Eq, Ord, Show)
```

## `Strat.Meta.Term.Class`

Abstract interface for term languages.

Key idea: algorithms depend on these, not on a specific AST.

```hs
{-# LANGUAGE TypeFamilies #-}
module Strat.Meta.Term.Class where

import Strat.Meta.Types
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- Generic substitution mapping variables to terms
newtype Subst t = Subst { unSubst :: M.Map (Var t) t }
  deriving (Eq, Show)

class (Eq t, Ord (Var t)) => TermLike t where
  type Var t

  -- Observe term shape
  isVar   :: t -> Bool
  asVar   :: t -> Maybe (Var t)

  -- Enumerate positions (include [] by convention)
  positions :: t -> [Pos]

  subtermAt  :: t -> Pos -> Maybe t
  replaceAt  :: t -> Pos -> t -> Maybe t

  vars :: t -> S.Set (Var t)

  -- Apply a substitution to a term (recursive / homomorphic)
  applySubst :: Subst t -> t -> t

  -- Rename variables (used to alpha-rename rules apart if needed)
  renameVars :: (Var t -> Var t) -> t -> t

-- For rewriting: match(pattern, target) instantiates vars in pattern
class TermLike t => Matchable t where
  match :: t -> t -> Maybe (Subst t)

-- For critical pairs: unify(t1, t2) instantiates vars in both terms
-- If a term language cannot support unification, you can omit this instance
class TermLike t => Unifiable t where
  unify :: t -> t -> Maybe (Subst t)

-- For rule-scoped variables
class ScopedVar v where
  setNs :: Ns -> v -> v
```

Notes:
- `positions/subtermAt/replaceAt` are required methods because later term representations (binders) won’t have “obvious” structural recursion.
- `renameVars` allows rule-variable scoping strategies (see below).

## `Strat.Meta.Term.FO`

A concrete first-order term instance for early testing. Later, you add new instances (e.g., second-order/binding) without touching the meta engine.

```hs
module Strat.Meta.Term.FO where

import Strat.Meta.Term.Class
import Strat.Meta.Types
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Text (Text)

data Ns = Ns { nsRule :: RuleId, nsInst :: Int }
  deriving (Eq, Ord, Show)

newtype Sym = Sym Text
  deriving (Eq, Ord, Show)

data V = V { vNs :: Ns, vLocal :: Int }
  deriving (Eq, Ord, Show)

data Term
  = TVar V
  | TApp Sym [Term]
  deriving (Eq, Ord, Show)

instance TermLike Term where
  type Var Term = V

  isVar (TVar _) = True
  isVar _        = False

  asVar (TVar v) = Just v
  asVar _        = Nothing

  positions t = go [] t
    where
      go p (TVar _)     = [p]
      go p (TApp _ as)  = p : concat [ go (p ++ [i]) a | (i,a) <- zip [0..] as ]

  subtermAt = ...        -- implement via recursion on Pos
  replaceAt = ...        -- implement via recursion on Pos

  vars (TVar v)    = S.singleton v
  vars (TApp _ as) = S.unions (map vars as)

  applySubst (Subst s) tm =
    case tm of
      TVar v -> case M.lookup v s of
        Nothing -> tm
        Just t  -> applySubst (Subst s) t
      TApp f as -> TApp f (map (applySubst (Subst s)) as)

  renameVars f tm =
    case tm of
      TVar v     -> TVar (f v)
      TApp h as  -> TApp h (map (renameVars f) as)

instance ScopedVar V where
  setNs ns v = v { vNs = ns }

instance Matchable Term where
  match = ...   -- standard FO pattern matching

instance Unifiable Term where
  unify = ...   -- standard FO unification with occurs-check
```

## `Strat.Meta.Rule`

Rules/equations plus metadata.

```hs
module Strat.Meta.Rule where

import Strat.Meta.Types
import Strat.Meta.Term.Class
import Data.Text (Text)

data Equation t = Equation
  { eqName   :: Text
  , eqClass  :: RuleClass
  , eqOrient :: Orientation
  , eqLHS    :: t
  , eqRHS    :: t
  } deriving (Eq, Show)

-- Oriented rule used by the rewrite engine
-- ruleIx is deterministic iteration order only (not identity)
data Rule t = Rule
  { ruleId    :: RuleId
  , ruleIx    :: Int
  , ruleName  :: Text
  , ruleClass :: RuleClass
  , lhs       :: t
  , rhs       :: t
  } deriving (Eq, Show)
```

## `Strat.Meta.Presentation`

A doctrine/presentation is just a set of equations plus build helpers.

```hs
module Strat.Meta.Presentation where

import Strat.Meta.Rule
import Strat.Meta.Types
import Data.Text (Text)

data Presentation t = Presentation
  { presName     :: Text
  , presEqs      :: [Equation t]
  } deriving (Eq, Show)

-- Later: add optional fields like precedence/orderings, completion hints, etc.
```

## `Strat.Meta.RewriteSystem`

Compile a Presentation into a set of oriented rewrite rules (possibly several “views” depending on policy).

```hs
module Strat.Meta.RewriteSystem where

import Strat.Meta.Rule
import Strat.Meta.Presentation
import Strat.Meta.Types
import qualified Data.Map.Strict as M

-- Ordered for deterministic iteration, map for lookup

data RewriteSystem t = RewriteSystem
  { rsRules   :: [Rule t]
  , rsRuleMap :: M.Map RuleId (Rule t)
  } deriving (Eq, Show)

lookupRule :: RewriteSystem t -> RuleId -> Maybe (Rule t)
getRule    :: RewriteSystem t -> RuleId -> Rule t
rulesInOrder :: RewriteSystem t -> [Rule t]

-- A policy is needed because not all equations are oriented or safe for normalization

data RewritePolicy
  = UseOnlyComputationalLR
  | UseStructuralAsBidirectional
  | UseAllOriented
  deriving (Eq, Show)

-- Reject duplicate eqName values (unique identity required)
compileRewriteSystem :: RewritePolicy -> Presentation t -> Either Text (RewriteSystem t)
```

**Policy semantics:**
- `UseStructuralAsBidirectional`
  - If `eqClass == Structural`, **always** generate two rules: `lhs -> rhs` and `rhs -> lhs` (even if `eqOrient` is `Unoriented`).
  - If `eqClass == Computational`, honor `eqOrient`:
    - `LR` => one rule `lhs -> rhs`
    - `RL` => one rule `rhs -> lhs`
    - `Bidirectional` => two rules
    - `Unoriented` => skip
- Deterministic ordering: equation order in `presEqs`, then direction order `LR` then `RL`.

## `Strat.Meta.Rewrite`

Rewriting engine over Matchable terms.

```hs
module Strat.Meta.Rewrite where

import Strat.Meta.Types
import Strat.Meta.Rule
import Strat.Meta.RewriteSystem
import Strat.Meta.Term.Class

data Step t = Step
  { stepRule  :: RuleId
  , stepPos   :: Pos
  , stepSubst :: Subst t
  } deriving (Eq, Show)

data Redex t = Redex
  { redexStep :: Step t
  , redexFrom :: t
  , redexTo   :: t
  } deriving (Eq, Show)

-- All one-step rewrites from a term
rewriteOnce :: Matchable t => RewriteSystem t -> t -> [Redex t]

applyStep :: TermLike t => (RuleId -> Rule t) -> Step t -> t -> Maybe t

-- Normalization with a step limit (since termination is not guaranteed)
data Strategy = FirstRedex

normalizeWith :: Matchable t => Strategy -> Int -> RewriteSystem t -> t -> t
normalize     :: Matchable t => Int -> RewriteSystem t -> t -> t
normalize = normalizeWith FirstRedex
```

Notes:
- `applyStep` is strict: it checks that `applySubst subst (lhs rule)` matches the subterm at `stepPos`, then replaces with `applySubst subst (rhs rule)`, else fails.
- `rewriteOnce` order is deterministic:
  1) by `rsRules` order (compiled order), then
  2) by position order (lexicographic on `Pos`, with `[]` first, consistent with `positions`).
- `normalizeWith FirstRedex`: repeatedly takes the first redex from `rewriteOnce`.

## `Strat.Meta.CriticalPairs`

Critical pair enumeration is where unification is required. If Unifiable isn’t available, you can return [] or `Left NotSupported`.

```hs
module Strat.Meta.CriticalPairs where

import Strat.Meta.Rule
import Strat.Meta.RewriteSystem
import Strat.Meta.Types
import Strat.Meta.Term.Class

-- For scoped variables in overlaps
import Strat.Meta.Term.FO (Ns(..))


data CriticalPair t = CriticalPair
  { cpRule1   :: RuleId
  , cpRule2   :: RuleId
  , cpPosIn2  :: Pos
  , cpPeak    :: t
  , cpLeft    :: t
  , cpRight   :: t
  , cpMgu     :: Subst t
  } deriving (Eq, Show)

-- Controls which overlaps matter (relative coherence)
data CPMode
  = CP_All
  | CP_OnlyStructural
  | CP_StructuralVsComputational
  deriving (Eq, Show)

criticalPairs
  :: (Unifiable t, TermLike t)
  => CPMode
  -> (RuleId -> Rule t)     -- lookup
  -> RewriteSystem t
  -> [CriticalPair t]
```

Algorithm sketch (FO standard):
- For each ordered pair of rules `(r1, r2)` (including self-pairs)
- Freshen rule variables into disjoint namespaces:
  - `r1` renamed with `setNs (Ns (ruleId r1) 0)`
  - `r2` renamed with `setNs (Ns (ruleId r2) 1)`
- For each position `p` in `lhs(r2)` where the subterm is **not a variable**
- Compute `mgu <- unify (lhs r1) (subtermAt (lhs r2) p)`
- Let `peak  = applySubst mgu (lhs r2)`
- Let `left  = applySubst mgu (replaceAt (lhs r2) p (rhs r1))`
- Let `right = applySubst mgu (rhs r2)`
- Record `(peak -> left, peak -> right)` as a critical pair

**CPMode filtering:**
- `CP_All`: include all pairs (including self-pairs) and root overlaps; exclude variable overlaps.
- `CP_OnlyStructural`: include only `(Structural, Structural)` pairs.
- `CP_StructuralVsComputational`: include only mixed pairs `(Structural, Computational)` and `(Computational, Structural)`.

## `Strat.Meta.Coherence`

This stores obligations and (optional) joiners.

```hs
module Strat.Meta.Coherence where

import Strat.Meta.CriticalPairs
import Strat.Meta.Rewrite
import Strat.Meta.RewriteSystem
import Strat.Meta.Rule
import Strat.Meta.Types
import Strat.Meta.Term.Class
import qualified Data.Map.Strict as M

data ObligationKind = NeedsJoin | NeedsCommute
  deriving (Eq, Show)

data Obligation t = Obligation
  { obKind  :: ObligationKind
  , obPair  :: CriticalPair t
  } deriving (Eq, Show)

-- A joiner is a “confluence diagram”: left ->* join <-* right
data Joiner t = Joiner
  { joinTerm :: t
  , leftDerivation  :: [Step t]
  , rightDerivation :: [Step t]
  } deriving (Eq, Show)

newtype JoinDB t = JoinDB (M.Map (RuleId, RuleId, Pos) (Joiner t))

obligationsFromCPs :: [CriticalPair t] -> [Obligation t]

-- Validation: do the derivations actually rewrite to joinTerm?
validateJoiner
  :: Matchable t
  => (RuleId -> Rule t)
  -> RewriteSystem t
  -> CriticalPair t
  -> Joiner t
  -> Bool
```

**Validation behavior (real check):**
- Start from `cpLeft`, replay `leftDerivation` step-by-step using `applyStep`.
- Confirm the final term equals `joinTerm`.
- Repeat from `cpRight` with `rightDerivation`.
- Return `True` only if both sides reach `joinTerm` successfully.

---

# Rule variable scoping

Option A is required: **rule-local variables carry a scope**.

- Use `Ns { nsRule :: RuleId, nsInst :: Int }` as a namespace.
- In critical pairs, always rename variables into disjoint namespaces, even when rule IDs differ.

This avoids freshening pain later and makes self-overlaps well-defined.

---

# Minimal example (for testing the meta layer)

Start with a tiny FO rewrite system that has real overlaps.

Example: monoid right-association + unit elimination (terminating in practice on left-nesting)

Terms:
- `e` constant
- `m(x,y)` binary

Rules (Computational or Structural—your choice; this is just a test):
- `m(e, x) -> x`
- `m(x, e) -> x`
- `m(m(x,y), z) -> m(x, m(y,z))`  (right associate)

This creates critical pairs like `m(m(e,x), y)` etc.

In `Strat.Meta.Examples.Monoid`:
- build `Presentation Term`
- compile with `RewritePolicy`
- compute `criticalPairs`
- print obligations

Test file asserts:
- non-empty critical pairs
- normalize reduces some sample term

---

# Stubs for lower layers (compile-time placeholders)

## `Strat.Doctrine.Stub`

```hs
module Strat.Doctrine.Stub where

import Strat.Meta.Presentation

-- Eventually: richer doctrine API. For now: doctrine = presentation.
newtype Doctrine t = Doctrine { doctrinePres :: Presentation t }
```

## `Strat.Syntax.Stub`

```hs
module Strat.Syntax.Stub where

-- Eventually: presheaf/second-order syntax + elaboration.
data SurfaceTerm = SurfaceStub
```

## `Strat.Model.Stub`

```hs
module Strat.Model.Stub where

-- Eventually: interpretation of doctrine terms into a backend.
data Backend = BackendStub
```

---

# Implementation order (Layer M)

1) Implement Types, Rule, Presentation.
2) Implement FO Term + Matchable + Unifiable.
3) Implement Rewrite (rewriteOnce, normalize with fuel).
4) Implement CriticalPairs using unify.
5) Implement Coherence obligation generation + joiner validation.
6) Add one example + a few tests.

---

# Tests (tasty + tasty-hunit)

Required tests (small but real):
- Monoid example:
  - `criticalPairs` is non-empty
  - `normalize` reduces a sample term deterministically
- Matching sanity: expected substitution
- Unification sanity, including an occurs-check failure
- `applyStep` strict failure on mismatched substitution/position
- `validateJoiner` succeeds for a simple hand-constructed joiner

---

# Checklist (implementation progress)

- [ ] Update `Strat.Meta.Types` with stable `RuleId`, `RuleDir`
- [ ] Add `ScopedVar` class and `Ns` namespace type
- [ ] Update FO term (`V`, `Term`) and instances (`TermLike`, `Matchable`, `Unifiable`)
- [ ] Implement `Strat.Meta.Rule` with `ruleIx`
- [ ] Implement `RewriteSystem` (`rsRules`, `rsRuleMap`, lookup helpers)
- [ ] Implement `compileRewriteSystem` with duplicate `eqName` check
- [ ] Implement `rewriteOnce`, `applyStep` (strict), `normalizeWith`
- [ ] Implement `criticalPairs` with freshened namespaces + CPMode filtering
- [ ] Implement `Coherence` obligations + real `validateJoiner`
- [ ] Add monoid example
- [ ] Add tests (tasty + tasty-hunit)

