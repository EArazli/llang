Implementation specification: kernel cleanup + modular doctrines + principled interfaces + faithful (SO)GATs + useful semantics

Clarifications added (2026-01-16)
	•	Morphism checking: add optional check { policy; fuel; } stanza on morphisms; defaults policy=UseStructuralAsBidirectional, fuel=200. Morphism validity is not run-dependent; runs may skip re-checking only if morphisms were already checked with their own policy/fuel.
	•	Include collisions: detect equation name collisions during include-merge; allow only α-equivalent duplicates, else error DuplicateEquationName. (Same policy as sorts/ops.)
	•	SOGAT v1 restriction: reject any binder term variable occurrence inside Ty-sorted indices (e.g. Tm(B) where B mentions the bound var). Error SOGAT_V1_DependentTypeNotSupported.
	•	Derived contexts override: generate only missing components (ctxObj/proj/var rule), derive dependencies as needed; if derivation requires missing interface slots, error DeriveContextsFailed.

Answers to open questions (recorded)
	•	Morphism checking: declaration-local check { policy; fuel; } with defaults UseStructuralAsBidirectional / 200; run blocks must not override.
	•	Include collisions: equation name collisions are idempotent only if α-equivalent after renaming; otherwise error.
	•	SOGAT v1 restriction: reject any bound term variable appearing in Ty-sorted indices; error SOGAT_V1_DependentTypeNotSupported.
	•	Derived contexts: derive only missing ctxObj/proj/var rule; derive dependencies as needed; error if required interface slot missing.

0. Target end-state and acceptance criteria

End-state goals
	1.	Kernel supports full first-order GATs (including dependent sort constructors via telescopes).
	2.	Doctrine modularity is real: no duplication of sort/op declarations just to reference them; doctrines can include/extend/import other doctrines.
	3.	Interfaces are principled (not hard-coded): an “interface” is a checked morphism of presentations (sort/op mapping + equation preservation check), and surfaces reference interface slots without hacks (slotKey/suffix tricks removed).
	4.	Surface elaboration is declarative: rule ordering no longer changes results; ambiguities are detected and reported.
	5.	Second-order GATs are implemented as a presentation layer and give boilerplate reduction (at minimum: binder-aware signatures + derived context/product machinery for CCC compilation).
	6.	Results can be read back to useful values: the system can report true for (\x.x) true, not only a categorical combinator.

Acceptance criteria (verifiable)
	•	All existing tests pass after updating fixtures, plus new tests listed in §8.
	•	Updated examples load and run. In particular:
	•	examples/ccc_surface/stlc.run.llang prints a result line containing true for (lam x:Bool. x) true.
	•	Doctrines like monoid.llang and ccc.llang no longer repeat the same core declarations; instead they use include/extends.
	•	Surface rule order is irrelevant for deterministic surfaces: swapping rule order yields identical elaboration result; overlapping rules trigger an ambiguity error.

⸻

1. Kernel: faithful first-order GATs (dependent sort constructors)

Problem being fixed

Sort constructors currently take a list of parameter sorts ([Sort]) and cannot depend on earlier parameters. This blocks faithful GAT presentations where sort indices depend on previous indices.

Required change: Sort constructors use a telescope

Data structure changes
In src/Strat/Kernel/Signature.hs:

Before

data SortCtor = SortCtor
  { scName :: SortName
  , scParamSort :: [Sort]
  }

After

data SortCtor = SortCtor
  { scName :: SortName
  , scTele :: [Binder]   -- telescope (v : Sort), later sorts may depend on earlier vars
  }

Invariants
	•	For SortCtor scName scTele, each binder var v in scTele has:
	•	varScope == ScopeId ("sort:" <> renderSortName scName)
	•	varLocalIx is 0..(n-1) in order.
	•	Binder sorts in scTele may reference earlier binder vars (dependency).
	•	No other free variables are allowed in binder sorts.

mkSort must become dependency-aware
In Signature.hs, re-implement mkSort to type-check sort indices sequentially (mirroring mkOp).

Sketch:

mkSort :: Signature -> SortName -> [Term] -> Either SortError Sort
mkSort sig sName args = do
  ctor <- lookupSortCtor sig sName
  let tele = scTele ctor
  when (length args /= length tele) $
    Left (WrongSortArgCount sName (length tele) (length args))
  go emptySubst 0 tele args
  pure (Sort sName args)
 where
  go subst _ [] [] = pure ()
  go subst i (Binder v expected : tele') (t:ts) = do
    let expected' = applySubstSort subst expected
    actual <- termSort sig t
    if actual == expected'
      then go (extendSubst subst v t) (i+1) tele' ts
      else Left (SortParamSortMismatch sName i expected' actual)
  go _ _ _ _ = impossible

Update validation
In src/Strat/Kernel/Presentation.hs:
	•	Replace validateSortCtor logic with telescope validation analogous to validateTele for ops:
	•	validate binder scopes and contiguous locals
	•	validate binder sorts under earlier binders

Update signature merging and renaming
Anywhere scParamSort is used, update to telescope-aware logic:
	•	mergeSortCtors must compare sort ctors up to α-equivalence on binder vars (scope-local differences across instantiations).
	•	renameSortsSignature must also rename binder var scopes to match renamed sort ctor names (analogous to renameOpsDecl updating "op:" scope).

Define:

alphaEqSortCtor :: SortCtor -> SortCtor -> Bool

by renaming binders of one to the other and comparing binder sorts structurally.

⸻

2. Doctrine modularity: include / extends inside doctrine blocks

Problem being fixed

Doctrines duplicate declarations because a doctrine block can’t reference symbols from another doctrine at definition time.

New surface syntax

Inside a doctrine ... where { ... } block, allow:

include <doctrine-expr>;

Also allow sugar:

doctrine Ext extends Base where { ... }

Semantics: extends Base is equivalent to the first item being include Base;.

AST changes

In src/Strat/Kernel/DSL/AST.hs:
	•	Add to RawItem:
	•	RawInclude RawExpr

Parser changes

In src/Strat/Kernel/DSL/Parse.hs:
	•	Add a parser alternative for doctrine items: include followed by a doctrine expression.

Elaboration changes

In src/Strat/Kernel/DSL/Elab.hs:
	•	Modify elabPresentation to process items sequentially with an accumulating presentation (sig, eqs):
	•	On include expr:
	1.	Elaborate expr to a Presentation using the existing doctrine-expr evaluation pipeline.
	2.	Merge it into the accumulator before continuing.
	•	On sort/op/equation items:
	•	elaborate against the current accumulator signature (so included symbols are in scope).

Collision semantics
	•	If include introduces a symbol name already present:
	•	If α-equivalent (for sort ctors / ops) → OK (no duplicate).
	•	Otherwise → hard error DuplicateSymbol with both definitions printed.

This makes “spurious duplication to reference things” impossible and forces explicit qualification if the user intends different symbols.

⸻

3. Interfaces: replace hard-coded interface kinds with checked morphisms of presentations

Problems being fixed
	•	Built-in interface kinds (CCC, CCC_Bool) are hard-coded in Haskell.
	•	Surface references use a suffix hack (slotKey) rather than a principled namespace.
	•	Interface “instances” don’t behave like real theory morphisms.

New conceptual model
	•	An interface is just a source doctrine I (a presentation: sorts, ops, equations).
	•	An interface instance is a morphism of presentations I → D where D is the run doctrine:
	•	maps sort constructors and ops
	•	and preserves equations (checked via joinability in D’s rewrite theory)

DSL changes

A. Surface requires becomes explicit and names its alias
In a surface block:

requires ccc : CCC_Bool;

	•	ccc is an alias used as a namespace in core expressions.
	•	CCC_Bool is a normal doctrine name or doctrine expression.

B. Define morphisms at top-level
Replace the old interface ... for doctrine ... construct with:

morphism CCCIface : CCC_Bool -> CCC where {
  sort Obj = Obj;
  sort Hom = Hom;

  op id   = id;
  op comp = comp;
  ...
}

Rules:
	•	Total on source sorts/ops (unless you add an explicit default rule; see below).
	•	“Identity by name” may be allowed as a convenience:
	•	If a sort/op mapping line is missing, and a target symbol with the same name exists and typechecks, it is assumed.

C. Run blocks select morphisms per alias
In a run block:

use ccc = CCCIface;

Multiple use entries allowed.

Convenience rule: if a surface requires ccc : X and the run doctrine is exactly X (same doctrine expr after resolution), then use ccc = identity is implicit.

Implementation: new kernel structure for morphisms

Add a new module: src/Strat/Kernel/Morphism.hs.

Define:

data Morphism = Morphism
  { morName    :: Text
  , morSrc     :: Presentation
  , morTgt     :: Presentation
  , morSortMap :: Map SortName SortName
  , morOpMap   :: Map OpName OpName
  }

Provide:
	•	applyMorphismSort :: Morphism -> Sort -> Sort
	•	applyMorphismTerm :: Morphism -> Term -> Term

Morphism checking

Implement:

checkMorphism
  :: RewritePolicy  -- recommended: UseStructuralAsBidirectional
  -> Int            -- fuel for normalization/joinability checks
  -> Morphism
  -> Either MorphismError ()

Checks:
	1.	Sort arities match: for each sort ctor S in source, mapped ctor S' exists in target and has α-equivalent telescope after mapping.
	2.	Op arities and types match: for each op f in source, mapped f' exists in target and:
	•	telescope lengths match
	•	binder sorts match after applying sort mapping + substitution
	•	result sort matches after applying sort mapping + substitution
	3.	Equation preservation: for each equation in source:
	•	map lhs/rhs to target terms using applyMorphismTerm
	•	check joinability under target rewrite system:
	•	normalize both with the chosen policy and fuel
	•	require normal forms syntactically equal
	•	if fuel exhausted → error MorphismEqUndecided (do not silently accept)

Surface core-expression resolution must be principled

Remove slotKey behavior.

Core refs in surface rules/defines:
	•	ccc.foo means:
	•	alias = ccc
	•	slot = foo (an op name in the source interface doctrine)
	•	resolved to target op name via the chosen morphism for alias ccc

If core expr name has no dot:
	•	first check surface-defined core functions (same as current behavior)
	•	otherwise error “unresolved core name” (do not fall back to ignoring prefixes)

Code changes required
	•	Delete (or deprecate) src/Strat/Surface2/Interface.hs and InterfaceInst.hs.
	•	Update:
	•	Frontend.Env to replace meInterfaces with meMorphisms
	•	Kernel/DSL/Elab.hs to elaborate morphism declarations into Morphism values
	•	Frontend/RunSpec.hs and Kernel/DSL/Parse.hs to parse use alias = morphismName;
	•	Surface2/CoreEval.hs to accept a map alias -> Morphism (or alias -> resolved op map) instead of a single interface instance

⸻

4. Surface elaboration: remove operational bias, detect ambiguity

Problem being fixed

The current solver is a backtracking engine that is sensitive to rule ordering and fuel quirks.

Required behavior

For a given goal (Judgment, Args):
	•	All rules that match are considered.
	•	If exactly one rule leads to a successful derivation, it is used.
	•	If more than one rule leads to success → error: ambiguity, listing the matching rules.
	•	If none succeed → error: no rule applies, with best-effort diagnostics.

Implementation change

In src/Strat/Surface2/Engine.hs, replace “try rules in order and return first success” with:
	1.	Enumerate candidate rules r where rcJudg matches.
	2.	For each candidate:
	•	attempt matchConclusion
	•	if match succeeds, attempt to solve all premises recursively
	•	if premises succeed, record success (ruleName, result, newSupply)
	3.	At end:
	•	0 successes → Left NoRuleApplies
	•	1 success → return it
	•	1 successes → Left AmbiguousRules [ruleName...]

Supply handling: each candidate attempt uses the same input supply; only the chosen unique success commits its returned supply.

New error types

Add to Surface2.Types (or where surface errors live):
	•	AmbiguousRules { goal, candidates :: [RuleName] }
	•	NoRuleApplies { goal, attempted :: [(RuleName, MatchFailureSummary)] }

⸻

5. Second-order GATs: implement as a presentation layer + immediately use it for boilerplate reduction

This section is split into two deliverables:
	•	5A: immediate boilerplate reduction for CCC-style compilation (required now)
	•	5B: SOGAT front-end block (required now, minimal but real; can be iterated)

5A. Derived context/product machinery for surfaces (boilerplate reduction now)

Motivation
In STLC→CCC compilation, ctxObj and proj are generic consequences of finite products. They should not be re-written in every surface.

New surface directive
Inside a surface block:

derive contexts using ccc;

Meaning:
	•	the surface must have requires ccc : <InterfaceDoctrineExpr>;
	•	the interface doctrine must include the cartesian structure needed:
	•	Unit, prod, exl, exr, pair, terminal
	•	and id, comp (for assembling projections)
	•	the surface must define tyObj : Ty -> Core (or equivalent) so context objects can be built

What gets generated
If not explicitly defined by the user:
	•	A generated core define:
	•	ctxObj : Ctx -> Core
	•	A generated core define:
	•	proj : (Γ:Ctx)(i:Nat) -> Core
	•	A generated typing rule (if not explicitly present):
	•	variable rule for #i:
	•	premise: lookup(Γ, i) = A
	•	conclusion core: proj(Γ,i)

Override policy
	•	Prefer “explicit overrides derived”: if user provides ctxObj/proj/var rule explicitly, do not generate that component.

Implementation notes
	•	Implement generation by directly injecting Def values into the surface definition after parsing/elaboration (in Surface2.Def or the surface elaborator).
	•	The generated code must be exactly the existing STLC boilerplate, but parameterized by the alias ccc and by the user’s tyObj.

This reduces the surface file sprawl immediately while remaining faithful to the intended semantics.

5B. Minimal but real SOGAT front-end for presentations

You must implement a new top-level declaration form that is genuinely second-order in the presentation syntax, but compiles to a first-order GAT presentation.

New top-level block

sogat <Name> where {
  context_sort Ty;

  sort Ty;
  sort Tm (A:Ty);

  op Arr (A:Ty) (B:Ty) -> Ty;

  op Lam (A:Ty) (t : Tm(B) [x:A]) -> Tm(Arr(A,B));
  op App (f:Tm(Arr(A,B))) (u:Tm(A)) -> Tm(B);

  -- (optional in v1) equations, but **no binding in equations yet**
}

Compilation target
The sogat block elaborates into an ordinary Presentation with:
	•	An explicit context sort ctor:
	•	sort Ctx;
	•	Context constructors:
	•	op empty : Ctx;
	•	op extend : (Γ:Ctx) (A:Ty(Γ)) -> Ctx;
	•	Each user sort becomes context-indexed:
	•	Ty(Γ:Ctx)
	•	Tm(Γ:Ctx)(A:Ty(Γ))
	•	Each user op gets an explicit Γ:Ctx first parameter, and binder arguments become arguments in extended context:
	•	Lam becomes (schematically):
	•	(Γ:Ctx)(A:Ty(Γ))(B:Ty(Γ))(t:Tm(extend(Γ,A), B↑)) -> Tm(Γ, Arr(A,B))
	•	For v1 (simply-typed), B↑ is just B (no dependency, so no weakening/substitution required).

v1 restriction (explicit)
To keep this implementable without full dependent substitution:
	•	Types do not depend on term variables (simply-typed fragment).
	•	Binder variables may not appear in type indices.
	•	Equations in sogat v1 cannot quantify over binder meta-variables (no β-laws in this layer yet).

This is still a meaningful second-order presentation language (binders in op arities) and produces concrete boilerplate reduction for writing syntax theories.

Integration
	•	sogat-produced presentations must be usable anywhere a doctrine presentation is accepted (e.g., as an interface doctrine in §3).

⸻

6. Cleanup: remove redundant declaration sprawl

Required simplifications
	1.	Eliminate the old interface subsystem:
	•	remove built-in interface kinds
	•	remove interface ... for doctrine ... as a primitive
	•	replace with morphism + use in runs
	2.	Unify syntax declarations
	•	Replace surface_syntax and syntax with a single syntax declaration parameterized by the target:

syntax CoreSyn   for doctrine CCC where { ... }
syntax StlcSyn   for surface  STLC where { ... }


	•	Internally, share the instantiation pipeline; do not maintain two independent syntax-spec ASTs.

	3.	Remove redundant modules
	•	If Strat.Surface (non-2) is only legacy parsing and not needed by any example/test after migration, delete it and remove runSurface = Nothing path. Keep only one surface subsystem (Surface2).

⸻

7. Useful semantics: add readback to surface results (true, not a combinator)

Problem being fixed

Even with correct compilation, the user-facing output is a categorical term. You need a way to report a useful surface-level result.

Strategy (minimal, correct, immediately valuable)
	1.	Ensure the CCC doctrine used in the STLC example contains enough computational equations for normalization to reduce closed Bool computations to T or F.
	2.	Add a new run output channel: result (readback), printed via surface syntax.

7A. Fix CCC doctrine in examples/ccc_surface/ccc.doctrine.llang

Replace the minimal CCC with a CCC_Bool doctrine that includes at least:
	•	category laws (idL, idR, assoc) (assoc may remain structural)
	•	product β rules as computational:
	•	exl_pair, exr_pair
	•	CCC β rule as computational (already present as beta in the minimal file)
	•	terminal/unit computation as computational:
	•	terminal_unit : terminal(Unit) -> id(Unit)
(needed so comp(Unit,Unit,Bool,T,terminal(Unit)) reduces to T)
	•	Bool constants T, F and (optionally) eliminator with β rules

This is necessary for (\x.x) true to normalize to exactly T under UseOnlyComputationalLR.

7B. Add show result; and readback

RunSpec changes
In src/Strat/Frontend/RunSpec.hs and parsing:
	•	Add a new show flag: result
	•	show result; in run blocks

Run pipeline changes
In src/Strat/Frontend/Run.hs, in surface mode:
	•	After solving surface judgment and producing coreTerm:
	•	normalize coreTerm under the run policy (already done)
	•	Attempt readback:
	1.	Determine inferred surface type (the hole that corresponds to the type argument of HasType).
	2.	If inferred type is BoolTy (surface term constructor), then:
	•	if normalized core term is TOp <mapped T> [] → surface result term is True
	•	if normalized core term is TOp <mapped F> [] → surface result term is False
	•	otherwise: “result not in canonical Bool form”
	3.	Pretty-print the surface result term using the selected surface syntax.

Note: since interface mapping is now morphism-based, “mapped T/F” means:
	•	T and F are interface slots in the required interface doctrine
	•	their images are concrete ops in the run doctrine via use ccc = ...

Output format
Add rrResult :: Maybe Text (or similar) to RunResult, and in CLI display print a line:
	•	result: true (using surface syntax printer)

This gives the required behavior without implementing a full Set model.

⸻

8. Tests to add/update

8.1 Kernel: dependent sort ctor telescope

Create test/Test/Kernel/SortCtorTele.hs:
	•	Define a doctrine (in-memory or via parsing) with:

doctrine Dep where {
  sort Ctx;
  sort Ty (Γ:Ctx);
  sort Tm (Γ:Ctx) (A:Ty(?Γ));
}


	•	Assert validatePresentation succeeds.
	•	Add an op using dependent sort indices and assert elaboration succeeds.

8.2 Doctrine include/extends eliminates duplication

Create test/Test/Kernel/Include.hs:
	•	Base defines sort Obj; op A : Obj;
	•	Ext does include Base; op f : Hom(A,A);
	•	Assert Ext signature has exactly one Obj ctor and f elaborates without re-declaring Obj or Hom.

8.3 Morphism typechecking + equation preservation

Create test/Test/Kernel/Morphism.hs:
	•	Define MonoidSig doctrine with equations.
	•	Define MonoidRenamed doctrine with same equations but renamed op symbols.
	•	Define morphism mapping and assert checkMorphism passes.

8.4 Surface determinism + ambiguity detection

Create test/Test/Surface/Determinism.hs:
	•	Duplicate STLC surface with rules permuted; solve the same goal; assert same normalized core term.
	•	Create surface with two identical rules matching a goal; assert solver throws AmbiguousRules.

8.5 End-to-end: STLC result is true

Update test/Test/CLI.hs:
	•	In the STLC surface test, use a run file that includes show result;
	•	Assert the run result includes true (either via a new rrResult field or by inspecting output text).

⸻

9. Required example migrations

9.1 Sort declaration syntax migration

All occurrences like:

sort Hom(Obj, Obj);

must be rewritten to telescope form (after §1):

sort Hom (a:Obj) (b:Obj);

This applies across examples/*.llang and stdlib.

9.2 Replace duplicated doctrine blocks with include

Example: examples/ccc.llang and examples/monoid.llang should become:

doctrine CCCore where { ... }

doctrine CCGen where {
  include CCCore;
  op X : Obj;
  op A : Obj;
  ...
}

9.3 Replace requires interface ... with alias form

In surface files:

requires interface CCC_Bool;

becomes:

requires ccc : CCC_Bool;

All core references must be qualified as ccc.<slot> (and must now be respected, not ignored).

9.4 Replace interface declarations and run selection
	•	Remove interface CCCIface for doctrine CCC ... blocks.
	•	Replace with:
	•	a doctrine CCC_Bool (interface theory) if needed
	•	a morphism:

morphism CCCIface : CCC_Bool -> CCC where { ... }


	•	In run blocks, replace:

interface CCCIface;

with:

use ccc = CCCIface;



9.5 Add useful semantics display in STLC run

Update examples/ccc_surface/stlc.run.llang:
	•	Ensure CCC doctrine used is the enriched one from §7A
	•	Add:

show result;



Expected behavior: result: true.

⸻

10. Ordering of implementation (for the agent)

A minimal dependency-correct order:
	1.	Kernel sort ctor telescope (§1) + update all usages/tests that break.
	2.	Doctrine include/extends (§2) + refactor examples to remove duplication.
	3.	Morphism subsystem (§3) + remove old interface code paths.
	4.	Surface requires alias + run use mapping (§3) + update STLC surface example.
	5.	Deterministic surface solver (§4) + ambiguity errors.
	6.	Derived contexts (§5A) + remove ctxObj/proj boilerplate from STLC surface (optional but required for “boilerplate reduction now”).
	7.	SOGAT front-end block (§5B) + at least one small example/test proving it elaborates.
	8.	Result readback (§7B) + CCC doctrine enrichment (§7A) so (\x.x) true → true.

This ordering ensures each step has a stable testable surface before proceeding.
