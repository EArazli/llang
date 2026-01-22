# Mathematical specification of the project as implemented

This document specifies the mathematical objects and algorithms implemented by the project (kernel, doctrine composition, morphisms/interpretations, surface layer, runs, normalization, and model evaluation). It is written to support reasoning about correctness and behavior of the implementation.

---

## 0. Meta-level goal and architecture

The project implements a **meta-language** (the “llang” DSL) for specifying and composing:

1. **Doctrines**: presentations of (first-order) generalized algebraic theories with dependent arities (dependent signatures + equations), equipped with a rewriting system for definitional equality.
2. **Interfaces**: not a distinct concept—an interface is simply a doctrine/presentation that other layers “require”.
3. **Morphisms / interpretations** between doctrines: mappings of symbols to symbols/terms with proof obligations (equation preservation) checked by normalization/joinability.
4. **Syntax**: parsing/printing of core kernel terms via user-defined notations (no binding) and a separate, rule-based “Surface2” language with binding and typing judgments.
5. **Runs**: configurable elaboration + rewriting + model evaluation pipelines, with reusable run-specs and multiple runs per file.
6. **Models**: an interpretation of operations into a simple meta-evaluator (symbolic or expression-based).

Everything ultimately compiles to / is checked against the **kernel presentation**:

* sort constructors + operation symbols (with dependent telescopes),
* equations (classified structural/computational, oriented/bidirectional),
* rewriting within a bounded fuel.

---

## 1. Kernel: first-order dependent signatures and terms

### 1.1 Names and scopes

* **Sort names**: `SortName` (text).
* **Operation names**: `OpName` (text).
* **Variables** are scoped by:

  * a **scope id** `ScopeId` (text), and
  * a **local de Bruijn-like index** `vLocal :: Int`.

So a variable is `Var(scope, local)`.

Scopes are generated deterministically from declaration sites:

* sort telescope variables live in `scope = "sort:<SortName>"`,
* op telescope variables live in `scope = "op:<OpName>"`,
* equation telescope variables live in `scope = "eq:<EqName>"`,
* critical-pair generation renames scopes under `cp:<...>`.

This makes variables globally distinguishable without binders in the term syntax.

### 1.2 Sort expressions

A **sort expression** is a constructor applied to **index terms**:

* Sort: `S(t1, …, tn)` where `S : SortName` and each `ti` is a kernel term.

In code: `Sort (SortName S) [t1..tn]`.

There is **no binder** in sort expressions; dependency is represented by allowing index terms to contain variables from the ambient telescope.

### 1.3 Contexts and telescopes

A **telescope** (used for sort constructors, operation arities, equations) is a list of binders:

* Binder: `(x : A)` where `x : Var` and `A : Sort`.

In code: `Binder v sort`.

A telescope `Γ = (x0:A0, x1:A1, …, x_{k-1}:A_{k-1})` is **dependent**: each `Ai` may mention earlier variables `x0..x_{i-1}` via index terms inside `Ai`.

### 1.4 Terms

A **term** is:

* a variable `x`, or
* an operation application `o(u1,…,um)`.

In the implementation each term stores its sort:

* `Term { termSort :: Sort, termNode :: TermNode }`
* `TermNode = TVar Var | TOp OpName [Term]`

There are no binders in `Term`. Binding is expressed only through telescopes on declarations/equations.

### 1.5 Signatures

A **signature** consists of:

1. **Sort constructors**:

   * `SortCtor` has a name `S` and a telescope `ΔS` of parameters.
   * Intuition: `S` is a family of sorts indexed by terms of the sorts given in `ΔS`.

2. **Operation declarations**:

   * `OpDecl` has name `o`, telescope `Δo` (arguments), and a result sort `B`.
   * Intuition: `o` is a dependent operation:
     [
     o : (x_0:A_0,\ldots,x_{m-1}:A_{m-1}) \to B
     ]
     where later `A_i` and `B` may depend on earlier arguments.

In code: `Signature { sigSortCtors :: Map SortName SortCtor, sigOps :: Map OpName OpDecl }`.

### 1.6 Well-formedness of sort applications: `mkSort`

Given a signature and a sort application `S(t1..tn)`:

* Check `S` exists.
* Check arity: number of indices equals length of telescope `ΔS`.
* Check each index term has the expected sort, **instantiating dependencies**:

  * Maintain a substitution `σ` mapping binder vars to provided index terms.
  * For binder `(v : A)` in telescope order, expected sort is `A[σ]`.
  * Require `sort(ti) = A[σ]`, then extend `σ := σ ∪ {v ↦ ti}`.
* If successful, the sort expression is well-formed.

This is implemented as `mkSort`.

### 1.7 Well-formedness of operation applications: `mkOp`

Given a signature, an op `o`, and arguments `u1..um`:

* Lookup `Δo = (v0:A0,...,v_{m-1}:A_{m-1})` and result sort `B`.
* Check arity: `m` matches.
* Check each argument sort against the instantiated binder sorts as above, building a substitution `σ`.
* Result sort is `B[σ]`.

This is implemented by constructing a `Term` whose `termSort` is the substituted result sort.

### 1.8 Substitution

A substitution is a finite map `σ : Var ⇀ Term`.

* Apply to sorts: `S(t1..tn)[σ] = S(t1[σ]..tn[σ])`.
* Apply to terms:

  * `x[σ] = σ(x)` if present, otherwise `x` (with sort substituted).
  * `o(args)[σ] = o(args[σ])` (with sort substituted).

Implementation detail: substitution application tracks a `seen` set to prevent non-termination on cyclic substitutions.

---

## 2. Presentations: signatures + equations

### 2.1 Equations

An equation is:

* a name `e`,
* a **class**: `Computational` or `Structural`,
* an **orientation**:

  * `Unoriented` (no rewrite rule),
  * `LR` (left-to-right),
  * `RL` (right-to-left),
  * `Bidirectional` (both directions),
* a telescope `Γ`,
* two terms `l, r` (well-typed in `Γ`) of the same sort.

In code: `Equation { eqName, eqClass, eqOrient, eqTele, eqLHS, eqRHS }`.

### 2.2 Presentation

A presentation is:

* a name `P`,
* a signature `ΣP`,
* a list of equations `EP`.

In code: `Presentation { presName, presSig, presEqs }`.

### 2.3 Validation

The kernel validates a presentation by checking:

* sort constructor decls are well-formed (telescope binders have well-formed sorts),
* op decls are well-formed,
* each equation:

  * telescope well-formed,
  * LHS and RHS terms are well-typed under telescope and have the same sort,
  * *variables used* are from the telescope,

Rewrite-specific side conditions are enforced when compiling a rewrite system (not when merely validating a presentation). In particular:
Whether an equation is eligible as a rewrite rule depends on the chosen rewrite policy and its orientation.
For any equation direction selected as a rewrite rule, the kernel requires vars(RHS) ⊆ vars(LHS) (no new variables introduced by rewriting).
Rule-name uniqueness (among the rules included in the selected rewrite system) is also enforced at rewrite-system compilation time.
These checks are implemented in `compileRewriteSystem` via `buildRules`/`rulesForEq` (see `src/Strat/Kernel/RewriteSystem.hs`).

---

## 3. Rewriting systems and definitional equality

### 3.1 From equations to rewrite rules

Each equation can yield **directed rewrite rules** depending on its orientation and on the chosen **rewrite policy** (next section). Internally, a `Rule` carries:

* rule id (from equation name and direction),
* rule index (deterministic iteration order),
* equation name and class (`Computational`/`Structural`),
* LHS/RHS terms.

The equation telescope is not stored on `Rule`; variables in `lhs`/`rhs` originate from the equation telescope and are represented explicitly as `Var` nodes with scoped identifiers.

### 3.2 Rewrite policy

The implementation supports three policies:

1. `UseOnlyComputationalLR`

   * Use only `Computational` equations.
   * Use only their left-to-right direction.
   * Ignore structural equations.

2. `UseStructuralAsBidirectional`

   * Use computational equations as oriented.
   * Treat **structural** equations as **bidirectional** rewrite rules (both directions) regardless of declared orientation.

3. `UseAllOriented`

   * Use all oriented rules (computational and structural) following the declared orientation(s).

### 3.3 Matching (rewrite application)

To apply a rewrite rule `l → r`:

* Search for a subterm position `p` in target term `t` such that `l` matches `t|p`.
* Matching is *first-order pattern matching* using kernel variables as pattern variables:

  * matching checks sorts as well as term structure,
  * substitution must be consistent,
  * matching does not use occurs checks (it is pattern matching, not unification).

If a match `σ` is found, the reduct is `t[r[σ]]_p` (replace the matched subterm by `r` instantiated by `σ`).

The implementation enumerates all such redexes.

Occurs-checking unification (unify) is used by critical-pair generation tooling (overlaps/unifiers between LHS patterns), and does reject cyclic bindings. (See src/Strat/Kernel/Unify.hs for match vs unify.)

### 3.4 One-step rewrite and strategy

* `rewriteOnce` enumerates all possible redexes `(pos, rule, subst)` and yields the resulting terms.
* `chooseRedex` selects the **first** redex by:

  * smallest position (lexicographic), then
  * smallest rule index.

This yields a deterministic “first redex” strategy.

Before matching, rules are **freshened** against the target term to avoid variable-scope collisions; substitutions and step replay are computed against the freshened rule.

### 3.5 Normalization (bounded)

`normalize(fuel, RS, t)` performs up to `fuel` rewrite steps using the first-redex strategy. If no redex exists, it returns the term unchanged.

This is a **bounded**, strategy-dependent normalization; it is not guaranteed to compute a canonical normal form unless the rewrite system is confluent/terminating and the strategy is normalizing.

### 3.6 Joinability (bounded)

`joinableWithin(fuel, RS, t1, t2)` computes bounded reachability sets from each term by nondeterministic rewriting (BFS up to fuel) and checks whether the sets intersect.

This is the project’s general-purpose “definitional equality” check when normalization is insufficient (e.g. due to bidirectional structural rules).

### 3.7 Critical pairs and coherence tooling

The kernel includes:

* computation of **critical pairs** between rewrite rules by unifying the LHS of one rule with subterms of another’s LHS (all positions),
* classification into:

  * structural vs structural overlaps (“needs commute”),
  * structural vs computational overlaps (“needs join”).

A “joiner” can be validated by replaying derivation steps. This is tooling; runs do not automatically enforce completion/coherence.

---

## 4. Doctrine assembly (as implemented)

The DSL provides only three ways to build doctrines; there are **no** doctrine expressions (`&`, `rename`, `share`, `include`, `@`) in the implementation.

### 4.1 Atomic doctrines and qualification

A doctrine declaration `doctrine X where { ... }` elaborates a **raw presentation** from the items and then **qualifies** it by prefixing:

* every sort constructor name `S` ↦ `X.S`,
* every op name `o` ↦ `X.o`,
* every equation name `e` ↦ `X.e`,

and sets the resulting presentation’s `presName = X`.

This qualification is the project’s primary name-spacing mechanism.

Raw terms and raw sorts inside doctrine and morphism declarations may use **qualified identifiers** containing `.` to refer to symbols from other namespaces (e.g., `Category.Obj`, `BoolExt.g`). Unqualified identifiers resolve within the current presentation as usual.

Qualification is purely prefix-based: qualifying a presentation under `X` prefixes existing names rather than structurally rebasing them (so `BoolExt.g` becomes `X.BoolExt.g`).

### 4.2 Extension (`extends`)

`doctrine X extends Y where { ... }` is elaborated as:

1. look up the **raw** presentation of `Y`,
2. merge it with `X`’s new raw items (duplicates allowed only if α‑equivalent),
3. qualify the merged presentation by prefixing with `X`.

Additionally, the system generates a morphism:

* `X.fromBase : Y -> X`,

implemented as a symbol-map morphism that maps each `Y.*` symbol to the corresponding `X.*` symbol. This morphism is validated by the kernel’s morphism checker.

### 4.3 Pushout (`pushout`)

`doctrine P = pushout f g;` constructs a presentation `P` from morphisms:

* `f : A -> B`
* `g : A -> C`

with the **same source** `A`. The implementation enforces:

* `f` and `g` are **symbol-map** morphisms (each op maps to `op(args...)`), and
* the induced maps on **interface** sorts/ops are injective.

The pushout works by renaming the images of interface symbols in `B` and `C` back to the interface names, then merging `A`, `B'`, and `C'`. The result’s `presName` is set to `P` (symbol names retain their original namespaces, except for unified interface symbols).

The system generates and validates:

* `P.inl : B -> P`,
* `P.inr : C -> P`,
* `P.glue : A -> P`.

### 4.4 Interoperability via morphisms

If there is a morphism `m : D1 -> D2`, then any term in `D1` can be transported into `D2` by applying the morphism (`applyMorphismTerm m`). This is the only interoperability mechanism used throughout the system.

---

## 5. Morphisms (interpretations) between presentations

### 5.1 Data of a morphism

A morphism ( M : P \to Q ) consists of:

1. A total sort-name mapping:
   [
   M_S : \mathrm{SortName}_P \to \mathrm{SortName}_Q
   ]
   (filled with identities where possible).

2. For each op ( o \in \mathrm{Op}_P ), an **operation interpretation**:

   * a telescope `Δ` (same length as the translated source telescope), and
   * a RHS term ( M_o ) in the target presentation.

In code:

* `Morphism { morSrc, morTgt, morSortMap, morOpMap, morCheck }`
* `OpInterp { oiTele :: [Binder], oiRhs :: Term }`

3. A morphism-check configuration `(policy, fuel)` used to validate equation preservation.

### 5.2 Translation of sorts and terms

Given a morphism (M):

* Translate a sort:
  [
  M(S(t_1,\ldots,t_n)) = M_S(S)(M(t_1),\ldots,M(t_n))
  ]

* Translate a term:

  * Variables: preserve variable identity but translate their stored sort.
  * Op applications:

    * translate args first,
    * then replace `o(args)` by the instantiated interpretation term:
      [
      M(o(u_1,\ldots,u_m)) = M_o[u_i / x_i]
      ]
      where the interpretation’s telescope variables are substituted by translated arguments (with dependent instantiation).

This is implemented by `applyMorphismSort`, `applyMorphismTerm`, and `applyOpInterp`.

### 5.3 Checking that an op interpretation is well-typed

Let the source op decl be:
[
o : (x_0:A_0,\ldots,x_{m-1}:A_{m-1}) \to B
]
Translate the telescope sorts and result sort into the target using `M`.

The op interpretation provides:
[
o \mapsto \langle (y_0:C_0,\ldots,y_{m-1}:C_{m-1}),\ t \rangle
]

The check requires:

* (m) matches,
* for each binder position (i):
  [
  C_i \equiv M(A_i)[y_0/x_0,\ldots,y_{i-1}/x_{i-1}]
  ]
* result sort:
  [
  \mathrm{sort}(t) \equiv M(B)[y_0/x_0,\ldots,y_{m-1}/x_{m-1}]
  ]

The current implementation uses strict syntactic sort equality for these checks (no weakening-aware coercions during morphism typechecking). Any weakening-aware morphism typing would be a future extension and would also require inserting explicit coercions when applying op interpretations.

### 5.4 Equation preservation obligation

For each equation (e : \Gamma \vdash l = r : A) in (P):

* compute translations (l' = M(l)), (r' = M(r)) in (Q),
* check that (l') and (r') are equal by:

  * normalize both sides with `normalizeStatus` under (Q)’s rewrite system (policy+fuel),
  * if **both** normalizations finish within fuel **and** the normal forms are syntactically equal, accept,
  * otherwise, attempt `joinableWithin fuel` on the unnormalized translated images (l' and r').

If joinability fails:

* if both normalizations finished, the check fails with `MorphismEqViolation`,
* otherwise, it fails with `MorphismEqUndecided` (insufficient fuel).

If preservation fails, the morphism declaration is rejected.

This makes “implements defaults” and run-time interface resolution safe up to the chosen policy/fuel.

---

## 6. Core syntax and elaboration (no binding)

A doctrine can have associated **doctrine syntax specs** (notations) defining:

* parser: text → a combinator AST → kernel `Term` by resolving op names,
* printer: kernel `Term` → text, using a chosen print notation per op.

Resolution of unqualified names uses an `open` list:

* an unqualified `o` resolves to `o` if present, otherwise to exactly one `ns.o` among the opened namespaces.

There is no binding at this layer; it is for direct construction of kernel op trees.

---

## 7. Surface2: a rule-based elaboration layer with binding

Surface2 is a separate user-declared layer designed to support “surface languages” with binding and typing judgments that elaborate into core/kernel terms via required interfaces.

### 7.1 Surface2 term language

Surface terms are de Bruijn terms:

* `SBound i` (bound variable),
* `SFree name` (free symbol),
* `SCon con [args]` (constructor with arguments),
* each argument is `SArg { binders :: [STerm], body :: STerm }`.

This is a binder-aware syntax: `binders` are surface terms representing binder types (in the surface’s designated context-sort), and `body` lives under those binders (shifted indices).

Basic operations: `shift`, `weaken`, `subst0`, `substMany`.

### 7.2 Surface definitions

A `SurfaceDef` contains:

* surface sorts (names only),
* a distinguished `context_sort` among them,
* contexts are cartesian lists with:

  * empty,
  * extension by a type,
  * lookup by index.
* constructors:

  * each constructor argument has:

    * a name,
    * a list of binder types (`caBinders :: [STerm]`),
    * a sort of the argument body (`caSort :: Sort2Name`),
  * and the constructor has a result sort.
* judgments:

  * each judgment has parameters and outputs,
  * parameter sorts can be:

    * surface term of some surface sort,
    * `Ctx`,
    * `Nat`,
    * `Core` (core terms are only used as *outputs*, not inputs).
* rules:

  * premises are either:

    * judgment premises with patterns,
    * context lookup premises (`lookup Γ i = T`) that bind metavariables.
  * a conclusion is a judgment with input patterns and core-expression outputs.
* `define` clauses: pattern-matching functions for core/surface/context/nat values.
* `requires`: a list of `(alias, Presentation)` pairs.
* optional `derive contexts`: generates a standard context/variable typing story from a required doctrine (cartesian-only at present).

The surface elaborator validates, among other things, that constructor binder types have the surface `context_sort`.

### 7.3 Surface solver semantics

Given a surface definition, a goal judgment (J(\vec{a})), and a fuel:

* Collect all rules whose conclusion judgment is (J).
* For each candidate rule:

  1. Freshen rule variable names (to avoid clashes between recursive uses).
  2. Match the goal arguments against the rule’s conclusion patterns, producing:

     * a metavariable substitution (surface-term metas),
     * nat bindings,
     * context variable bindings.
  3. Solve premises left-to-right recursively:

     * Judgment premises become recursive goals.
     * Under-context premises extend the relevant context argument by an additional type term.
     * Lookup premises bind metavariables to the looked-up type term.
  4. Merge environments/substitutions (with conflict checks and freshness handling).
* If exactly one rule succeeds, return its outputs.
* If none succeed: error.
* If multiple succeed: error (ambiguity).
* If fuel exhausted: error.

This is a deterministic *proof search with rejection of nondeterminism*.

### 7.4 Core expressions produced by the surface

Rule conclusions produce `CoreExpr` outputs:

* `CoreVar name`
* `CoreApp f [args]`

Evaluation of `CoreExpr` yields `CoreVal`:

* `CVCore Term` (kernel term),
* `CVSurf STerm` (surface term),
* `CVCtx Ctx` (context value),
* `CVNat Int`.

Resolution depends on whether the head is a variable reference (CoreVar) or an application (CoreApp).

For CoreVar `f`:
local core environment binding,
required-interface op via alias.slot naming (only if f contains a dot and matches a requires alias),
nullary surface constructor `f` (producing a surface value),
otherwise error.

For CoreApp `f args`:
local core environment binding,
define clause named `f` (function-style evaluation on core arguments),
required-interface op via alias.slot naming,
surface constructor application `f(args)` (building a surface term),
otherwise error.

#### Alias-qualified ops

A core name of the form `alias.slot` is interpreted using the morphism bound to `alias`:

* `alias` must be one of the surface’s `requires` aliases,
* `slot` is resolved as an op name in the **source interface presentation** (direct `slot` or `InterfaceName.slot`),
* that op’s interpretation is looked up in the morphism, yielding an `OpInterp`,
* apply the interpretation by substituting template vars with evaluated core arguments.

Arguments are checked **dependently**:

* expected binder sorts are instantiated by previously checked arguments (dependent telescopes), then compared against the argument’s stored sort.

---

## 8. Run system: composing doctrine, syntax/surface, rewriting, and evaluation

A `RunSpec` fixes:

* a doctrine **name** (referring to an already elaborated presentation),
* `syntax`:

  * required for core runs (core term parser/printer),
  * optional for surface runs (used only to pretty-print normalized core terms),
* for surface runs: a `surface` + `surface_syntax` (surface parser/printer),
* a model name,
* `open` namespaces for name resolution,
* rewrite policy and fuel,
* `uses` map for satisfying surface `requires`,
* show flags (normalized, value, cat, input).

A `run` can inherit from a `run_spec` and override fields.

### 8.1 Execution pipeline

Given a selected run:

1. Look up the doctrine presentation by name (already elaborated during module loading).
2. Compile its rewrite system with the selected policy.
3. Parse/elaborate input:

   * core/doctrine syntax: parse → core term → kernel term.
   * surface: parse surface term → solve `HasType` judgment → evaluate core outputs → kernel term.
4. Normalize the kernel term with fuel.
5. Compile normalized term to `CatExpr` (a syntax tree over ops/vars).
6. Evaluate the normalized term with the chosen model:

   * if the model’s doctrine equals the run doctrine, evaluate directly,
   * otherwise, require a morphism `runDoctrine -> modelDoctrine`, transport the term via that morphism, then evaluate.

### 8.2 Satisfying surface `requires`: building a morphism environment

For each required alias (a : I) and the target run doctrine (D):

Resolve a morphism (m : I \to D) by:

1. explicit `uses` in the run,
2. default `implements (I -> D)` mapping (use if exactly one default matches; if multiple defaults match, error),
3. identity morphism if the required interface presentation equals the run presentation,
4. if exactly one morphism exists in the environment with `src=I` and `tgt=D`, use it,
5. otherwise error.

Every morphism is already checked when declared; identity is checked when constructed.

---

## 9. Models (as implemented)

A model is **not** a general categorical model in the kernel. As implemented, it is a concrete interpreter:

* `interpOp : OpName -> [Value] -> Either RuntimeError Value`
* `interpSort : Sort -> Either RuntimeError SortValue`

Model specs provide:

* per-op clauses with an expression language (`MExpr`),
* a default behavior:

  * symbolic (return an atom or list-headed-by-atom),
  * or error.

Evaluation of a kernel term is straightforward recursion over the op tree, with no binders.

This is sufficient to prototype “interpretations” and to test rewriting correctness, but it is not (yet) a general semantics in categories.

The “compile to categories” output currently is `CatExpr`, which preserves only the op-tree structure; there is no categorical normalizer beyond kernel rewriting.

**Model restriction (implemented):** if a run selects a doctrine `D_run` but the chosen model was declared for `D_model`, the run is still valid provided there is a morphism `m : D_run -> D_model`. The term is transported with `applyMorphismTerm m` and then evaluated using the model for `D_model`. If no such morphism exists (or if it is ambiguous), the run fails.

---

## 10. Explicit limitations and non-goals of the current implementation

These are properties you must assume when reasoning about correctness:

1. **Definitional equality is bounded and strategy-dependent**: normalization is fuel-bounded; joinability is fuel-bounded; confluence/termination are not enforced.
2. **Surface2 proof search is intentionally deterministic**: ambiguity is an error, not backtracking.
3. **Contexts in Surface2 are cartesian lists**: no other context discipline is supported by design.
4. **Models are a simple evaluator**: no general categorical semantics are implemented (yet).

---

## References (for orientation, not required to understand the current code)

* Generalized algebraic theories (Cartmell and later formulations).
* Presheaf-style syntax/semantics: Fiore–Plotkin–Turi.
* Freyd categories / Arrows: classic categorical semantics of effects.
* GATLab (Julia): practical operations on GATs (pushouts/colimits and computations).

For future plans, see `ROADMAP.md`.
