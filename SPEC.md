# Mathematical specification of the project as implemented

This document specifies the mathematical objects and algorithms implemented by the project (kernel, doctrine composition, morphisms/interpretations, surface layer, runs, SOGAT elaboration, normalization, and model evaluation). It is written to support reasoning about correctness and behavior of the implementation.

Assumption: the “SOGAT fixes” previously discussed are applied (i.e. the SOGAT→FO elaborator and the kernel’s weakening-related checks handle context indices correctly, including updating explicit context arguments of operations). Where this matters, it is called out explicitly.

---

## 0. Meta-level goal and architecture

The project implements a **meta-language** (the “llang” DSL) for specifying and composing:

1. **Doctrines**: presentations of (first-order) generalized algebraic theories with dependent arities (dependent signatures + equations), equipped with a rewriting system for definitional equality.
2. **SOGAT doctrines**: a second-order “binder-aware” signature layer compiled down to the first-order kernel.
3. **Interfaces**: not a distinct concept—an interface is simply a doctrine/presentation that other layers “require”.
4. **Morphisms / interpretations** between doctrines: mappings of symbols to symbols/terms with proof obligations (equation preservation) checked by normalization/joinability.
5. **Syntax**: parsing/printing of core kernel terms via user-defined notations (no binding) and a separate, rule-based “Surface2” language with binding and typing judgments.
6. **Runs**: configurable elaboration + rewriting + model evaluation pipelines, with reusable run-specs and multiple runs per file.
7. **Models**: an interpretation of operations into a simple meta-evaluator (symbolic or expression-based).

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
  * (rewrite-side condition) if oriented, RHS variables are a subset of LHS variables.

**SOGAT fix hook (assumed applied):** equation/typechecking validity must treat “context weakening” (for context-indexed sorts/terms produced by the SOGAT elaboration) as admissible in the precise places discussed earlier (i.e. variable sorts can be checked modulo context extension, and weakening updates explicit context indices and explicit context arguments of ops). This is not a general feature of the first-order kernel; it is a targeted accommodation used by the SOGAT encoding and its derived theories.

---

## 3. Rewriting systems and definitional equality

### 3.1 From equations to rewrite rules

Each equation can yield **directed rewrite rules** depending on its orientation and on the chosen **rewrite policy** (next section). Internally, a `Rule` carries:

* rule id (from equation name and direction),
* class (`Computational`/`Structural`),
* LHS/RHS,
* telescope.

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
  * matching and unification include occurs checks to avoid infinite terms.

If a match `σ` is found, the reduct is `t[r[σ]]_p` (replace the matched subterm by `r` instantiated by `σ`).

The implementation enumerates all such redexes.

### 3.4 One-step rewrite and strategy

* `rewriteOnce` enumerates all possible redexes `(pos, rule, subst)` and yields the resulting terms.
* `chooseRedex` selects the **first** redex by:

  * smallest position (lexicographic), then
  * smallest rule index.

This yields a deterministic “first redex” strategy.

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

## 4. Doctrine expressions: compositional construction of presentations

A doctrine in the DSL denotes a `DocExpr`, which elaborates to a presentation.

### 4.1 Atoms and qualification

An atom is `Atom(ns, pres_raw)`.

Elaboration **qualifies** the raw presentation by prefixing:

* every sort constructor name `S` ↦ `ns.S`,
* every op name `o` ↦ `ns.o`,
* every equation name `e` ↦ `ns.e`,

and sets the resulting presentation’s `presName = ns`.

This is the project’s primary name-spacing mechanism.

### 4.2 Include (inside where-doctrines)

Inside a `where`-defined doctrine, `include X` merges presentations at the raw/unqualified level when possible. This enables writing a doctrine once, then later qualifying the whole result by the doctrine’s name when used as an atom.

### 4.3 Merging: `And`

`And A B` elaborates both sides, then merges:

* signatures: union of sort ctors and op decls; duplicates are permitted only if **α-equivalent** (binder-renaming equivalence).
* equations: union; duplicates by name are permitted only if α-equivalent.

If a duplicate name exists but is not α-equivalent, elaboration fails.

### 4.4 Renaming and sharing

* `RenameSorts`, `RenameOps`, `RenameEqs` apply renaming maps.
* `ShareSorts`, `ShareOps` take a list of pairs `(a,b)`, compute connected components, choose a representative, and rename all members to the representative (quotient by name-identification).

Renaming operations also update binder scopes (since scopes are derived from symbol names).

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

This is a strict sort equality check (plus whatever weakening accommodation exists for SOGAT-derived context sorts, if applicable to the target doctrine).

### 5.4 Equation preservation obligation

For each equation (e : \Gamma \vdash l = r : A) in (P):

* compute translations (l' = M(l)), (r' = M(r)) in (Q),
* check that (l') and (r') are equal by:

  * normalization under (Q)’s rewrite system (policy+fuel), and/or
  * bounded joinability under that rewrite system.

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
* a `ContextDiscipline`:

  * currently only `CtxCartesian`, meaning contexts support:

    * empty,
    * extension by a type,
    * lookup by index (with contraction/weakening at the meta-level via structural recursion on the list).
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

Resolution order for a `CoreVar`/`CoreApp` head symbol `f`:

1. local core environment binding,
2. required-interface op via `alias.slot` naming (see below),
3. surface constructor,
4. surface `define` clause.

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

* a doctrine expression,
* either:

  * a doctrine syntax (core term parser/printer), or
  * a surface + surface_syntax (surface parser/printer),
* a model name,
* `open` namespaces for name resolution,
* rewrite policy and fuel,
* `uses` map for satisfying surface `requires`,
* show flags (normalized, value, cat, input, result).

A `run` can inherit from a `run_spec` and override fields.

### 8.1 Execution pipeline

Given a selected run:

1. Elaborate the doctrine expression to a presentation.
2. Compile its rewrite system with the selected policy.
3. Parse/elaborate input:

   * core/doctrine syntax: parse → core term → kernel term.
   * surface: parse surface term → solve `HasType` judgment → evaluate core outputs → kernel term.
4. Normalize the kernel term with fuel.
5. Compile normalized term to `CatExpr` (a syntax tree over ops/vars).
6. Evaluate normalized term with the chosen model, producing a `Value`.
7. Optionally perform readback (currently only a bounded Bool heuristic for surface runs).

### 8.2 Satisfying surface `requires`: building a morphism environment

For each required alias (a : I) and the target run doctrine (D):

Resolve a morphism (m : I \to D) by:

1. explicit `uses` in the run,
2. default `implements (I -> D)` mapping,
3. identity morphism if `I` and `D` are the same presentation name,
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

---

## 10. SOGAT DSL and its compilation to the kernel

The `sogat` DSL is a *binder-aware* signature frontend. It is compiled into an ordinary kernel presentation.

### 10.1 SOGAT inputs

A SOGAT declaration provides:

* `context_sort Ty` (a name; also declared as a sort in the SOGAT block),
* sort declarations `S` with a telescope of parameters (written in SOGAT raw syntax),
* op declarations `o` with arguments, where each argument may carry a list of binders:

  * binder `x : A` where `A` is a SOGAT raw term,
  * argument sort `B`.

### 10.2 Generated first-order context theory

Compilation introduces:

* sort constructor `Ctx : Sort` (arity 0),
* ops:

  * `empty : Ctx`,
  * `extend : (Γ : Ctx, A : Ty(Γ)) -> Ctx`.

(Names `Ctx`, `empty`, `extend` are effectively reserved by this elaboration.)

### 10.3 Context-indexing of sorts and ops

* Every user sort `S` (including the context_sort `Ty`) becomes a first-order sort constructor whose first parameter is a context:
  [
  S(\Gamma, \vec{i})
  ]
* Every op returning a non-`Ctx` sort gets an explicit leading context argument `Γ : Ctx` and result sort indexed by that Γ.

### 10.4 Elaborating binder arguments

A SOGAT argument of the form:

* name `u`,
* binders `[x1:A1, …, xk:Ak]`,
* sort `B`

is compiled by:

1. starting with a current context term `Γ`,
2. elaborating binder types iteratively in the *current* context and extending it:
   [
   \Gamma_0 := \Gamma,\quad
   A_i' : Ty(\Gamma_{i-1}),\quad
   \Gamma_i := extend(\Gamma_{i-1}, A_i')
   ]
3. elaborating the argument sort `B` **under the extended context** `Γ_k`,
4. producing a first-order binder `(u : B'(Γ_k,...))` in the op telescope.

### 10.5 Dependent checking in elaboration

The elaborator threads a term environment mapping SOGAT binder names to kernel terms and performs dependent instantiation checks analogous to `mkSort`/`mkOp`:

* later binder sorts/types can mention earlier binders,
* op argument sorts can depend on earlier arguments,
* result sorts can depend on all arguments.

### 10.6 Implicit weakening (assumed fixed)

Because the SOGAT encoding uses explicit context indices, the system admits an implicit coercion:

* If `Γ'` is a syntactic extension of `Γ` (built by repeated `extend` from `Γ`), then terms/sorts indexed by `Γ` may be used where `Γ'` is expected, by weakening.

**Crucial operational content of the fix** (for correctness):

* weakening must update:

  1. the **leading context index** in the term’s sort, and
  2. the **explicit context argument** passed to any op application whose first argument is a context term,
     and do so recursively through subterms and sort indices.

This weakening is used to typecheck binder types and dependent arities produced by the SOGAT compilation, and (where needed) to validate presentations containing SOGAT-derived context-indexed sorts.

---

## 11. Explicit limitations and non-goals of the current implementation

These are properties you must assume when reasoning about correctness:

1. **Definitional equality is bounded and strategy-dependent**: normalization is fuel-bounded; joinability is fuel-bounded; confluence/termination are not enforced.
2. **Surface2 proof search is intentionally deterministic**: ambiguity is an error, not backtracking.
3. **Contexts in Surface2 are currently cartesian lists**: no linear/affine/relevant discipline is implemented yet.
4. **Models are a simple evaluator**: no general categorical semantics are implemented (yet).
5. **SOGAT encoding currently relies on weakening**: substructural/linear correctness is not expressible at the kernel level without extending the notion of context discipline (this is explicitly deferred to the roadmap).

---

# Plans and roadmap (less detailed, but complete enough to guide design)

This section describes the settled direction and remaining major pieces: effects, pushouts, e-graphs, recursion/datatypes, modules and interoperability, non-cartesian context handling, and improved semantics.

---

## A. Non-cartesian / substructural contexts (Option B direction)

### Target state

Make “context discipline” a first-class, user-provided structure rather than hard-coded cartesian weakening/contracting.

### Design sketch

1. Introduce an explicit *context discipline interface doctrine* `CtxDisc` exposing operations/relations used by:

   * SOGAT compilation,
   * Surface2 `UnderCtx`, lookup, and variable rules,
   * any effect system requiring specific structural rules.
2. Parameterize:

   * SOGAT elaboration over a chosen discipline (cartesian, linear, affine, ordered, relevant),
   * Surface2 context operations (`empty`, `extend`, `lookup`, and later split/merge/exchange where meaningful).
3. Replace “implicit weakening” with discipline-provided admissibility rules:

   * in a linear context, weakening is absent; “use” consumes variables;
   * in ordered contexts, exchange is absent; contexts are sequences.

### Payoff

* Linear syntax becomes definable *without mismatch*.
* Any effect system that assumes cartesian structure becomes implementable only when the doctrine/disciplines provide it (by obligations/implements).

---

## B. Effects as user-defined doctrine layers (no baked-in effect system)

### Target state

Provide primitives sufficient for *declaring* effect systems in user doctrines and proving interoperability constraints, without committing to a single baked-in notion.

### What the meta-language must support (foundation)

1. **Interfaces as doctrines** (already done): effects are expressed as additional required interfaces (e.g. “strong monad”, “Freyd category”, “algebraic effects handler interface”).
2. **Obligation checking** (already done for morphisms): effect laws are equations; implementations are morphisms; validation is equation preservation.
3. **Context-discipline gating** (future): effects that need cartesian structure require the cartesian discipline interface.

### Example family of libraries (later, not in kernel)

* monadic effects (Kleisli triples),
* Freyd categories / Arrows-style effects,
* algebraic effects via handlers,
* linear effects via graded/linear monads, etc.

---

## C. Pushouts / theory assembly (`CCC + Bool + Nat + …`)

### What “pushout” should mean here

In a category of presentations, a pushout is a way to *glue* theories along a shared subtheory:

* Given morphisms (A \xrightarrow{f} B) and (A \xrightarrow{g} C),
* build (B \sqcup_A C) that identifies the images of (A) in both.

### Practical implementation plan (tractable subset)

1. Implement **pushout of signatures** along *symbol maps* (rename/share level):

   * For now restrict `f` and `g` to *structure-preserving symbol maps* (SortName↦SortName and OpName↦OpName) or to morphisms whose op interpretations are *variables/constructors* that act like renamings.
   * This yields a computable “gluing” by explicit renaming and sharing (which the project already supports via `Rename*` and `Share*`).
2. Add DSL sugar:

   * `pushout(B <- A -> C)` that expands to a `DocExpr` with the necessary renames and shares.
3. Once e-graphs are in place (section D), extend pushouts to more general op→term morphisms:

   * identification then becomes “quotient by equations induced by the span”, which is not tractable via simple name-sharing alone.

### What you get immediately

* A robust way to build `CCC_Bool` from `CCC` and `Bool` when the overlap is mostly shared by name/renaming (e.g. a common `Unit`, `Bool`, `T`, `F` interface).
* A structured replacement for ad-hoc `And + Share + Rename` recipes.

---

## D. E-graph normalization / equality saturation

### Motivation

Current rewriting is:

* oriented and fuel-bounded,
* sensitive to strategy,
* brittle for structural equalities (CCC, associativity, η-laws).

### Plan

1. Add an alternate equality engine based on **e-graphs**:

   * load equations (structural) as congruences,
   * optionally load computational rules as directed rewrites or also as equalities,
   * extract canonical representatives with cost functions.
2. Use it for:

   * morphism equation preservation (stronger, less strategy-dependent),
   * readback and “canonical form” reporting,
   * coherence obligation discharge automation (critical pair joins).

This is the natural next step once “theory assembly” and “interop correctness” become central.

---

## E. Recursion and user-definable datatypes

### What’s missing today

* There is no first-class notion of inductive definitions or recursion in the kernel.
* You can encode specific recursors manually as operations + equations, but there’s no user-facing mechanism for:

  * introducing a datatype,
  * generating constructors,
  * generating elimination/recursion principles and β/η laws.

### Plan (kept compatible with the kernel)

1. Add a doctrine-library layer that provides:

   * a schema for *initial algebras* / W-types-like signatures,
   * generated operations:

     * constructors,
     * fold/recursor,
   * generated computation equations (β-laws) as `Computational` rules.
2. Keep general recursion separate:

   * either add a `Fix` interface (with appropriate equations and/or guardedness discipline),
   * or treat general recursion as an effect (partiality) requiring additional structure.

This fits the existing foundation because “datatype definitions” compile to ordinary presentations + equations.

---

## F. Modules and true interoperability of doctrines/terms

### Problem today

Multiple runs in a file are separate pipelines. Terms do not interact across runs; there is no notion of “import a term produced under doctrine X and use it under doctrine Y”.

### Needed concept

A **module system** that:

* gives names to definitions (terms),
* assigns them a doctrine + surface + model context,
* and allows importing them through morphisms.

### Plan

1. Introduce module-level definitions:

   * `def foo : <judgment/type> := <surface/core term>`
   * each definition elaborates under some run context (doctrine/surface/syntax).
2. Allow a definition to be *re-used* under another doctrine by requiring a morphism:

   * if `foo` is a kernel term in doctrine `P`, and you want it in doctrine `Q`, require a morphism `P -> Q` and translate it with `applyMorphismTerm`.
3. Make run specs reusable at **term level**:

   * `run_spec` becomes a named environment that can be attached to defs, not just runs.
4. Add explicit “interop declarations”:

   * `import foo using morphism M` or `open module X as Y` with checked requirements.

This leverages the existing morphism machinery; what’s missing is the definition namespace and the ability to store elaborated terms in the environment.

---

## G. Interoperability between models

### Desired behavior

Interpret a term in one model (e.g. AD) and use it in another (e.g. Eval/Hask), with correctness constraints.

### Plan

1. Treat model interoperability as **morphisms at the model level**:

   * a natural transformation-like map between interpretations,
   * or a “model transformer” that maps `interpOp` implementations.
2. Make composition explicit:

   * `Model := AD ∘ Eval` becomes a declared object with obligations (equations/laws).
3. Use the same obligation machinery:

   * either by checking commutation on a test suite of generated terms,
   * or by symbolic equality saturation where possible.

This is strictly beyond the current model implementation, but the same discipline (“declare structure + prove obligations”) applies.

---

## H. Next steps to improve usability quickly (without destabilizing foundations)

1. Implement pushout-sugar on top of existing `Rename/Share/And`.
2. Add e-graph mode for equality checking and for morphism obligations (optional backend).
3. Add definition bindings (`def`) and module imports, using morphisms for translation.
4. Add datatype schema as library-doctrines (Nat/List + folds), generate β equations.
5. Generalize context discipline (Option B proper), then revisit SOGAT weakening assumptions.

---

## References (for orientation, not required to understand the current code)

* Generalized algebraic theories (Cartmell and later formulations).
* Presheaf-style syntax/semantics: Fiore–Plotkin–Turi.
* SOGAT presentations and semantics: Kaposi–Xie (“Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics”).
* Equality saturation / e-graphs: the “egg” approach (Tate et al. and subsequent work).
* Freyd categories / Arrows: classic categorical semantics of effects.
* GATLab (Julia): practical operations on GATs (pushouts/colimits and computations).