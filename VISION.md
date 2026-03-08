# llang: Vision and Design Rationale

## The problem

Most real software systems are compositions of multiple computational languages that differ in structural discipline, evaluation strategy, effect discipline, and compilation target. Even a single language is typically a composition of multiple type-theoretic features whose interactions are complex and whose combination is re-verified from scratch for each new system. These languages and features are rarely made explicit — they appear as implicit fragments within a single host language, separated by conventions, annotations, or phase distinctions rather than by typed interfaces.

Examples of such multi-language structure include:

- **Mode distinctions**: client vs. server code, GPU vs. CPU code, compile-time vs. runtime computation, linear vs. unrestricted resources, deterministic vs. nondeterministic execution, pure vs. effectful code.
- **Structural discipline variation**: code that admits copying and discarding (cartesian) vs. code that is resource-sensitive (linear/affine) vs. code that is ordered (planar), coexisting within a single system and needing to interoperate.
- **Evaluation strategy boundaries**: which subexpressions can be partially evaluated, which must be deferred, which can be staged across phases — and the correctness conditions when results cross these boundaries (e.g., hydration, serialization, quoting).
- **Effect boundaries**: which effects are available in which fragment, how effects compose across fragment boundaries, and whether composition preserves effect invariants.
- **Compilation as translation between languages**: code generation, optimization passes, and target specialization are all transformations from one language to another, with correctness conditions that are currently unchecked.

The same compositional structure appears not only between languages but within a single language's type system. A type system is typically assembled from independently-conceived features — polymorphism, type operators, dependent types, modalities, linearity — whose interactions must be carefully managed. The three axes of the lambda cube (terms depending on types, types depending on types, types depending on terms) each represent an independent capability; the eight vertices of the cube arise from choosing which axes to include. Conventionally, each combination (System F, System Fω, the Calculus of Constructions, etc.) is defined and studied as a standalone system, with its metatheory reproven from scratch for each vertex. But the axes are logically independent features, and a system that supports typed composition of language fragments should equally support typed composition of type-theoretic features: define each axis once as a doctrine functor (`doctrine_functor F(A : SA, ...)`) using explicit parameter namespaces (`A::...`), then apply any combination of them to a base language (`apply F to Target using { A = implA; ... }`) to reach any vertex of the cube — with the interaction of features checked at each composition step rather than verified monolithically.

When these boundaries — whether between languages or between features of a single language — are implicit, the resulting bugs are exactly the ones that are hardest to diagnose: hydration mismatches, effect leakage, incorrect staging, broken serialization, unsound optimization, linearity violations across FFI boundaries. These are not bugs in any single language fragment — they are bugs at the seams.

## The approach

llang treats **each computational fragment as a typed doctrine** (a presented monoidal category with generators, rewrite rules, and structural discipline) and **each boundary between fragments as a typed morphism** (a structure-preserving functor with checked equations). Composition of fragments — whether entire languages or individual type-theoretic features — is pushout of doctrines along shared interfaces.

This means:

1. **A language is not a monolith but a composite.** A system is described by a diagram of doctrines connected by morphisms, rather than by a single grammar. Each doctrine has its own mode (or modes), its own structural discipline, its own types and generators, and its own definitional equality (via oriented rewrite rules with checked confluence and termination). This applies at every level of granularity: a "language" can be a full programming system, but equally it can be a single type-theoretic feature (polymorphism, dependent types, a modality) packaged as a doctrine functor and applied to a base language. The same composition mechanism — morphisms and pushouts — serves both scales.

2. **Interoperation is a morphism.** When fragment A needs to interact with fragment B, the interaction is mediated by a morphism (or a span/cospan of morphisms) that specifies how types, generators, and equations in A map to those in B. The morphism's equation-preservation obligations are checked by proof search, yielding either a certified proof or an explicit "undecided" result. There is no unchecked boundary.

3. **Compilation is a morphism.** A codegen pass from a source doctrine to a target doctrine is a morphism whose equation-preservation guarantees that the compiled output respects the source semantics. Different targets (different browser capabilities, different hardware, different optimization levels) are different target doctrines, and the compilation morphism is parameterized accordingly.

4. **Language composition is pushout.** Combining two language fragments that share a common interface (e.g., a shared type system, a shared structural discipline) is computed as a pushout of doctrines along the interface morphisms. This is the mechanism for building composite systems from independently specified fragments, and it preserves the correctness guarantees of each fragment. The same mechanism composes type-theoretic features: a doctrine functor that adds polymorphism and a doctrine functor that adds dependent types can each be applied independently to a base language, and their combined application is a pushout that checks compatibility of the two features at the shared interface. The result is a modular construction where each feature is defined, validated, and maintained once, rather than re-implemented for each combination.

5. **Structural discipline, effects, and modalities are part of the doctrine, not hardcoded.** Whether a mode admits copying (cartesian), discarding, or neither is determined by which structural interfaces the doctrine implements — not by a built-in discipline lattice. Effects are doctrines. Modalities (functors between modes with 2-cell structure) mediate the interaction between fragments with different disciplines. Modal dependent types allow types in one mode to be indexed by terms in another.

6. **Evaluation strategy is a property of the mode theory, not a global switch.** Which subexpressions can be evaluated at which phase is determined by the mode structure: modes correspond to evaluation phases, modalities correspond to phase transitions, and fragment-driven quotation can reify explicit sharing inside chosen acyclic fragments when a pipeline needs that view. Partial evaluation is the morphism from the composite doctrine to the residualized doctrine, with correctness guaranteed by the morphism laws.

## The endgame

Because doctrines can describe their own compilation pipelines (a compiler is a morphism, a pipeline is a composition of morphisms), and because llang's own elaboration, normalization, and proof search are operations on doctrines:

- **Specialization**: given a fixed pipeline of morphisms, the compiler can be partially evaluated with respect to that pipeline, yielding a specialized compiler for a specific source-target pair. This is the first Futamura projection applied to doctrine morphisms.
- **Incrementalization**: given a morphism to an incremental computation target (e.g., a change-propagation doctrine rather than a batch-evaluation doctrine), the output is a correct-by-construction incremental evaluator — no virtual DOM, no ad-hoc diffing, no manual dependency tracking.
- **Self-hosting**: when llang's own kernel operations (normalization, unification, proof search) are expressed as doctrines, the above specialization and incrementalization apply to llang itself. A specialized, incremental language server for a given doctrine is a derived artifact, not a hand-written tool.

## Guiding invariants for development

The following invariants should hold throughout the development of llang and guide design decisions:

- **Correctness at boundaries is the primary value proposition.** Every design choice should be evaluated by whether it makes cross-fragment correctness cheaper to establish and harder to violate.
- **Decidability boundaries are explicit.** When a check (unification, obligation discharge, termination) cannot be decided within a budget, the result is `undecided`, never silently assumed. The user knows exactly where the boundary of automation is.
- **The kernel is small and the surface is derived.** Doctrines, morphisms, pushouts, and proof-carrying obligations are kernel concepts. Everything else — surface syntax, structural insertion, elaboration convenience, evaluation strategy — is derived from these by the DSL and pipeline layers.
- **Generality is validated by instances.** Every kernel mechanism must be justified by at least one concrete doctrine that uses it in a way that couldn't be expressed without it.
