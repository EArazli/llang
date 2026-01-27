## 1. What changed in the new bundle (high‑signal delta)

Compared to the previous GAT-centric codebase, this bundle introduces a *second kernel* centered on **typed string diagrams as hypergraphs** (“polygraphs”):

* New core data: `Strat.Poly.Graph` (`Diagram`, `Edge`, `PortId`, `EdgeId`) with explicit producer/consumer incidence maps.
* Diagram combinators: `Strat.Poly.Diagram` (`idD`, `genD`, `compD`, `tensorD`, plus validation).
* Subdiagram matching + DPO-style rewriting: `Strat.Poly.Match`, `Strat.Poly.Rewrite`, `Strat.Poly.Normalize`.
* A dedicated DSL front-end: `polydoctrine ... where { ... }` and `polyrun ... where { ... } --- <diag expr>`.
* Example polydoctrines (planar/symmetric/cartesian structural libraries) in `stdlib/struct.*.llang` and examples in `examples/poly/`.
* Unit tests for the poly stack: `test/Test/Poly/*`.

This is a real “polygraph kernel” now, not just a plan.

---

## 2. Correctness issues (real bugs / spec mismatches) and precise agent instructions

### 2.1 Matching is **not injective** on edges or ports (violates “embedding” and can crash rewriting)

**Where:** `Strat.Poly.Match`
**Problem:** `extendMatch`/`portsCompatible` only enforce *functional* mapping `patPort -> hostPort`, but not injectivity of the host image. Same for edges. This permits:

* two distinct pattern edges mapping to the same host edge
* two distinct pattern ports mapping to the same host port

This contradicts the spec language (“embedding”) and breaks `rewriteOnce` because `deleteMatchedEdges` will attempt to delete the same host edge twice (and error), and `deleteMatchedPorts` can attempt to delete the same host port twice.

**Agent instructions (must-do):**

1. Extend `Match` with *inverse/used sets*:

   * `mUsedHostPorts :: Set PortId`
   * `mUsedHostEdges :: Set EdgeId`
     (or store inverses `mPortsInv`, `mEdgesInv`).
2. In `extendMatch`:

   * Reject mapping `patEdge -> hostEdge` if `hostEdge ∈ mUsedHostEdges`.
   * For each newly-mapped port `p -> h`, reject if `h ∈ mUsedHostPorts`.
   * Keep allowing the case where `p` is already mapped to the same `h`.
3. Update `portsCompatible` to also check the injectivity constraint for *unmapped* pattern ports by consulting `mUsedHostPorts`.
4. Add tests:

   * Construct a pattern that is a tensor of two identical generators and a host with only one; ensure **no match** is found.
   * Construct a rule where a non-injective match would be “first” in your search order; ensure rewriting never errors (should either not match or match injectively).

This single fix removes a whole class of “mysterious rewriteOnce: missing edge” failures.

---

### 2.2 Rule type variables are recorded but **unused**; type unification is too permissive and semantically wrong for polymorphic reasoning

**Where:** `Strat.Poly.Rewrite` and `Strat.Poly.Match`
**Problem:** `RewriteRule` has `rrTyVars`, but `rewriteOnce` calls `findFirstMatchNoDoc` which unifies types with `unifyTy` **without restricting which type variables may be instantiated**.

This is not a minor nit: it changes the meaning of polymorphism. For equations with type variables (e.g. checking morphisms on schematic 2-cells), you generally want:

* rule type variables = *flexible* (can be instantiated by matching)
* host type variables = *rigid parameters* (must not be “solved” by matching)

Right now, the unifier can bind host variables (because `unifyTy` is symmetric), which is both:

* semantically dubious (specializes the host schematic)
* operationally dangerous (can create a match that later fails `mergePorts` type equality).

**Agent instructions (must-do, aligns with the presence of `rrTyVars`):**

1. Implement a **one-way / guarded** unifier:

   * `unifyTyFlex :: Set TyVar -> TypeExpr -> TypeExpr -> Either Text Subst`
     where only `TyVar ∈ flexSet` may be bound. Any `TVar v` not in `flexSet` is treated as a rigid constant.
2. Thread `flexSet` through matching:

   * Add `findFirstMatchWithTyVars :: Set TyVar -> Diagram -> Diagram -> Either Text (Maybe Match)` and `findAllMatchesWithTyVars ...`.
   * In `extendMatch.unifyPorts`, call `unifyTyFlex flexSet (applySubstTy subst pTy) hTy`.
3. In `Strat.Poly.Rewrite.rewriteOnce` / `rewriteAll`, call the `WithTyVars` matcher with `flexSet = Set.fromList rrTyVars`.
4. (Optional but recommended) assert `Set.fromList rrTyVars == freeVars(rrLHS)` in `validateDoctrine`/rule elaboration, so the declared tyvar list isn’t lying.

This gives you parametric polymorphism behavior that is consistent with how your legacy GAT telescope variables behaved.

---

### 2.3 `validateDiagram` is incomplete (one-directional) and permits states that later crash `canonicalizeDiagram`

**Where:** `Strat.Poly.Graph.validateDiagram`
**Problem:** It checks:

* every edge’s ports exist
* for each edge incidence, `dProd/dCons` points back to that edge
* for each port in `dPortTy`, `dProd` and `dCons` entries exist

But it does **not** check the reverse direction:

* if `dProd[p] = Just eid`, then `eid` exists in `dEdges` and `p ∈ eOuts(eid)`
* if `dCons[p] = Just eid`, then `eid` exists and `p ∈ eIns(eid)`

It also does not ensure keyset equality:

* `keys(dPortTy) == keys(dProd) == keys(dCons)` (no extras)

If stale incidence entries exist, `canonicalizeDiagram` will call `mapEdge` on an `EdgeId` not present in `edgeMap` and `error`.

**Agent instructions (must-do):**

1. Strengthen validation:

   * Enforce keyset equality between `dPortTy`, `dProd`, `dCons`.
   * For each port key `k`:

     * if `dProd[k] = Just eid`, check `eid` exists and `PortId k ∈ eOuts`.
     * if `dCons[k] = Just eid`, check `eid` exists and `PortId k ∈ eIns`.
2. Add “no duplicate port usage inside an edge” sanity checks:

   * `eIns` and `eOuts` lists should have no duplicates.
   * (And optionally disallow overlap between `eIns` and `eOuts` unless you explicitly want that.)
3. Add test(s) that intentionally introduce a stale incidence and ensure validation fails (not crash later).

This makes diagram validity robust enough that the rest of the code can safely rely on it.

---

### 2.4 Unsafe `error` paths in core library code

**Where:**

* `Strat.Poly.Graph.canonicalizeDiagram` uses `error` on missing maps
* `Strat.Poly.Diagram.diagramDom/diagramCod` use `error` if a boundary port lacks a type
* `Strat.Poly.Match.lookupEdge` uses `error` on missing edge id

Given you already return `Either Text` in most places, these are unacceptable failure modes.

**Agent instructions:**

1. Make `canonicalizeDiagram :: Diagram -> Either Text Diagram` (or `canonicalizeDiagramSafe`), and update call sites:

   * `Strat.Poly.Pretty.renderDiagram`
   * `Strat.Poly.Normalize`
   * `Strat.Poly.Rewrite` (`canonicalizeDiagram` after rewrite)
2. Similarly make:

   * `diagramDomE :: Diagram -> Either Text [TypeExpr]`
   * `diagramCodE :: Diagram -> Either Text [TypeExpr]`
     and update `compD`/`tensorD`/`genD`/etc to use the safe variants (or ensure validation is called before any use and enforce that).
3. Replace `lookupEdge` with an `Either` and thread errors upward.

The goal is: **no pure `error` in the poly kernel**.

---

### 2.5 `polyrun` selects a mode nondeterministically (set iteration) and can silently pick the wrong one

**Where:** `Strat.Frontend.RunPoly.firstMode` chooses `S.toList (mtModes)` head.
Sets are unordered; this is nondeterministic and breaks multi-mode doctrines (which you explicitly want long term).

**Agent instructions (must-do):**

1. Extend `RawPolyRun` / `PolyRunSpec` to include `Maybe ModeName` (or mandatory `ModeName`).
2. Extend `polyrun` block syntax to allow `mode M;`.
3. In elaboration / execution:

   * If mode not specified and doctrine has exactly one mode: use it.
   * Otherwise: error “polyrun requires an explicit mode for multi-mode doctrines”.

---

### 2.6 `insertDiagram`/union-style merges silently overwrite on key collisions

**Where:** `Strat.Poly.Rewrite.insertDiagram`, `Strat.Poly.Morphism.insertDiagram`, and `Diagram.unionDiagram` use `IM.union` (left-biased) without asserting disjointness.

If shifting logic is ever wrong, you get silent corruption.

**Agent instructions:**

1. Replace with a checked union:

   * `unionDisjointIntMap :: Text -> IntMap a -> IntMap a -> Either Text (IntMap a)`
     that fails if `intersection(keys m1, keys m2) ≠ ∅`.
2. Use the checked union in:

   * `insertDiagram`
   * `unionDiagram`
3. Add tests that intentionally violate disjointness and ensure you get a useful error.

---

## 3. Feature gap analysis: what the polygraph route currently lacks vs the legacy GAT route

Below is the missing set I would treat as “parity blockers” given your stated requirements (modularity, user-definable EDSLs, no kernel cartesianness assumptions).

### 3.1 No polygraph morphisms in the DSL / environment (despite `Strat.Poly.Morphism` existing)

Legacy GAT has:

* named morphisms in files
* morphism checking
* pushouts built from morphisms

Poly currently has:

* a Haskell `Morphism` type + checker
* **no way to declare/store/use them in `.llang`**

**Parity requirement:** users must be able to publish compiler passes / semantics / translations as libraries ⇒ morphisms must be first-class.

---

### 3.2 No pushouts/colimits for polydoctrines

Legacy has `doctrine X = pushout f g;` with pushout morphisms.
Poly has only `extends`.

You explicitly asked for **pushouts/colimits of polygraph doctrines**. This is also the backbone of “EDSL mixing” without ad-hoc glue code.

---

### 3.3 No surface system that elaborates to diagrams (only a fixed diagram-combinator expression language)

Legacy has:

* surfaces + syntaxes
* user-definable elaboration rules (Surface2)
* runs can choose a surface/syntax/model pipeline

Poly has:

* only `DiagExpr` with `id`, generator call, `;`, `*`
* no variable binding / naming / scoping
* no “surface definitions” as libraries

You explicitly require a surface language elaborating directly to diagrams.

---

### 3.4 No boxes / hierarchical diagrams (explicit requirement)

Your spec plan mentions boxes/hierarchy; current kernel diagrams are flat.
Without hierarchy you can’t:

* modularize large diagrams (crucial for real EDSLs)
* represent “local subprograms” cleanly
* support later higher-order encodings if you choose that path

You explicitly require boxes/hierarchy.

---

### 3.5 No models/evaluation pipeline for diagrams (needed for “compile to CUDA/JS/…” use cases)

Legacy has models (`model ... where { ... }`) and runs can output values / categories.
Poly `polyrun` can only print normalized diagrams.

Your motivating examples (ML, web, game engine) require **interpreting diagrams**:

* as code generators (strings/ASTs)
* as semantic evaluators
* as compilers (diagram-to-diagram via morphisms, then diagram-to-code via a model)

So poly needs a model layer and run integration.

---

### 3.6 Multi-mode composition story is underdeveloped in morphisms and mapping keys

Even aside from the `polyrun` issue, the current poly `Morphism` type is keyed only by `TypeName` and `GenName`, while the doctrine stores them **per mode**. That’s a structural mismatch that will become painful later.

This is exactly the kind of “big-ticket” design issue that is hard to retrofit.

---

## 4. Agent instructions to bring polygraphs up to feature parity with GAT (including your explicit items)

I’m going to fix the target design now (no open design branches), and then give a migration plan in agent steps.

### Target design choices (fixed)

1. **Kernel remains assumption-light:** no built-in cartesian/symmetric/etc; structural discipline is provided by user libraries (your `stdlib/struct.*` already matches this).
2. **Modes are first-class and must be supported end-to-end**:

   * every generator/type is mode-indexed
   * morphisms are mode-aware (even if initial implementation only supports identity mode maps)
3. **Pushouts/colimits are supported** for *inclusion/renaming-style morphisms* (same restriction as the legacy pushout code effectively assumes). This covers the intended modular composition workflow (extend base theories, then glue).
4. **Surfaces elaborate to diagrams**; initially via a “diagram SSA surface” (explicit wiring, no implicit structural operations) plus a cartesian convenience surface if the doctrine imports/extends a cartesian-structure library.
5. **Boxes exist as hierarchical containers**; rewriting and normalization recurse into boxes (outermost-leftmost strategy). Initial milestone: boxes are opaque to matching unless explicitly matched as a node of its own (no second-order metavariables yet).

These choices keep the kernel neutral, make mode theory real, and keep the transition incremental.

---

### 4.1 Add poly morphisms as first-class DSL declarations

**Agent tasks:**

1. Extend AST:

   * Add `RawPolyMorphism` to `Strat.Kernel.DSL.AST`.
   * Add `DeclPolyMorphism RawPolyMorphism` to `RawDecl`.
2. Parser:

   * Add `polymorphism <Name> : <Src> -> <Tgt> where { ... }` block.
   * Inside:

     * `type <SrcType> @<Mode> -> <TgtTypeExpr> @<Mode>` (or initially require same mode)
     * `gen <SrcGen> @<Mode> -> <DiagExpr>` (where `<DiagExpr>` elaborates in the target doctrine/mode)
     * `policy ...; fuel ...;` (reuse existing rewrite policy strings)
3. Elaboration:

   * Produce a `Strat.Poly.Morphism.Morphism` value.
   * Validate that:

     * every source generator has a mapping
     * mapping diagrams are well-typed in target doctrine
     * mapping diagram mode matches mapped mode (until you add true mode mapping)
4. Environment:

   * Add `mePolyMorphisms :: Map Text PolyMorphism`.
   * Update `mergeEnv` and loader to include these.
5. Tests:

   * A `.llang` example file declaring the monoid→string-monoid morphism currently built in Haskell test.
   * End-to-end `checkMorphism` from the DSL output.

**Note:** while doing this, fix the “mode indexing mismatch” by updating the poly morphism representation now (see §4.6).

---

### 4.2 Implement pushouts/colimits for polydoctrines

**Agent tasks:**

1. Add a poly pushout module: `Strat.Poly.Pushout`.
2. Restrict supported morphisms (for v1) to **inclusion/renaming morphisms**:

   * type map must be a pure constructor rename template
   * gen map must map to a *single generator edge* (rename), not an arbitrary diagram
   * mode map identity-only for now
   * require injectivity like the legacy pushout code does
3. Implement:

   * `computePolyPushout :: Text -> PolyMorphism -> PolyMorphism -> Either Text PolyPushoutResult`
     returning:
   * the pushout doctrine
   * the injection morphisms from each target into the pushout
4. Add DSL:

   * `polydoctrine D = pushout f g;`
     where `f` and `g` are poly morphism names.
5. Colimits:

   * Provide `polydoctrine D = coproduct A B;` as `pushout` over an empty doctrine with inclusions.
   * Provide `polydoctrine D = coequalizer f g;` later (optional).
6. Update env loader accordingly.

This restores the legacy “compose theories modularly” story for polydoctrines.

---

### 4.3 Add boxes/hierarchy to the diagram kernel (as per your spec)

**Agent tasks:**

1. Extend the graph data model:

   * Replace `Edge` with:

     ```haskell
     data EdgePayload
       = PGen GenName
       | PBox BoxName Diagram   -- nested diagram, same mode as outer edge
     data Edge = Edge { eId, ePayload, eIns, eOuts }
     ```
   * Add `BoxName` newtype.
2. Define invariants:

   * For `PBox b inner`:

     * `dMode inner == dMode outer diagram`
     * `dIn inner` length/types match `eIns` length/types
     * `dOut inner` length/types match `eOuts`
3. Update:

   * `validateDiagram` to recurse into boxes and check boundary agreement.
   * `shiftDiagram`, `canonicalizeDiagram` to recurse into inner diagrams.
   * `mergePorts` must update ports across all edges; for `PBox`, it must update the inner diagram too.
4. Extend matching/rewrite/normalize strategy:

   * **Rewrite strategy**: outermost-leftmost with recursion into boxes:

     1. try rewrite at top level
     2. if none, iterate edges in id order; when encountering a `PBox`, try rewriting inside it (recursively) before continuing.
   * This is enough to make boxes usable immediately without adding second-order metavariables.
5. Extend surface syntax (next section) to construct boxes.
6. Add tests:

   * A diagram containing a box where a rewrite only applies inside; ensure normalization rewrites inside and preserves outer structure.

This gives you hierarchical diagrams without special-casing cartesian/symmetric/etc.

---

### 4.4 Provide a surface language that elaborates directly to diagrams

Do **not** try to immediately port the full generality of Surface2. Instead, implement a surface that is:

* expressive enough for day-1 real users
* mode-respecting (no implicit structural rules)
* easy to elaborate into diagrams

#### Surface v1: “SSA wiring surface”

**Core idea:** a block introduces named wires; each statement applies a generator to named inputs producing named outputs. No duplication or dropping unless the doctrine provides generators and the user calls them.

Example sketch:

```
polysurface MySurf : doctrine Monoid mode M where { }

polyrun R where { doctrine Monoid; mode M; surface MySurf; }
---
diag {
  in  x:A, y:A, z:A;
  t <- mul(x,y);
  u <- mul(t,z);
  out u;
}
```

**Agent tasks:**

1. Add poly surfaces to DSL/env:

   * `polysurface Name : doctrine D mode M where { ... }` (v1 can be mostly just “select doctrine/mode + parser selection”)
2. Implement parsing of the SSA block into an AST:

   * `in` declarations define boundary ports and their types
   * statements `v1, v2 <- gen(args...)` produce outputs
   * `out ...` final boundary
3. Elaboration algorithm:

   * Maintain an environment `wireName -> PortId`.
   * Start with an empty diagram and allocate ports for `in`.
   * For each statement:

     * look up input ports
     * allocate fresh output ports with declared types (or infer from generator decl)
     * addEdge for the generator (or a box edge if statement is `box {...}`)
   * Set `dOut` from `out`.
4. Type checking:

   * For v1, require all types are explicit in `in`/`out` and possibly outputs. (You can relax later.)
   * Check that generator’s typed arity matches the provided wire types (instantiate tyvars if allowed).
5. Hook into `polyrun`:

   * add `surface` option to `RawPolyRun` so a run chooses SSA parsing instead of the current DiagExpr parsing.

This gives you an ergonomic, fully diagram-native surface without importing cartesianness.

#### Cartesian convenience surface (to recover the old “term language” feel)

This is the parity bridge for “Haskell-like” ergonomic programming in a cartesian discipline:

* It elaborates variable reuse and unused variables by inserting `dup`/`drop`/`swap` **from a library doctrine** (e.g. `StructCartesian`), not kernel special cases.
* You can implement it as a compiler from a simple term AST into diagrams.

**Agent tasks:**

1. Provide a built-in poly surface `CartTermSurface` that:

   * requires the doctrine to provide `dup` and `drop` generators (and optionally `swap`) with the conventional polymorphic types.
2. Implement term→diagram compilation:

   * variables become wires in context
   * function application inserts the appropriate structural rearrangements (swap) to align wires
   * variable reuse inserts `dup`
   * unused variables insert `drop`
3. This surface is *the* path to “define a Haskell-like language as a doctrine + surface + model”.

You can keep the SSA surface as the neutral baseline.

---

### 4.5 Add models/evaluation for diagrams (needed for your ML/JS/game-engine motivations)

You already have the right conceptual slot in FULL-POLYGRAPHS (Milestone 9): interpret diagrams by mapping generators to backend operations and then executing the graph.

**Agent tasks (v1, minimal but useful):**

1. Introduce `PolyModel`:

   * maps each generator (mode-qualified) to a backend primitive (Haskell function or an AST node builder).
2. Execution strategy v1:

   * Only evaluate **acyclic** diagrams (DAGs) by topological sorting edges using producer/consumer incidence (your representation makes this straightforward).
   * Treat `dIn` as inputs, compute values for produced ports, return `dOut`.
3. Integrate into runs:

   * Extend `polyrun` with optional `model Name;`
   * Extend show flags to support `show_value` again for polyrun when a model is present.

Later you can support cycles via traced/feedback doctrines, but v1 gets you compilation pipelines immediately (generate ASTs, strings, etc.).

---

### 4.6 Fix poly morphisms to be mode-aware (big-ticket, do it now)

Current poly `Morphism` is structurally inconsistent with `Doctrine` being mode-indexed.

**Agent tasks (do now, before DSL hardens):**

1. Change mapping keys:

   * `morTypeMap :: Map (ModeName, TypeName) TypeExpr`
   * `morGenMap  :: Map (ModeName, GenName) Diagram`
2. Thread `ModeName` everywhere `applyTypeMapTy` is called:

   * `applyTypeMapTy :: Morphism -> ModeName -> TypeExpr -> TypeExpr`
3. Update `checkMorphism` to iterate `(mode, gen)` pairs and lookup by the pair.
4. Update tests accordingly.

Even if you keep `morModeMap` identity-only for now, making morphisms *mode-indexed* prevents a major refactor later.

---

## 5. “Bring polygraphs up to parity with GAT” beyond the explicit list

This is the rest of the parity delta that will bite you later if you ignore it now.

### 5.1 Legacy term/surface/model pipeline should be recoverable on top of polygraphs (compatibility path)

You don’t need dependent types in the poly kernel to preserve legacy expressiveness; you can preserve the old pipeline by *compiling the old core to diagrams in a cartesian doctrine*.

**Agent tasks (compat layer):**

1. Implement `KernelTerm -> PolyDiagram` compilation for doctrines that extend a cartesian-structure polydoctrine.
2. Implement `KernelDoctrine -> PolyDoctrine` embedding for the “cartesian interpretation” of term theories:

   * each op becomes a generator
   * equations become rewrite rules (as diagrams)
3. Route legacy normalization through the poly normalizer when the embedding is enabled.

This gives you parity in practice even before you port Surface2 itself.

### 5.2 Rewrite policies / structural vs computational control in `polyrun`

Legacy runs can choose rewrite policy; poly run currently can’t (except inside morphism checking code).

**Agent tasks:**

* Add `policy ...;` to `polyrun` blocks and reuse `rulesFromPolicy` (move it to `Strat.Poly.Rewrite` and share).
* Default policy should match legacy defaults (whichever you consider standard).

### 5.3 Proof layer and “optimizations as libraries” (even if performance is postponed)

You can postpone e-graphs, but you should not postpone *packaging rewrite systems + proofs*.

**Agent tasks:**

* Make poly 2-cells first-class exports (already are in doctrines).
* Add a `polyproof` or `theorem` mechanism later; for now, ensure morphism checking and joinability are stable and have good error reporting.

---

## 6. Minimum viable migration order (keeps work incremental, avoids rewrites)

1. **Correctness fixes** (injective match, rrTyVars-driven matching, strengthen validation, remove `error`, polyrun mode selection, disjoint unions).
2. **Mode-aware morphism representation** (before adding DSL).
3. **Poly morphism DSL + env storage** (so libraries can publish translations).
4. **Poly pushout** (so doctrines can be combined modularly).
5. **Boxes/hierarchy in kernel + recursive normalize/rewrite**.
6. **SSA diagram surface + run integration** (surface elaborates to diagrams).
7. **Poly models/evaluation** (enables ML/JS/GPU pipelines).
8. Optional: legacy GAT→poly compat compiler (parity bridge), then gradually retire legacy kernel components.

This sequence avoids “big rewrites” and prevents locking in the wrong abstractions.

