## Correctness issues

### 1) `validateDiagram` currently allows ill‑formed open diagrams

**Problem:** `Strat.Poly.Graph.validateDiagram` checks internal consistency (back‑pointers, port existence, etc.) but does **not** enforce the standard “open graph” invariant that makes a diagram a well‑defined morphism:

* Inputs should be exactly the ports with **no producer**.
* Outputs should be exactly the ports with **no consumer**.
* Boundary inputs must **not** have producers.
* Boundary outputs must **not** have consumers.
* No duplicated ports in `dIn`/`dOut`.

Right now you can construct diagrams with:

* *Internal* ports with `pCons = Nothing` (silent discarding / dead wires).
* *Internal* ports with `pProd = Nothing` (silent creation / free inputs).
* Boundary ports that are not actually boundary ends.
* Duplicate boundary ports (implicit copy).

This undermines the “no implicit weakening/contraction” goal and will also make rewriting/morphism checking less trustworthy.

**Where:** `src/Strat/Poly/Graph.hs`, function `validateDiagram`.

**Remedy (agent instructions):**

1. Add boundary uniqueness checks:

   * Reject duplicates in `dIn` and in `dOut`.
2. Enforce boundary endpoint conditions:

   * For every `pid ∈ dIn`: require `pProd(pid) = Nothing`.
   * For every `pid ∈ dOut`: require `pCons(pid) = Nothing`.
3. Enforce that boundary lists are *complete* for open ends:

   * For every port `pid`:

     * If `pProd(pid) = Nothing`, then `pid ∈ dIn`.
     * If `pCons(pid) = Nothing`, then `pid ∈ dOut`.
   * This additionally prevents “unused inputs” unless they are also outputs (identity pass‑through), i.e. removes implicit weakening.
4. Add regression tests (new tests, not “golden” string tests):

   * A diagram with a produced port that is neither consumed nor in `dOut` should fail `validateDiagram`.
   * A diagram with an input port that is neither consumed nor also in `dOut` should fail.
   * A diagram with duplicate `dOut` should fail.

---

### 2) `evalGen` hard‑codes semantics for `"dup"`, `"drop"`, `"swap"`

**Problem:** `Strat.Poly.Eval.evalGen` special‑cases generator names `"dup"`, `"drop"`, `"swap"` and interprets them even if they are not declared in the doctrine and not provided by the model.

That is incorrect for a generic kernel:

* It lets diagrams evaluate successfully even if the doctrine doesn’t contain those generators.
* It overrides user intent if a doctrine defines a generator named `"dup"` that is *not* cartesian duplication.
* It violates the “nothing is implicit” direction.

**Where:** `src/Strat/Poly/Eval.hs`, function `evalGen`.

**Remedy (agent instructions):**

1. Remove all name‑based special cases in `evalGen`.
2. Require evaluation to:

   * look up the generator in the doctrine (`lookupGen`),
   * then interpret it via the model (or `DefaultSymbolic`).
3. Provide a standard library model file for cartesian structure, e.g.:

   * `stdlib/struct.cartesian.models.llang` containing model clauses:

     * `dup(x) = [x, x]`
     * `drop(x) = []`
     * `swap(x,y) = [y, x]`
4. Update examples that evaluate diagrams requiring these ops to import that model file.
5. Add tests:

   * Evaluating a diagram containing `"dup"` **must fail** if `"dup"` is not declared in the doctrine.
   * Evaluating must fail if `"dup"` is declared but the model is missing and `DefaultSymbolic` is not selected (or must behave symbolically if that’s the intended fallback).

---

### 3) The current “canonicalization” is not α‑canonicalization

**Problem:** `canonicalizeDiagram` currently renumbers ports/edges primarily by existing IDs (`portKey`, `edgeKey`), i.e. it’s a *renumbering*, not a canonical representative up to renaming/isomorphism.

That means two α‑equivalent diagrams that differ only by internal `PortId`/`EdgeId` naming can fail to compare equal after “canonicalization”. This is a correctness hazard for:

* `Morphism.checkCell` (it canonicalizes and then uses `(==)`),
* `Pretty.renderDiagram` (stability issues),
* any future joinability/coherence checks.

**Where:** `src/Strat/Poly/Graph.hs`, function `canonicalizeDiagram`, plus downstream uses in:

* `src/Strat/Poly/Pretty.hs`
* `src/Strat/Poly/Morphism.hs`
* `src/Strat/Poly/Normalize.hs`

**Remedy (agent instructions):**

1. Either:

   * (Preferred) Implement true α‑canonicalization / canonical labeling independent of original IDs, **or**
   * Add an explicit `diagramIsoEq` (isomorphism‑up‑to‑renaming) and use that instead of `(==)` in correctness‑critical places.
2. Add tests that must pass:

   * Create a diagram, then apply a non‑order‑preserving permutation to internal `PortId`s and `EdgeId`s (helper in test code).
   * The two diagrams must be equivalent under the chosen mechanism (canonical form equality or iso‑equality).
3. If you keep a simple renumbering routine, rename it to something like `renumberDiagram` and stop using it as a semantic equality proxy.

---

### 4) The “no implicit swap/exchange” intent is not enforced by the kernel/surfaces

**Problem:** As implemented, the SSA surface and the underlying hypergraph representation allow implicit permutations whenever types permit, without requiring an explicit `swap` generator. This directly contradicts the stated intent in `FULL-POLYGRAPHS.md` (“planar strict, no implicit swapping”) and blocks any future “exchange is a mode‑theory choice” story.

Examples of implicit exchange currently possible:

* Reordering generator inputs by naming wires out of order.
* Reordering outputs with `out y, x` without constructing a swap diagram.

**Where:**

* `src/Strat/Poly/Surface/SSA.hs` (arbitrary wiring / arbitrary output order)
* More fundamentally: the hypergraph kernel has no planarity/exchange constraint.

**Remedy (agent instructions):**

1. Decide at the kernel level: either the core is **symmetric** (exchange built‑in) or **planar/ordered** (exchange not built‑in).
2. For parity with the existing “struct.symmetric.llang” and the intent in `FULL-POLYGRAPHS.md`, implement **planar/ordered** as the default:

   * Add a planarity/serializability validation condition (or restrict construction so only serializable diagrams can be built).
   * Tighten SSA:

     * Maintain an ordered context (not a pure name→port map).
     * Require generator calls consume a contiguous slice of the current context in order.
     * Require `out` to be order‑preserving; no duplicates; no skipping without explicit `drop`.
3. Gate this by mode if you want multiple disciplines later (exchange allowed in some modes).
4. Add tests that currently pass but should fail in planar mode:

   * A program that “outputs swapped order” without an explicit swap must be rejected.

If you **instead** want the kernel to be symmetric by design, then remove `stdlib/struct.symmetric.llang` as a “discipline” and update docs/spec to say exchange is primitive. That is a breaking semantic choice and should be explicit.

---

## Parity gaps relative to the old (GAT) pipeline

### 1) No auto‑generated `.fromBase` polymorphisms for `polydoctrine … = Base`

Old `doctrine … = Base` generates `X.fromBase`, which the pushout examples rely on. Poly doesn’t.

**Where:** `src/Strat/Kernel/DSL/Elab.hs` (`DeclPolyDoctrine`) and/or `src/Strat/Poly/DSL/Elab.hs`.

**Remedy (agent instructions):**

1. When elaborating `polydoctrine New = Base …`, automatically create and register:

   * `polymorphism New.fromBase : Base -> New` with

     * empty type map (identity),
     * generator map mapping each `Base` generator to itself in `New` via `genD`.
2. Add tests:

   * Declaring an extended polydoctrine makes the morphism appear in the env.
   * The morphism passes `checkMorphism`.
3. Port the poly pushout examples to use `.fromBase` and delete the manual boilerplate polymorphisms.

---

### 2) `run_spec` parity for poly runs is missing

Old has `run_spec` + `run … using Spec`. Poly has no analogous mechanism.

**Where:** DSL AST/Parse/Elab/Loader/RunPoly.

**Remedy (agent instructions):**

1. Add new declarations:

   * `polyrun_spec Name { … }`
   * `polyrun Name using Name { … }` (or match old syntax closely)
2. Extend:

   * `src/Strat/Kernel/DSL/AST.hs`
   * `src/Strat/Kernel/DSL/Parse.hs`
   * `src/Strat/Kernel/DSL/Elab.hs`
   * `src/Strat/Frontend/Loader.hs`
   * `src/Strat/Frontend/Env.hs`
3. Implement spec application in `RunPoly` (merge defaults with run block, same precedence rules as old).
4. Port `examples/runspec/*` to `examples/poly/runspec/*`.

---

### 3) `implements` / interface resolution has no poly analogue

Old supports `implements` and resolving required morphisms automatically when running. Poly runs currently require an explicit `morphisms:` list.

**Remedy (agent instructions):**

1. Add poly equivalents:

   * `polyimplements Interface by polymorphism P : Interface -> Target` (or similar)
2. Extend env with defaults mapping.
3. Add optional `uses:` field to `polyrun` mirroring old behavior:

   * If a polyrun says `uses: I1, I2`, automatically pick default polymorphisms (or error with a clear “missing polyimplements” message).
4. Add tests:

   * A polyrun with `uses:` works without listing morphisms explicitly when defaults exist.

---

### 4) `polysurface` is effectively a stub (no user-defined surfaces)

Right now `polysurface` declarations don’t let users define a language; only built-in SSA (and a hard-coded CartTerm surface name) exist. That’s not parity with the old `surface` + `syntax` pipeline, and it blocks the “publish a compiler as a library” story.

**Remedy (agent instructions):**

1. Minimum viable parity approach (fast path):

   * Reuse the existing `surface`/`syntax` infrastructure as the user-facing way to define languages.
   * Retarget its backend from “produce a core `Term` in a GAT doctrine” to “produce a poly `Diagram` in a polydoctrine” by compiling the elaborated term into a diagram (using explicit `dup/drop/swap` generators from `stdlib/struct.cartesian.llang`).
2. Longer-term (clean path, still poly-native):

   * Allow `polysurface` blocks to define elaboration rules to either:

     * `DiagExpr`, or
     * SSA IR, or
     * directly to `Diagram`.
3. Port `examples/ccc_surface/*` to a poly target via one of the above paths, so the old surface system can be deleted without losing the feature.

---

### 5) Example parity: several “old feature” examples still have no poly equivalent

Concrete gaps in the tree:

* `examples/ccc_surface/*` (surface + syntax + implements + evaluation pipeline)
* `examples/runspec/*` (run_spec)
* Some `examples/pushout/*` scenarios beyond the single poly pushout demo
* The old `ccc.llang` example (the current `examples/poly/ccc.poly.llang` is not demonstrating the same structure)

**Remedy (agent instructions):**

1. Add `examples/poly/ccc_surface/*` demonstrating the same end-to-end pipeline (custom surface + model + normalization/eval).
2. Add `examples/poly/runspec/*`.
3. Port the remaining pushout examples to `examples/poly/pushout/*` and ensure the outputs (rendered normalized forms) match the old ones modulo the renamed symbols expected from `computePolyPushout`.

---

### 6) `show cat` parity is missing for poly runs

`polyrun` errors on `show: cat`, while old runs can show categorical expressions.

**Remedy (agent instructions):**

1. Either implement a poly “cat-like” display:

   * A textual normal form of diagrams as a composition/tensor expression, or
   * A structural pretty-print of the hypergraph.
2. Or explicitly deprecate/remove `ShowCat` globally if it’s not part of the poly route. Right now it’s a silent parity regression.

---

## “Deletion readiness” checklist for removing the old GAT kernel

If “old GAT approach can be deleted” is the target, you need all of the following to be true in-tree:

1. All shipped stdlib theories needed by examples exist as `polydoctrine`s (nat, bool, cartesian, symmetric if applicable).
2. All end-to-end examples have poly equivalents (including surface/syntax + run_spec + pushout).
3. The loader/CLI can run the entire example suite without referencing:

   * `Strat.Kernel.Presentation`, `Strat.Kernel.Term`, old rewrite/morphism/pushout.
4. Tests cover:

   * rewrite correctness,
   * morphism checking,
   * pushouts,
   * surface elaboration,
   * model evaluation.

Right now (based on the bundle contents), items (2) and (3) are not yet satisfied.

---

## Priority order (what to fix first)

1. **Tighten `validateDiagram`** (boundary ends + no duplicates). This is foundational and prevents implicit structural behavior.
2. **Remove eval special-casing** for `"dup/drop/swap"`.
3. **Add auto `.fromBase` polymorphisms** for `polydoctrine extends` (improves pushout parity immediately).
4. **Implement poly run_spec** (direct parity with existing examples).
5. **Decide/enforce exchange semantics** (planar vs symmetric) before more surfaces get written.
6. **Make diagram equality robust** (true α‑canonicalization or iso‑equality).

These are the changes required for the bundle to be correct under its own stated goals and for parity claims (“old GAT can be deleted”) to be defensible.
