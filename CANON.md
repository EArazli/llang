## Resolve first: canonical representation for diagrams (true canonization)

> Implementation note (2026-02-15): This repository currently follows the **fallback path** from this document: a **custom pure-Haskell canonicalizer** is used instead of nauty/Traces integration. The nauty/Traces section remains as the preferred architecture, but is intentionally not implemented here.

This should be done before “fuel” (and most other major cleanups), because:

* **Fuel is currently compensating for the inability to reliably detect repeats.** Your normalizer/reachability code repeatedly calls `renumberDiagram` and then uses `diagramIsoEq` to test membership (`Normalize.reachable`, `reachableWithParents`, etc.). If “canonicalization” doesn’t actually canonicalize, you get state explosion and/or premature “OutOfFuel”, even when the search is looping through isomorphic states.
* **Everything else becomes simpler once equality is cheap and correct.** Pushouts, critical pairs, completion, memoization, confluence checks, rewrite graph exploration, and caching all benefit immediately from having a canonical form + stable hashing.

So I’m treating this as the foundational fix that will cascade into fixing/meaningfully reframing fuel later.

---

## Verify the problem is real in your codebase

### What `renumberDiagram` actually does today

In `Strat.Poly.Graph.renumberDiagram`, internal IDs are renumbered **based on the *existing* numeric IDs**, not based on the *graph structure*:

* It assigns **boundary ports first** in boundary order.
* Then it takes **remaining ports** and sorts them using `sortPorts`, which is by `unPortId` (old numeric ID).
* It assigns edges by sorting using `sortEdges`, which is by `unEdgeId` (old numeric ID).

So if two diagrams are isomorphic but were built with different internal PortId/EdgeId allocations (very common after merges/shifts/unions/rewrite steps), **`renumberDiagram` will generally produce different outputs**.

That exactly matches your “worst of both worlds” description: you pay the overhead of renumbering everywhere, but you don’t get syntactic equality for isomorphic diagrams.

### Consequence: you cannot use `(==)`/`Ord`/`Map`/`Set` on diagrams the way you want

Because the derived `Eq/Ord` instances for `Diagram` are structural over IntMaps + IDs, any mismatch in renumbering decisions prevents syntactic comparison.

This also directly harms algorithms that need to:

* detect repeated states in rewrite exploration,
* deduplicate critical pairs,
* memoize normalization,
* do joinability testing by meeting in a rewrite graph.

---

## The rigorous “best possible” approach: canonize via canonical labeling (graph canonization)

### The core idea

A canonical form is a function `C` such that:

1. `C(D)` is isomorphic to `D`
2. `D1 ≅ D2` iff `C(D1) == C(D2)` syntactically

This is exactly what *canonical labeling* provides for graphs: isomorphic graphs map to the same canonical form. ([drops.dagstuhl.de][1])

Your diagrams are (typed, port-ordered, boundary-ordered) **open directed hypergraphs**. Canonization for that structure is not “invent a clever renumbering heuristic”; it is:

1. **Reduce the diagram isomorphism problem to (vertex-colored) graph isomorphism**
2. Run a **canonical labeling algorithm** (nauty/Traces/Bliss class)
3. Rebuild the diagram using the canonical labeling as the ID order

This is a deep, established approach (it’s the standard industrial approach in chemistry toolchains, compilers that canonicalize flow graphs, etc.), and it’s theoretically clean.

### Why this is not “overkill”

* You already have `diagramIsoEq`, which is effectively solving a constrained graph isomorphism problem by backtracking search.
* Canonical labeling tools implement the same underlying paradigm but far more robustly and efficiently, using decades of refinement/pruning heuristics (the individualization–refinement paradigm). ([arXiv][2])
* Once you have a canonical form, you stop paying GI costs repeatedly: you canonicalize once, then equality is O(size) (or O(1) with hashing).

---

## Grounding in established theory of string diagrams / hypergraphs

Your diagrams are very close to the “hypergraph category” / “string diagrams modulo Frobenius” viewpoint:

* Hypergraph categories can be presented as **cospan-algebras**, and there are coherence theorems supporting reasoning by canonical representatives in objectwise-free settings. ([arXiv][3])
* There is a well-developed line of work interpreting string diagram rewriting as **(double-pushout) hypergraph rewriting** in free hypergraph categories. ([arXiv][4])

That gives you solid theoretical footing for “diagrams are hypergraphs; rewrite is hypergraph rewrite”. Canonization is a representational/algorithmic layer on top: you’re not changing the semantics, you’re giving the implementation the right normal form for “diagram = isomorphism class”.

---

## Define the exact equivalence relation you want to canonize

Your current notion of “same diagram” for iso-equality is essentially:

* Boundary order is fixed: ith input maps to ith input; ith output maps to ith output.
* Port types must match syntactically (`TypeExpr` equality).
* Edge payload “shape” must match (same constructor; `PBox` ignores name; `PFeedback` recurses; etc.).
* Incidence/order matters: `eIns` and `eOuts` are ordered lists, and that order is respected.

This is exactly “isomorphism of an open port-ordered hypergraph with colored vertices/edges and fixed boundary positions”.

We should canonize **that** relation.

---

## Reduction: encode your diagram as a vertex-colored simple graph

To use standard canonizers (nauty/Traces), we reduce your diagram to a plain graph whose isomorphisms correspond exactly to diagram isomorphisms.

A standard reduction for hypergraphs is the **incidence graph**: bipartite between vertices and hyperedges, adjacent when vertex is in hyperedge. ([drops.dagstuhl.de][1])
We extend it with *ordered ports* and *directed input/output structure*.

### Encoding (faithful, order-preserving)

Given a diagram `D` with ports `P` and hyperedges `E`:

Create a graph `G(D)` with vertices of several kinds:

1. **Port vertices**: one vertex `v_p` per port `p ∈ P`
2. **Edge vertices**: one vertex `v_e` per edge `e ∈ E`
3. **Slot vertices**: for each edge `e` and each input position `i`, a vertex `v_{e,in,i}`; similarly for output positions `j`, `v_{e,out,j}`
4. **Boundary position vertices**: for each boundary input position `i`, a vertex `b_in_i`; similarly for boundary outputs `b_out_j`

Add undirected edges in `G(D)`:

* Boundary attachment:

  * connect `b_in_i` — `v_{dIn[i]}`
  * connect `b_out_j` — `v_{dOut[j]}`
* Edge incidence with order:

  * connect `v_e` — `v_{e,in,i}` and `v_{e,in,i}` — `v_{port}` where `port = eIns[i]`
  * connect `v_e` — `v_{e,out,j}` and `v_{e,out,j}` — `v_{port}` where `port = eOuts[j]`

### Vertex colors (to enforce typing, payload, boundary order, and slot order)

Canonical labeling works with an initial vertex partition (“colors”). In nauty/Traces, that is given by `lab`/`ptn`, and canonization respects it. 

Assign a color key to each vertex:

* Boundary position vertices:

  * `color(b_in_i) = BoundaryIn(i)` (each i distinct)
  * `color(b_out_j) = BoundaryOut(j)` (each j distinct)
* Slot vertices:

  * `color(v_{e,in,i}) = SlotIn(i)`
  * `color(v_{e,out,j}) = SlotOut(j)`
    This forces “ith input stays ith input” and similarly for outputs.
* Port vertices:

  * `color(v_p) = Port( typeOf(p), maybeLabelClass(p) )`
    At minimum include port type. (Whether to include labels depends on whether labels are semantic; see below.)
* Edge vertices:

  * `color(v_e) = Edge( payloadKey(ePayload), arityIn, arityOut )`
    The payloadKey must reflect exactly what your iso-equality compares, including recursion into inner diagrams for `PBox`/`PFeedback` and binder-arg diagrams.

### Correctness sketch (why this encoding is right)

* Any diagram isomorphism (bijection on ports+edges preserving boundary order, incidence order, types, payload) induces a color-preserving graph isomorphism of `G(D)` (map each gadget vertex accordingly).
* Conversely, any color-preserving graph isomorphism of `G(D)` must map port vertices to port vertices, edge vertices to edge vertices, preserve boundary positions (unique colors), and preserve slot indices (colors), so it corresponds to a diagram isomorphism.

So canonizing `G(D)` canonizes `D`.

---

## Canonization algorithm

### Step 0: canonicalize recursively-contained diagrams first

Because payloads contain diagrams (`PBox`, `PFeedback`, `BAConcrete`), define:

* `canon(D)` recursively:

  * canonize all child diagrams appearing inside payloads and binder args
  * then canonize the outer diagram structure using `G(D)` labeling

This ensures payloadKey can include a stable representation of child diagrams.

### Step 1: build `G(D)` and its color partition

Build adjacency lists and a deterministic mapping from “vertex kind” → 0..n-1 indices.

Colors:

* Compute a `ColorKey` per vertex.
* Map `ColorKey` to small integers via stable ordering (sort unique keys); this fixes “color order”, which matters for canonical labeling conventions. ([ANU Users][5])

### Step 2: run canonical labeling using a battle-tested engine

Use nauty/Traces:

* They are designed to compute canonical forms/labelings and automorphism groups using the individualization–refinement paradigm. ([arXiv][2])
* The nauty user guide explicitly describes how `lab`/`ptn` represent colored partitions and how canonization is produced. 

Implementation detail: Traces is restricted to simple undirected graphs; our encoding is exactly that, so Traces is applicable.

### Step 3: rebuild the diagram with canonical PortId/EdgeId order

From the canonical labeling result, compute:

* `portOrder`: sort original ports by canonical label of their corresponding `v_p`
* `edgeOrder`: sort original edges by canonical label of `v_e`

Then:

* assign new PortId = 0.. in `portOrder`
* assign new EdgeId = 0.. in `edgeOrder`
* rebuild:

  * `dIn`, `dOut` by mapping old ports through port map (preserving list order)
  * edges: map `eIns/eOuts` via port map; map `eId` via edge map; payload already has canonized subdiagrams
  * recompute `dProd/dCons` from the rebuilt edges (do not “patch” old maps; reconstructing is safer)
  * recompute `dPortTy/dPortLabel` by mapping keys
  * set `dNextPort`, `dNextEdge` to sizes

The output is a canonical representative of the isomorphism class.

---

## What about port labels: should they affect canonization?

Right now:

* `diagramIsoEq` ignores port labels entirely.
* But term-diagram conversion uses input-port labels of the form `tmctx:n` as a mapping hint (`TermExpr.resolveInputGlobal`), which *can* affect interpretation if the boundary is a sparse subset of the context.

This is a real design inconsistency:

* Either labels are **metadata** and should not affect semantics (then term interpretation must not depend on them),
* Or labels are **semantic** and must be included in equality/isomorphism/canonization.

For this canonization task, the clean “won’t need replacement” direction is:

1. **Make semantics not depend on string labels.**
2. If a term diagram needs an input-to-context mapping, represent it explicitly and typed (e.g., a `[TmCtxIndex]` aligned with `dIn`), not via `Maybe Text`.

However, that is a second foundational redesign (term binding/interface). It’s adjacent, but it’s a larger semantic change than strictly required to fix diagram canonization.

So the end-state I recommend is:

* Canonization engine supports a toggle: **labels included or excluded** from port vertex colors.
* Then you can migrate term diagrams to explicit mappings and flip the toggle off, without rewriting canonization again.

---

## End state design

### 1) A new “canonical diagram” type that makes equality trivial

Introduce:

```haskell
newtype CanonDiagram = CanonDiagram { unCanon :: Diagram }
  deriving (Eq, Ord, Show)
```

Invariant: `CanonDiagram` is always validated and canonicalized.

Expose:

* `canonDiagram :: Diagram -> Either Text CanonDiagram`
* `canonKey :: CanonDiagram -> ByteString` (stable hash / serialization-derived fingerprint)
* `diagramIsoEq :: Diagram -> Diagram -> Either Text Bool`
  implemented as `canonDiagram d1 == canonDiagram d2` (or via `canonKey` first)

### 2) Replace `renumberDiagram` everywhere that intends “canonicalization”

* `renumberDiagram` becomes:

  * either deleted,
  * or kept strictly as a **pretty-print normalization** (boundary-first, old-ID-based) but renamed to something honest like `normalizeIdsForDisplay`.
* `Foliation.canonicalizeDiagram` becomes true canonization (calls `canonDiagram`).

### 3) Make rewrite exploration cacheable and terminating-by-construction (no “fuel for dedup”)

Once diagrams have canonical keys, rewrite exploration should use:

* a `HashSet canonKey` visited set,
* a queue/worklist for BFS/DFS,
* explicit bounds on:

  * depth, or
  * number of nodes explored, or
  * cost measure (size growth), etc.

Fuel then becomes a policy choice, not a correctness crutch.

(You can still keep a depth bound; but the *loop prevention* should come from canonical visited-set dedup, not from hoping fuel runs out.)

---

## Payoff

### Immediate, high-impact payoffs

* **Syntactic equality for isomorphic diagrams**: `CanonDiagram` can go into `Map/Set` directly.
* **Huge speedups in normalization/joinability/reachability**: visited-set checks become hash lookups, not repeated backtracking GI checks.
* **Eliminates a large class of “duplicate critical pair / duplicate match / duplicate rewrite node” bugs**.
* **Makes “fuel” a user-level resource limit rather than a correctness mechanism**.

### Secondary payoffs

* Simplifies code: remove “renumber everywhere”, remove repeated iso checks.
* Makes debugging deterministic: printing a canon diagram always yields the same IDs.

---

# Implementation document for a coding agent

This is written as an actionable plan, assuming you can change anything and do not need backwards compatibility.

## A. Add canonization backend

### A1. Choose the canonization engine

Preferred: **nauty/Traces** (C library), via Haskell FFI, because it is the standard, well-tested solution. ([arXiv][2])

Alternative (fallback): a pure-Haskell canonizer (slower), used only if you want to avoid C. (Given your “no effort constraints” stance, use nauty.)

### A2. Vendor nauty/Traces into the repo

* Add `cbits/nauty/` containing nauty + Traces sources and headers.

* Add a small wrapper C file `cbits/llang_canon.c` exposing one function:

  **Inputs**:

  * `n` vertices
  * adjacency as edge list `(u,v)` for simple undirected graph
  * color class partition as an array `colors[n]` (integers)

  **Outputs**:

  * canonical labeling `lab[n]` (or a permutation array you define)

* Internally, the wrapper should:

  * build a `sparsegraph` or `graph` (dense) structure
  * build `lab`/`ptn` arrays from the colors:

    * sort vertices by color so same colors are contiguous
    * set `ptn` zeros at cell boundaries as described in the nauty manual 
  * call `Traces(...)` or `sparsenauty(...)` with `getcanon = TRUE`
  * return the `lab` permutation

Reference: nauty manual describes the `lab`/`ptn` format and that `lab` gives the labeling (and `canong` gives canon graph) when `getcanon=TRUE`. 

### A3. Wire the build

* In `llang.cabal`:

  * add `c-sources: cbits/llang_canon.c ...`
  * add `include-dirs: cbits/nauty`
  * ensure required nauty sources compile (may need `cc-options`)

* Add a CI/local build target to confirm `cabal test` or `stack test` works.

## B. Implement diagram → colored graph encoding

Add module: `src/Strat/Poly/GraphCanon.hs`

### B1. Define internal vertex kinds

```haskell
data V
  = VPort PortId
  | VEdge EdgeId
  | VSlotIn EdgeId Int
  | VSlotOut EdgeId Int
  | VBoundIn Int
  | VBoundOut Int
  deriving (Eq, Ord, Show)
```

Maintain deterministic enumeration:

* boundary position vertices first (in order)
* then ports sorted by `PortId`
* then edges sorted by `EdgeId`
* then slot vertices in deterministic order (edges then slots)

### B2. Define color keys

```haskell
data ColorKey
  = CKBoundIn Int
  | CKBoundOut Int
  | CKSlotIn Int
  | CKSlotOut Int
  | CKPort TypeExpr (Maybe TextOrLabelKey)  -- decide label policy
  | CKEdge PayloadKey Int Int               -- include arities
  deriving (Eq, Ord, Show)
```

`PayloadKey` must be structural and recursive:

* `PGen`: include `GenName`, normalized `AttrMap`, and list of binder-arg keys
* `PBox`: include canonKey of inner diagram (ignore BoxName to match current iso-eq)
* `PFeedback`: include canonKey of inner diagram
* `PSplice`: include BinderMetaVar text
* `PTmMeta`: include `sameTmMetaId`-relevant parts (name + scope; optionally sort too)

### B3. Recursive canonization dependency

Expose an internal function:

* `canonDiagramRaw :: Diagram -> Either Text Diagram` (returns plain canonical Diagram)
  and public:
* `canonDiagram :: Diagram -> Either Text CanonDiagram`

In `canonDiagramRaw`:

* first traverse payloads and binder args:

  * recursively canonize any inner diagrams and replace them in the payload
* then encode the outer diagram as `G(D)` and call canonical labeling

### B4. Build adjacency list

Produce edge list `[(Int,Int)]` over indices 0..n-1, without duplicates.

### B5. Call C canonizer

FFI:

```haskell
foreign import ccall unsafe "llang_canon_label"
  c_llang_canon_label :: ...
```

Return labeling info.

## C. Rebuild the canonical diagram

### C1. Extract canonical order for ports and edges

Compute:

* `canonLabelOf :: V -> Int` (from labeling permutation)
* `portOrder = sortOn canonLabelOf [VPort p | p <- ports]`
* `edgeOrder = sortOn canonLabelOf [VEdge e | e <- edges]`

Create maps:

* `portMap :: Map PortId PortId`
* `edgeMap :: Map EdgeId EdgeId`

### C2. Reconstruct all diagram fields from scratch

Avoid “patching” IntMaps (bug-prone). Build:

* `dPortTy'` by mapping old keys through `portMap`
* `dPortLabel'` similarly
* `dEdges'` by:

  * mapping edge ids using `edgeMap`
  * mapping ins/outs through `portMap`
  * payload already has canonized children
* then recompute `dProd'`/`dCons'` from edges deterministically
* `dIn'`, `dOut'` by mapping boundary lists through `portMap` in place
* `dNextPort = nPorts`, `dNextEdge = nEdges`

Finally run `validateDiagram` as a postcondition.

## D. Replace old “canonicalization” uses and equality uses

### D1. Replace `renumberDiagram` call sites that expect canonicalization

* `Strat.Poly.Normalize`: replace every `renumberDiagram` with `canonDiagramRaw` (or `unCanon <$> canonDiagram`)
* `Strat.Poly.Foliation.canonicalizeDiagram`: replace with true canonization
* `Strat.Poly.Rewrite`: canonicalize rewrite results using canonization, not renumbering

### D2. Change `diagramIsoEq`

Implement as:

* `diagramIsoEq d1 d2 = (==) <$> canonDiagramRaw d1 <*> canonDiagramRaw d2`

Optionally keep the old backtracking iso checker as `diagramIsoEqSlow` (private) for testing only.

## E. Tests: add, update, and use as correctness oracle

### E1. Add new test module: `test/Test/Poly/Canon.hs`

Add QuickCheck properties:

1. **Idempotence**

   * `canon(canon(d)) == canon(d)`

2. **Agreement with old isomorphism (small diagrams)**

   * For randomly generated small well-typed diagrams:

     * `diagramIsoEqSlow d1 d2 == (canon d1 == canon d2)`
       Keep sizes tiny to avoid GI blowups.

3. **Regression: renumberDiagram is not canonical**

   * Construct two isomorphic diagrams differing only by internal PortId allocation order.
   * Assert:

     * `renumberDiagram d1 /= renumberDiagram d2`
     * `canon d1 == canon d2`

4. **Symmetry stress**

   * Diagram with multiple identical generator edges in parallel (high automorphism).
   * Canonization should be deterministic and stable.

### E2. Update existing tests

Any test asserting about `renumberDiagram` output should switch to canonization or to “display normalization” if that’s what was intended.

## F. Spec updates

Update `SPEC.md` with:

1. **Definition of diagram isomorphism** (boundary order fixed; port types compared syntactically; edge payload compared structurally; incidence order preserved).
2. **Definition of canonical form**:

   * Diagrams are canonized by reduction to a vertex-colored graph and canonical labeling.
3. Clarify status of:

   * Box names (`PBox`) are annotations (ignored by equality), matching current implementation.
   * Port labels: explicitly state whether they are semantic; if not, move them to “metadata” section and forbid them from affecting term interpretation (or document the new explicit mapping design if you do that next).

---

## What the agent should use to self-check correctness

1. **Round-trip invariants**

   * After canonization, `validateDiagram` must succeed.
   * Counts must match: number of ports/edges unchanged.

2. **Equality correctness**

   * For any `d`: `diagramIsoEq d d == True`
   * For random pairs small: compare to slow oracle

3. **Stability**

   * Canonization output must be byte-for-byte stable across runs (no nondeterminism from Maps/Sets traversal).
     If instability occurs: enforce deterministic ordering wherever you enumerate keys (always sort).

4. **Performance sanity**

   * Normalization reachability should explore far fewer nodes on examples that previously “ballooned”.

---

## Why this won’t need replacement later

* Canonical labeling is a *general*, *theory-backed* solution to canonical representatives of isomorphism classes. ([drops.dagstuhl.de][1])
* Your diagram notion is a structured hypergraph; reduction to colored graph canonization is standard (incidence graph technique) and fully faithful. ([drops.dagstuhl.de][1])
* It composes cleanly with future upgrades:

  * If you later change what counts as “equal” payloads (e.g., treat more labels as metadata), you only change color keys—**the canonizer stays**.
  * If you later move to a more semantic notion of diagram equality (e.g., quotient by additional axioms), canonization remains the canonical form for the *structural* layer, and the semantic quotient is handled by rewriting/e-graphs on top.
