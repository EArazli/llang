# llang Specification (Current)

This document describes the current kernel and DSL surface used by this repository.

## 1. Core Model

A doctrine is the kernel object:

- modes and modalities (`mode`, `modality`, `mod_eq`)
- types and generators
- rewrite cells (`computational` and `structural`)
- modality actions (`action`)
- schema obligations (`obligation`)

There is no `structure` keyword and no `adjunction` keyword.

## 2. Type Layer

### 2.1 Type Expressions

```hs
TypeExpr = TVar TyVar | TCon TypeRef [TypeArg] | TMod ModExpr TypeExpr
TypeArg  = TAType TypeExpr | TATm TermDiagram
```

`TermDiagram` is graph-backed and represented as:

```hs
newtype TermDiagram = TermDiagram { unTerm :: Diagram }
```

Dependent parameters are declared with `PS_Tm sort` in type signatures.
Inside term diagrams, term metavariables are represented with graph payload `PTmMeta TmVar`.
The kernel may also insert `PInternalDrop` nodes in term diagrams to consume unused
required boundary-prefix inputs; this payload is internal-only and not surface syntax.
`dTmCtx` is the bound-term telescope for the diagram.

### 2.2 Definitional Equality

Type normalization and term-argument normalization are performed by `normalizeTypeDeep`.
For `TATm`, normalization uses compiled first-order term rewriting in the term mode:

- rewrite rules come from computational `Cell2` equations (`ttTmRules`) compiled to TRSs
- normalization is fuel-free (`normalizeTermExpr` on `TermExpr`)
- doctrines are rejected if term TRSs fail:
  - SCT-based termination check
  - critical-pair confluence check (by normalization to normal forms)

Definitional term equality is equality of normalized term expressions (then deterministically re-embedded as `TermDiagram`).

## 3. Doctrine Layer

Key records:

- `TypeSig = [ParamSig]`, where `ParamSig = PS_Ty ModeName | PS_Tm TypeExpr`
- `GenDecl` supports type vars, term vars, attributes, and binder inputs
- `Cell2` rewrites diagrams
- `ModAction` stores per-modality generator images
- `ObligationDecl` stores named equations checked on `implements`

Validation checks:

- mode/modality well-formedness
- type/generator/rule well-formedness
- action coverage and mode correctness
- obligation diagrams are valid and boundary-compatible

## 4. Diagram Layer

A `Diagram` is a typed port graph with edge payloads:

- `PGen`
- `PBox`
- `PFeedback`
- `PSplice`
- `PTmMeta`
- `PInternalDrop` (kernel-internal, non-surface payload)

Matching and rewriting are structural and mode-aware.

### 4.1 Isomorphism

Structural diagram isomorphism (`diagramIsoEq`) uses:

- fixed boundary positions (`dIn` index-to-index, `dOut` index-to-index)
- syntactic port-type equality
- ordered incidence lists (`eIns`, `eOuts`) preserved positionally
- payload-structural equality:
  - `PGen`: generator name, attrs, binder args
  - `PBox`: inner diagram only (box name is annotation)
  - `PFeedback`: inner diagram
  - `PSplice`: binder metavariable
  - `PTmMeta`: metavariable identity by `(name, scope)`
  - `PInternalDrop`: exact constructor match

### 4.2 Canonical Form

Canonicalization reduces a diagram to a colored graph encoding:

- vertices for boundary positions, ports, edges, and ordered input/output slots
- edges for boundary attachments and slot incidence
- colors enforcing boundary index, slot index/direction, port type, and edge payload shape

Canonical labeling picks a deterministic representative and rebuilds the diagram with canonical `PortId`/`EdgeId` assignment. Canonization is recursive through payload-contained diagrams (`PBox`, `PFeedback`, `BAConcrete`).

Port labels are currently treated as metadata for structural isomorphism/canonization by default (ignored as equality keys), while still being stored on diagrams.

## 5. Modalities

`mod_eq` gives oriented modality-expression equations.

`action <ModName> where { gen g -> <diag> }` defines the functorial map on generator edges.

`map[<ModExpr>](<DiagExpr>)` elaborates by applying declared actions along the composed modality expression.

## 6. Schemas and Obligations

A schema is an ordinary doctrine used as an interface.

`implements IFace for Target using m` checks source/target compatibility and then checks each obligation from `IFace` after translating both sides through morphism `m`.

Obligation success is proof-carrying:

- a checker accepts an equality when it has a `JoinProof` and replay/verification succeeds
- automated search (`auto`) may try to synthesize a `JoinProof` within a tooling budget
- if automation fails to find a proof, result is `undecided` (not “false”)

## 6.1 Proof-Carrying Equality Checking

For morphism law checking, action semantics, obligation discharge, and coherence obligations:

- automation can search for join proofs
- kernel/checker code validates proofs by replaying certified rewrite steps and checking join endpoints
- “unknown within budget” is reported as undecided, not as a semantic counterexample

Budgets are tooling-level search parameters (`SearchBudget`), not doctrine/morphism/obligation data.
`sbTimeoutMs` is interpreted as a real wall-clock timeout for auto-proof search.

## 7. DSL Summary

Doctrine items:

- `mode`, `modality`, `mod_eq`
- `action`, `obligation`
- `attrsort`, `type`, `data`, `gen`, `rule`

Removed legacy items:

- `index_mode`, `index_fun`, `index_rule`
- `structure ... = ...`
- `adjunction F dashv U`

## 8. Morphisms and Pushouts

Morphisms map modes/modalities/types/generators and transport diagrams.
Pushout/coproduct construction remains available and merges doctrine content with compatibility checks.

Morphism equation checking uses proof search over join proofs with tooling budgets.
DSL morphism blocks may set optional:

- `max_depth`
- `max_states`
- `timeout_ms`

If search cannot produce a proof within budget, the result is reported as `undecided`
with a concrete limit reason.

## 9. Surface Elaboration

Surface elaboration is capability-driven:

- duplication requires a resolved unary copy capability (`[a] -> [a, a]`) from default `implements` instances for the target doctrine
- dropping requires a resolved unary discard capability (`[a] -> []`) from default `implements` instances for the target doctrine

No discipline lattice is consulted.

## 10. Temporary Restrictions

See `RESTRICTIONS.md`.
