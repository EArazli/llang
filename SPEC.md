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
`dTmCtx` is the bound-term telescope for the diagram.

### 2.2 Definitional Equality

Type normalization and term-argument normalization are performed by `normalizeTypeDeep`.
For `TATm`, normalization uses the diagram rewrite engine in the term mode:

- rewrite rules come from `TypeTheory.ttTmRules`
- reduction is fuel bounded by `TypeTheory.ttTmFuel`
- policy is controlled by `TypeTheory.ttTmPolicy` (default computational orientation)

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

Matching and rewriting are structural and mode-aware.

## 5. Modalities

`mod_eq` gives oriented modality-expression equations.

`action <ModName> where { gen g -> <diag> }` defines the functorial map on generator edges.

`map[<ModExpr>](<DiagExpr>)` elaborates by applying declared actions along the composed modality expression.

## 6. Schemas and Obligations

A schema is an ordinary doctrine used as an interface.

`implements IFace for Target using m` checks source/target compatibility and then checks each obligation from `IFace` after translating both sides through morphism `m`.

Obligation success criterion is joinability under its policy/fuel.

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

## 9. Surface Elaboration

Surface elaboration is capability-driven:

- duplication requires a resolved unary copy capability (`[a] -> [a, a]`) from default `implements` instances for the target doctrine
- dropping requires a resolved unary discard capability (`[a] -> []`) from default `implements` instances for the target doctrine

No discipline lattice is consulted.

## 10. Temporary Restrictions

See `RESTRICTIONS.md`.
