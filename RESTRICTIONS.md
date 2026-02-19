# Restrictions (Temporary)

## 1. Term Diagram Fragment

Term arguments (`TATm`) normalize through a restricted diagram fragment:

- one output
- only `PGen`, `PTmMeta`, and internal `PInternalDrop` payloads
- no boxes, feedback, or splice nodes
- no generator attrs/binder args inside term diagrams
- `PTmMeta` inputs must be the canonical prefix determined by `tmvScope`
- `PInternalDrop` is kernel-internal only and must be `1` input / `0` outputs

## 2. Context-sensitive Normalization

Term normalization requires enough same-mode bound context for scoped reductions.
If a scoped term needs concrete context (for example it mentions non-meta structure), normalization fails with an explicit error.
Pure metavariable terms may be preserved as-is when context is insufficient.

## 3. Definitional TRS Admissibility

Dependent definitional term normalization is fuel-free, but only for admissible term TRSs.
Doctrine validation rejects term-rule sets when termination is not proven (SCT) or when
critical pairs are not joinable after normalization.

## 4. Surface Structural Capabilities

Surface duplication/drop are capability-based and resolved through default `implements` instances for the target doctrine.
Any mapped source generator with the required polymorphic unary shape can provide `dup`/`drop`; there is no local-name fallback path.

## 5. Term Rule Compilation Shape

Term rewrite compilation requires function-headed left-hand sides and a first-order term fragment
(no residual `TMVar` after abstraction to `TMBound`). Rules outside this fragment are rejected for
definitional normalization.

## 6. Bound-Index Reporting Is Output-Reachable

`boundTmIndicesTerm` reports bound indices reachable from term outputs.
Disconnected dead subgraphs do not contribute to reported bound indices.

## 7. Functor Restrictions (Phase 1)

- `doctrine_functor` currently supports exactly one parameter (`L : Schema`).
- The functor parameter identifier is currently parsed/stored only; it is not used for name qualification.
- Functor bodies must preserve the schema's mode-theory 1-category (same modes, modality declarations, and `mod_eq` equations). Adding or changing these in a functor body is currently rejected.
- This should be genuinely fixed only when functors need to define or transform mode-theory structure as part of normal usage (not just type/gen/cell/action/obligation extensions), because that requires a broader redesign of apply/pushout mode-mapping semantics.
- Schema doctrines used as functor parameters should be signature-level only: modes/modalities/mod_eq, attrsort/type/gen/data declarations.
- Cells/actions/obligations in schemas are not fully enforced by morphism mapping and should be avoided for functor schemas.
- `apply` preserves target names; only colliding functor-body declarations are renamed with `FunctorName_...` for attr sorts, types, generators, cells, obligations, and `mod_transform` names.
- Schema-declared cells/obligations/`mod_transform`s are treated as reserved names during `apply`: body-side declarations with the same schema name are not renamed away, and merge then requires semantic equality.
- This reserved-name behavior should be genuinely fixed only if functor bodies must intentionally redefine schema-named cells/obligations/`mod_transform`s with different semantics.

## 8. Transform Restrictions (Phase 2)

- `mod_transform` does not rewrite modalities and does not change `mod_eq`.
- The witness must be a generator with exactly one type variable, no term vars, no attrs, one input port, and one output type.
- Witness shape is constrained to `mu(A) -> nu(A)` (checked after modality/type normalization).
- No automatic transform coercion insertion is performed; witnesses must be used explicitly.
