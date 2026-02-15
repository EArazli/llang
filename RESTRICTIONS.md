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

## 3. Fuel-Bounded Reduction

Type/term definitional equality is fuel-bounded (`ttTmFuel`).
Normalization may fail with fuel exhaustion.

## 4. Surface Structural Capabilities

Surface duplication/drop are capability-based and resolved through default `implements` instances for the target doctrine.
Any mapped source generator with the required polymorphic unary shape can provide `dup`/`drop`; there is no local-name fallback path.

## 5. Term Rule Recontextualization

During term-rule extraction/alignment (`termRulesForMode`), rule diagrams are recontextualized to the ambient
`tmCtx` and revalidated with `validateDiagram` (not `validateTermGraph`).
So the strict term boundary-prefix invariant is guaranteed for concrete normalized term diagrams, but not
re-enforced at that intermediate aligned-rule representation.

## 6. Bound-Index Reporting Is Output-Reachable

`boundTmIndicesTerm` reports bound indices reachable from term outputs.
Disconnected dead subgraphs do not contribute to reported bound indices.
