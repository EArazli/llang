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

## 7. Proof IO Surface Is Not Implemented Yet

The DSL and CLI do not yet expose proof input/output workflows for equational checks.
In particular, there is no `by ...` / `by auto` clause on obligations or morphism checks, and no
proof artifact pipeline such as `--emit-proofs` / `--use-proofs`.
`encodeJoinProof` exists as scaffolding, but `decodeJoinProof` is still a placeholder.
