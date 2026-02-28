# Restrictions

## 1. Term Diagram Fragment

Term arguments (`TATm`) normalize through restricted diagram fragments that depend on the mode's defeq engine:

- `TRS` defeq term-argument fragment:
  - one output
  - no boxes, feedback, or splice nodes
  - no generator attrs or binder args
  - `PTmMeta` inputs must be boundary ports; explicit meta arguments may choose any boundary subset/order
  - `PInternalDrop` is kernel-internal only and must be `1` input / `0` outputs

- `NbE` defeq term-argument fragment:
  - one output
  - no boxes, feedback, or splice nodes
  - no generator attrs
  - binder args are allowed only for `lam`, and only as the enforced concrete binder-body form used by NbE (`BAConcrete`, bound var first, then outer-prefix inputs)
  - `PTmMeta` inputs must be boundary ports; explicit meta arguments may choose any boundary subset/order
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

## 7. Doctrine Functors

- **Persistent restriction (kept intentionally):** functor parameter schemas are signature-only.
  Allowed: modes, modalities, `mod_eq`, attrsort/type/gen/data declarations.
  Disallowed (compiler error): cells/rules, actions, obligations, and `mod_transform`.

## 8. Transform Restrictions (Phase 2)

- `mod_transform` does not rewrite modalities and does not change `mod_eq`.
- The witness must be a generator with exactly one type variable, no term vars, no attrs, one input port, and one output type.
- Witness shape is constrained to `mu(A) -> nu(A)` (checked after modality/type normalization).
- No automatic transform coercion insertion is performed; witnesses must be used explicitly.

## 9. NbE Primitive Selection Is Currently Fixed

For NbE modes, the required primitive names are currently fixed in the kernel (`lam`, `app`, and `Arr`).
This is temporary and should be revisited so NbE primitive/operator names can be configured per mode.
Follow-up work item: replace hardcoded names with per-mode NbE configuration.

## 10. NbE Fragment Coverage Is Intentionally Narrow

Current NbE normalization targets a strict lambda-calculus fragment for definitional equality.
Unsupported constructs (for now) include structural diagram features such as splice/feedback/box/tensor/comp/symmetry in definitional normalization paths.
This is a scope restriction, not a fundamental limitation, and should be revisited after core NbE stability and soundness are locked in.
Follow-up work item: expand supported definitional fragment after NbE core stability/soundness are established.

## 11. Classification Graph Limits

- Non-self classification cycles are rejected. Allowing longer cycles would require an explicit universe-level stratification design and implementation.

## 12. Constructor/Surface Caveats

- Constructor term-parameter sorts are required to be closed with respect to the generator's type parameters.
- Surface type annotations do not support constructor parameters of kind `TPS_Tm`; term-indexed arguments must be expressed through core/kernel paths.

## 13. Mode Equations

Mode theory `mod_eq` declarations are treated as an oriented rewrite system used to normalize modality expressions (so that definitional equality is equality of normal forms).

To make this mathematically well-defined (strategy-independent), the kernel requires the compiled rewrite system to be *convergent*:

- **Termination:** must be proven by the same SCT-based termination check used for computational TRSs.
- **Confluence:** all critical pairs must be joinable (checked by normalizing both sides).

The kernel still does not perform completion: users must provide a convergent presentation themselves.
