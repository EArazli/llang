# Restrictions (Temporary)

## 1. Term Diagram Fragment

Term arguments (`TATm`) normalize through a restricted diagram fragment:

- one output
- only `PGen` and `PTmMeta` payloads
- no boxes, feedback, or splice nodes
- no generator attrs/binder args inside term diagrams
- `PTmMeta` inputs must be the canonical prefix determined by `tmvScope`

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
