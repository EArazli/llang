# Cleanup Decisions

- Morphism checking uses declaration-local `check { policy; fuel; }` with defaults `UseStructuralAsBidirectional` and `fuel 200`; run blocks do not override morphism check settings.
- Include merging treats equations like sorts/ops: duplicate names are allowed only if alpha-equivalent; otherwise error.
- SOGAT v2 enabled: context_sort is context-indexed (Ty(Γ)) with implicit weakening during elaboration; v1 restriction removed.
- `derive contexts using ccc` is piecewise: only missing components are derived, dependencies are derived as needed, and missing prerequisites are hard errors.
- Surface declarations may omit `requires` (zero requirements allowed).
- Multi-run examples should canonicalize to Bool results (beta run uses computational policy).
