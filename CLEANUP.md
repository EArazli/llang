# Cleanup Decisions

- Morphism checking uses declaration-local `check { policy; fuel; }` with defaults `UseStructuralAsBidirectional` and `fuel 200`; run blocks do not override morphism check settings.
- Include merging treats equations like sorts/ops: duplicate names are allowed only if alpha-equivalent; otherwise error.
- SOGAT v1 restriction is enforced: bound term vars must not appear free in any Ty-sorted index term; violations error.
- `derive contexts using ccc` is piecewise: only missing components are derived, dependencies are derived as needed, and missing prerequisites are hard errors.
