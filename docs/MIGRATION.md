# MIGRATION

This document records user-facing syntax and behavior changes.

## Phase 1 — Mode-signatured type constructors + modeful type expressions

User-facing changes:

- Type constructors now have **mode signatures** `(m1,...,mk) -> m`; type expressions can nest
  constructors from different modes.
- Type variables are **mode-indexed**. Binder lists support `a@Mode`; if the mode is omitted,
  it defaults to the declaration mode. Binder names must be unique by name.
- Type expressions now accept **mode-qualified constructors**: `Mode.Type(args)` or `Mode.Type`.
  Unqualified constructor names must be unique across all modes.
- Preferred type declaration syntax uses parentheses:
  `type T (a@M, b@M) @M;`
- CLI/pretty-print output shows mode-qualified constructors and tyvar modes, e.g.
  `M.A` and `a@M`.

## Phase 2 — Morphism mode maps

User-facing changes:

- Morphisms can declare mode translations inside the block:
  `mode SrcMode -> TgtMode;`. The mapping is total on source modes.
- If a source mode is not explicitly mapped, it defaults to the same‑named target
  mode (and it is an error if that mode does not exist in the target doctrine).
- Type mappings must target the mapped mode, and binder modes are checked against
  the source type’s parameter modes after applying the mode map.
- Generator mappings elaborate in the target mode determined by the mode map, and
  their type parameters are mapped through it as well.
- Applying a morphism now translates the diagram mode and type‑variable modes via
  the mode map.
- `pushout` still requires **mode‑preserving** morphisms (identity mode map).
- New example: `examples/mode_map_demo.run.llang`.

## Phase 3 — Surface structural discipline

User-facing changes:

- Surfaces can declare a `structural { ... }` block:
  `discipline: linear | affine | relevant | cartesian`,
  with optional `dup:` and `drop:` generator names.
- If the block is omitted, it defaults to **cartesian** with `dup`/`drop` generators
  named `dup` and `drop`.
- If the block is present, `discipline` defaults to `cartesian` and `dup`/`drop` are
  unset unless specified.
- Variable‑use discipline is enforced:
  linear = exactly once; affine = at most once (drop inserted for 0 uses);
  relevant = at least once (dup inserted for >1); cartesian = any uses.
- Configured `dup`/`drop` generators must exist in the surface mode and have shapes
  `dup(a) : a → (a, a)` and `drop(a) : a → []`.
