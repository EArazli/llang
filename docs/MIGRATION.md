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
