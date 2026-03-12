# MIGRATION

This document records user-facing syntax and behavior changes.

## Mode-Signatured Type Constructors + Modeful Type Expressions

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

## Morphism Mode Maps

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

## Surface Structural Discipline

User-facing changes:

- Surface variable discipline is taken from the doctrine mode declaration:
  `structure M = linear | affine | relevant | cartesian;`.
- Structural generator names are fixed to `dup` and `drop` (no surface-level renaming).
- Required structural generators must:
  - use the ordinary generator-parameter system (there is no separate attr channel),
  - have no stored term parameters,
  - have the expected structural shape,
  - and have no binder slots in their domain.
- Variable‑use discipline is enforced during surface elaboration:
  linear = exactly once; affine = at most once (drop inserted for 0 uses);
  relevant = at least once (dup inserted for >1); cartesian = any uses.
- Surface grammar uses direct template actions and explicit binder clauses:
  - `bind in(varCap, typeCap, bodyHole)`
  - `bind let(varCap, valueHole, bodyHole)`
- Surfaces may declare `base D;`. When present and `D != doctrine`, elaboration normalizes
  away surface-only generators and returns a diagram in the base doctrine.

## Terms and `@term` References

User-facing changes:

- New top-level `term <Name>` blocks compile a diagram and store its **normalized** form.
  `term` supports doctrine/mode/surface/uses/apply/policy/fuel configuration and compiles
  directly (without run pipelines).
- Diagram expressions accept `@<TermName>` to splice a named term into a diagram.

## Coercion Morphisms + Implicit Coercion Paths

User-facing changes:

- Morphism blocks accept `coercion;` to mark a morphism as eligible for implicit coercion.
- Doctrines defined with `extends` generate `<Name>.fromBase` coercion morphisms, and
  pushout/coproduct-generated morphisms are also marked coercions.
- Runs and terms must end in the declared doctrine; if not, the compiler attempts a **unique
  shortest** coercion path. Ambiguous or missing paths are now errors.

## Doctrine Templates + Instantiation

User-facing changes:

- `doctrine_template T(P1, ..., Pn) where { doctrine T ... }` defines a parameterized doctrine.
- `doctrine D = instantiate T(A1, ..., An);` expands the template with identifier substitution.

## `effects` Macro

User-facing changes:

- `doctrine Combined = effects Base { E1, E2, ... };` expands to an iterated pushout over
  `Base` using each effect’s `fromBase` morphism, producing intermediate doctrines
  `<Combined>__stepN`.

## `data` Macro Inside Doctrine Blocks

User-facing changes:

- `data T (a@M) @M where { C : [...]; ... }` expands to a `type` declaration plus
  constructor `gen`s with codomain `[T(a,...)]`.

## Pipeline-Based Runs

User-facing changes:

- Runs are now `run <Name> using <Pipeline> where { source ... }` with explicit `pipeline` declarations.
- `run_spec` has been removed.
- Run-level `model` and `show ...` clauses have been removed.
