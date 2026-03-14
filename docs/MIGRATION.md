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
- Canonical example coverage lives in `examples/build/**`; `examples/run/**` now
  contains restored build-native entrypoints at the historic paths.

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

## Module Values and `@value` References

User-facing changes:

- Top-level `term` blocks were removed.
- Named reusable diagrams now live inside `module` declarations as `let`-bound values.
- Module values are referenced by bare name in later declarations, e.g. `hello; cat`.
- Legacy `@value` splice syntax is rejected.

## Languages + Module Surfaces

User-facing changes:

- `language` declarations no longer carry direct `mode` / `expr_surface` items.
- `language` declarations no longer carry declaration-default `uses` items; interface defaults
  belong on the selected `module_surface`.
- Declaration-layer defaults now live in a first-class `module_surface`:
  `module_surface DocUnit where { doctrine Doc; mode Doc; }`
- Languages bind to that declaration surface explicitly:
  `language DocLang where { doctrine Doc; module_surface DocUnit; }`
- Module/interface elaboration uses the resolved module-surface defaults for mode and
  expression-surface selection.
- Declaration surfaces are now configurable from source through
  `module_elaborator` declarations, but the extensibility point is still bounded:
  `custom <tag> --- ... ---` bodies expand into ordinary interface/module items.

## Recursive Module Groups

User-facing changes:

- `rec { ... }` inside `module` blocks has been removed.
- Recursive program structure now needs an explicit representation in the selected
  language surface or doctrine, rather than a placeholder module-level group syntax.

## Module `data` Packages

User-facing changes:

- Ordinary program/module `data` declarations now elaborate as declaration packages, not
  doctrine extensions.
- Current syntax:
  `data T @M where { ctor C : [] -> [T] @M; ... }`
- Representation choice is now explicit and source-definable through `data_repr`.
  Shipped base representations are `doctrine_data` and `opaque_data`.
- `doctrine_data` is doctrine-backed packaging:
  the language doctrine must already provide the type constructor and constructor generators.
- `opaque_data` packages opaque module-level types with provider-backed constructors and may be
  configured from source via `provider_interface` and `descriptor_prefix`.
- Module `data` introduces a local type binding plus constructor value bindings, so later
  declarations use the packaged constructors as ordinary module values, e.g. `Red ; Wrap`.
- Parametric module `data` is currently rejected with a dedicated diagnostic; the current
  module/interface type-binding layer is still monomorphic.

## Coercion Morphisms + Implicit Coercion Paths

User-facing changes:

- Morphism blocks accept `coercion;` to mark a morphism as eligible for implicit coercion.
- Doctrines defined with `extends` generate `<Name>.fromBase` coercion morphisms, and
  pushout/coproduct-generated morphisms are also marked coercions.
- Module values must elaborate in the declared language doctrine; if not, the compiler attempts a
  **unique shortest** coercion path. Ambiguous or missing paths are now errors.

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

## Build-Oriented Execution

User-facing changes:

- Legacy `run` declarations have been removed.
- Entry points are explicit `build <Name> from <Module> using <Pipeline>;` declarations.
- Historic paths under `examples/run/**` are now build-native examples, not a separate execution model.
