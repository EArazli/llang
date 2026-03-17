# Restrictions

## 1. Unified Defeq Term-Diagram Fragment

Public kernel definitional equality now uses one normalization path, but it still has a deliberate
two-level boundary:

- term-headed subdiagrams are evaluated by the term defeq core,
- fragment-owned structural computational rules may rewrite surrounding diagram structure before/around that core,
- residual structural diagrams may survive normalization when no structural rule removes them.

The current fragment restrictions are:

- normalized term diagrams must have exactly one output,
- `PTmMeta` inputs must be boundary ports; explicit meta arguments may choose any boundary subset/order,
- `PInternalDrop` is kernel-internal only and must be `1` input / `0` outputs,
- structural nodes (`box`, `feedback`, `provider`, `module_ref`) are not term heads for builtin semantic evaluation or trusted term-rule compilation; they participate only through structural computational rewriting and residual structural diagrams.

## 2. Definitional TRS Admissibility

Dependent definitional term normalization is fuel-free, but only for admissible term TRSs.
Doctrine validation rejects term-rule sets when termination is not proven (SCT) or when
critical pairs are not joinable after normalization.

## 3. Surface Structural Capabilities

Surface duplication/drop are capability-based and resolved through default `implements` instances for the target doctrine.
Any mapped source generator with the required polymorphic unary shape can provide `dup`/`drop`; there is no local-name fallback path.

## 4. Term Rule Compilation Shape

Term rewrite compilation requires function-headed left-hand sides and a first-order term fragment
(no residual `TMVar` after abstraction to `TMBound`). Rules outside this fragment are rejected for
definitional normalization.

## 5. Bound-Index Reporting Is Output-Reachable

`boundTmIndicesTerm` reports bound indices reachable from term outputs.
Disconnected dead subgraphs do not contribute to reported bound indices.

## 6. Doctrine Functors and `apply`

- Functor parameter schemas are full doctrines (including rules, actions, obligations, and `mod_transform`).
- `apply` is checked before pushout: it must pass a full morphism check (`CheckAll`) for the merged interface morphism and discharge all interface obligations.
- Any failed check or undecided obligation proof search result rejects `apply`.
- `apply` checking is budget-sensitive: tighter search budgets can produce undecided failures even when a proof exists with a larger budget.
- `using { ... }` keys must exactly match the functor parameter set.

## 7. Action-System Strictness

- `map[...]` uses an effective action image per generator:
  explicit action images when declared, otherwise a canonical same-name generator image in the modality target mode.
- This means `map[mu](...)` does not require explicit `action` declarations for every modality in `mu`, but it still fails if any needed generator has neither an explicit image nor a canonical same-name target generator.
- Action declarations may be partial; explicit images are validated and canonical fallback fills missing generator images.
- Action images (explicit or canonical) must elaborate/typecheck in the modality target mode.
- For generators with binder inputs, action images must provide binder arguments with matching boundaries (either concrete diagrams or the generator's allowed binder holes).
- Action images may use binder holes only for the generator's own binder inputs (`?b0`, `?b1`, ...) and may use `splice(?bi)`.
- Action images may not introduce any other binder metavariables.
- Action-semantics proof checking currently targets the explicitly declared image fragment (rules/generators that only mention explicitly mapped generators), not fallback-only generator behavior.

## 8. Pushout/`apply` Merge Strictness for Actions and Obligations

- When two branches define actions for the same modality name, merge combines them if:
  - rewrite policies agree, and
  - overlapping generator-image entries are diagram-isomorphic.
  Otherwise pushout/`apply` fails.
- When two branches define obligations with the same `obName`, merge requires exact obligation equality; otherwise pushout/`apply` fails.

## 9. Transform Restrictions (Phase 2)

- `mod_transform` does not rewrite modalities and does not change `mod_eq`.
- The witness must be a generator with exactly one type variable, no term vars, one input port, and one output type.
- Witness shape is constrained to `mu(A) -> nu(A)` (checked after modality/type normalization).
- No automatic transform coercion insertion is performed; witnesses must be used explicitly.

## 10. Builtin Eliminator Scope

Builtin eliminators are intentionally conservative and currently support:

- one scrutinee selected from the eliminator head's ordinary input ports,
- branches keyed by direct constructors of the scrutinee family,
- recursive-result sources only for direct recursive constructor fields of that same family,
- unary branch codomains.

Builtin eliminator **inference** is stricter still:

- ambiguous same-sort branch-input or local-`tm`-context source assignments are not inferred semantically and must use explicit builtin declarations,
- constructors with binder inputs are not inferred as builtin eliminator branches,
- explicit builtin declarations are the authoritative path whenever conservative inference is insufficient.

## 11. Generated Structural Obligations (Current Scope)

- Auto-generated comprehension/Beck-Chevalley slot obligations currently apply to:
  - binder-only generator domains, and
  - constructor term-argument slots (dom/cod side according to slot position).
- Mixed-domain binder generators (having both plain ports and binder slots) are currently excluded from these auto-generated slot-law obligations.

## 12. Classification Graph Limits

- Non-self classification cycles are rejected. Allowing longer cycles would require an explicit universe-level stratification design and implementation.

## 13. Mode Equations

Mode theory `mod_eq` declarations are treated as an oriented rewrite system used to normalize modality expressions (so that definitional equality is equality of normal forms).

To make this mathematically well-defined (strategy-independent), the kernel requires the compiled rewrite system to be *convergent*:

- **Termination:** must be proven by the same SCT-based termination check used for computational TRSs.
- **Confluence:** all critical pairs must be joinable (checked by normalizing both sides).

The kernel still does not perform completion: users must provide a convergent presentation themselves.

## 14. Module / Build Scope

- `link` is currently **structural component-graph composition**, not a full
  signature/substitution module calculus.
  Linked modules must share a language and doctrine; imports are satisfied
  against present linked components and equal-name components must be equal.
- Whole-module `quote` is a **closure-and-lowering** step.
  It first closes the module graph, then quotes values into the target
  doctrine, and the resulting artifact is value-only.
  It does **not** preserve typed/import/provider metadata as a translated typed
  module graph.
- `module_surface` elaborator extensibility is bounded to the existing
  declaration grammar.
  Source-defined `module_elaborator` declarations may expand
  `custom <tag> --- ... ---` items into ordinary interface/module items, but
  they do not define new parser syntax or new kernel declaration kinds.
- Source-defined `data_repr` declarations are aliases/configuration over
  existing host-side representation semantics.
  They may reuse `doctrine_data` or configure `opaque_data`, but genuinely new
  representation behavior still requires host-side implementation.
- The shipped standard module-data representations are intentionally small:
  `doctrine_data` and `opaque_data`.
  `doctrine_data` currently requires doctrine-provided **nullary** type
  constructors for packaged module data.

## 15. Host Backend Scope

- Host backends are a Haskell-side registry consumed by `emit via ...`.
  They are injectable/configurable on the host side, but they are not currently
  userland-defined or dynamically loaded from source files.
