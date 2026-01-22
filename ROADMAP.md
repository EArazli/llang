# Roadmap

This document describes the settled direction and remaining major pieces: effects, pushouts, recursion/datatypes, modules and interoperability, and improved semantics.

---

## Effects as user-defined doctrine layers (no baked-in effect system)

### Target state

Provide primitives sufficient for *declaring* effect systems in user doctrines and proving interoperability constraints, without committing to a single baked-in notion.

### What the meta-language must support (foundation)

1. **Interfaces as doctrines** (already done): effects are expressed as additional required interfaces (e.g. “strong monad”, “Freyd category”, “algebraic effects handler interface”).
2. **Obligation checking** (already done for morphisms): effect laws are equations; implementations are morphisms; validation is equation preservation.

### Example family of libraries (later, not in kernel)

* monadic effects (Kleisli triples),
* Freyd categories / Arrows-style effects,
* algebraic effects via handlers,
* linear effects via graded/linear monads, etc.


## Recursion and user-definable datatypes

### What’s missing today

* There is no first-class notion of inductive definitions or recursion in the kernel.
* You can encode specific recursors manually as operations + equations, but there’s no user-facing mechanism for:

  * introducing a datatype,
  * generating constructors,
  * generating elimination/recursion principles and β/η laws.

### Plan (kept compatible with the kernel)

1. Add a doctrine-library layer that provides:

   * a schema for *initial algebras* / W-types-like signatures,
   * generated operations:

     * constructors,
     * eliminators,
     * β/η equations.
2. Provide library doctines for `Nat`, `List`, etc., with minimal sugar.

This fits the existing foundation because “datatype definitions” compile to ordinary presentations + equations.

---

## Modules and true interoperability of doctrines/terms

### Problem today

Multiple runs in a file are separate pipelines. Terms do not interact across runs; there is no notion of “import a term produced under doctrine X and use it under doctrine Y”.

### Needed concept

A **module system** that:

* gives names to definitions (terms),
* assigns them a doctrine + surface + model context,
* and allows importing them through morphisms.

### Plan

1. Introduce module-level definitions:

   * `def foo : <judgment/type> := <surface/core term>`
   * each definition elaborates under some run context (doctrine/surface/syntax).
2. Allow a definition to be *re-used* under another doctrine by requiring a morphism:

   * if `foo` is a kernel term in doctrine `P`, and you want it in doctrine `Q`, require a morphism `P -> Q` and translate it with `applyMorphismTerm`.
3. Make run specs reusable at **term level**:

   * `run_spec` becomes a named environment that can be attached to defs, not just runs.
4. Add explicit “interop declarations”:

   * `import foo using morphism M` or `open module X as Y` with checked requirements.

This leverages the existing morphism machinery; what’s missing is the definition namespace and the ability to store elaborated terms in the environment.

---

## Interoperability between models

### Desired behavior

Interpret a term in one model (e.g. AD) and use it in another (e.g. Eval/Hask), with correctness constraints.

### Plan

1. Treat model interoperability as **morphisms at the model level**:

   * a natural transformation-like map between interpretations,
   * or a “model transformer” that maps `interpOp` implementations.
2. Make composition explicit:

   * `Model := AD ∘ Eval` becomes a declared object with obligations (equations/laws).
3. Use the same obligation machinery:

   * either by checking commutation on a test suite of generated terms,
   * or by symbolic equality checks where possible.

This is strictly beyond the current model implementation, but the same discipline (“declare structure + prove obligations”) applies.

---

## Next steps to improve usability quickly (without destabilizing foundations)

1. Implement pushout-sugar on top of existing `Rename/Share/And`.
2. Add definition bindings (`def`) and module imports, using morphisms for translation.
3. Add datatype schema as library-doctrines (Nat/List + folds), generate β equations.
