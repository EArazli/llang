Polygraph examples

planar_monoid.llang
  Planar monoid in a single mode (no implicit swap/dup/drop). Includes unit/assoc rules.
planar_monoid.run.llang
  Normalizes a closed planar monoid diagram.
monoid.run.llang
  A short monoid normalization run that mirrors the legacy monoid example.

cart_monoid.llang
  Monoid over an explicit cartesian structural library (dup/drop/swap generators).
cart_monoid.run.llang
  Uses dup to build a square-like diagram and normalizes it.

no_dup_error.run.llang
  Demonstrates a boundary mismatch when composing without dup.

subdiagram_match.llang
  A small doctrine with a rule intended to match as a subdiagram inside larger graphs.

planar_monoid.ssa.run.llang
  Uses the SSA surface to build a monoid diagram with named wires (see planar_monoid.ssa.surface.llang).

cart_monoid.term.run.llang
  Uses a CartTerm surface plus a model to normalize and evaluate a duplicated term.

monoid_to_string.llang
  Declares a morphism from a monoid doctrine to a string monoid doctrine.

cat.llang + cat.run.llang
  A tiny typed chain of generators showing categorical composition in the diagram kernel.

ccc.llang + ccc.run.llang
  A minimal cartesian doctrine with an eval‑like generator; normalizes a simple diagram.
ccc_surface/ccc.llang + ccc_surface/stlc.*.llang
  Defines a surface for STLC-in-CCC and runs surface terms as diagrams.

bool.models.llang + stlc_bool.term.run.llang
  Boolean cartesian doctrine with if‑rules; demonstrates surface evaluation.

peano.llang + peano.models.llang + peano.run.llang
  Peano naturals with add rules and a native model; normalizes and evaluates a term.

ski.llang + ski.run.llang
  SKI combinators as string‑diagram rewriting with explicit app/dup/drop/swap.

morphism_term.llang
  Defines an endomorphism morphism and uses run apply to normalize after the pass.

pushout_basic.llang + pushout_basic.run.llang
  A small pushout that demonstrates automatic disjoint renaming for non‑interface gens.
pushout/*
  Poly pushout parity examples (category/bool/nat base, commutative monoid, nat/bool coproduct, and model restriction).

implements_uses.run.llang
  Demonstrates implements + run uses with an SSA surface over an interface doctrine.

runspec/multi.llang
  Two runs in a single file to mirror the legacy multi‑run example (run_spec).
