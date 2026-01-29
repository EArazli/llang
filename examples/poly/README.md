Polygraph examples

planar_monoid.poly.llang
  Planar monoid in a single mode (no implicit swap/dup/drop). Includes unit/assoc rules.
planar_monoid.run.llang
  Normalizes a closed planar monoid diagram.
monoid.run.llang
  A short monoid normalization run that mirrors the legacy monoid example.

cart_monoid.poly.llang
  Monoid over an explicit cartesian structural library (dup/drop/swap generators).
cart_monoid.run.llang
  Uses dup to build a square-like diagram and normalizes it.

no_dup_error.run.llang
  Demonstrates a boundary mismatch when composing without dup.

subdiagram_match.poly.llang
  A small doctrine with a rule intended to match as a subdiagram inside larger graphs.

planar_monoid.ssa.run.llang
  Uses the SSA polysurface to build a monoid diagram with named wires (see planar_monoid.ssa.surface.llang).

cart_monoid.term.run.llang
  Uses a CartTerm polysurface plus a polymodel to normalize and evaluate a duplicated term.

monoid_to_string.llang
  Declares a polymorphism from a monoid doctrine to a string monoid doctrine.

cat.poly.llang + cat.run.llang
  A tiny typed chain of generators showing categorical composition in the poly kernel.

ccc.poly.llang + ccc.run.llang
  A minimal cartesian doctrine with an eval‑like generator; normalizes a simple diagram.
ccc_surface/ccc.poly.llang + ccc_surface/stlc.*.llang
  Defines a polysurface for STLC-in-CCC and runs surface terms as poly diagrams.

bool.models.llang + stlc_bool.term.run.llang
  Boolean cartesian doctrine with if‑rules; demonstrates polysurface evaluation.

peano.poly.llang + peano.models.llang + peano.run.llang
  Peano naturals with add rules and a native model; normalizes and evaluates a term.

ski.poly.llang + ski.run.llang
  SKI combinators as string‑diagram rewriting with explicit app/dup/drop/swap.

morphism_term.llang
  Defines a polymorphism and uses polyrun apply to normalize after mapping.

pushout_basic.poly.llang + pushout_basic.run.llang
  A small pushout that demonstrates automatic disjoint renaming for non‑interface gens.
pushout/*
  Poly pushout parity examples (category/bool/nat base, commutative monoid, nat/bool coproduct, and model restriction).

implements_uses.run.llang
  Demonstrates polyimplements + polyrun uses with an SSA surface over an interface doctrine.

runspec/multi.llang
  Two polyruns in a single file to mirror the legacy multi‑run example (polyrun_spec).
