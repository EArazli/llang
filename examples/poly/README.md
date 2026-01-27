Polygraph examples

planar_monoid.poly.llang
  Planar monoid in a single mode (no implicit swap/dup/drop). Includes unit/assoc rules.
planar_monoid.run.llang
  Normalizes a closed planar monoid diagram.

cart_monoid.poly.llang
  Monoid over an explicit cartesian structural library (dup/drop/swap generators).
cart_monoid.run.llang
  Uses dup to build a square-like diagram and normalizes it.

no_dup_error.run.llang
  Demonstrates a boundary mismatch when composing without dup.

subdiagram_match.poly.llang
  A small doctrine with a rule intended to match as a subdiagram inside larger graphs.

planar_monoid.ssa.run.llang
  Uses the SSA polysurface to build a monoid diagram with named wires.

cart_monoid.term.run.llang
  Uses the CartTermSurface plus a polymodel to normalize and evaluate a duplicated term.

monoid_to_string.llang
  Declares a polymorphism from a monoid doctrine to a string monoid doctrine.
