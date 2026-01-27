Polygraph examples (current kernel)

poly/planar_monoid.poly.llang + poly/planar_monoid.run.llang demonstrate a planar monoid with explicit generators and rules; run the .run file to see normalized diagram output.

poly/cart_monoid.poly.llang + poly/cart_monoid.run.llang add explicit cartesian structure (dup/drop/swap) and normalize a diagram that uses dup.

poly/no_dup_error.run.llang is a negative example that fails due to a boundary mismatch (no implicit duplication).

poly/subdiagram_match.poly.llang is a small doctrine intended to exercise true subdiagram matching.

poly/planar_monoid.ssa.run.llang demonstrates the SSA polysurface; run it to see a wire‑named diagram elaborate and normalize.

poly/cart_monoid.term.run.llang uses the CartTermSurface and a polymodel to normalize and evaluate a duplicated term.

poly/monoid_to_string.llang defines a polymorphism between two polydoctrines (monoid → string monoid).

Legacy examples (term kernel + Surface2)

cat.llang + cat.run.llang demonstrate a small category doctrine with a direct core run using CombDefault syntax; run `examples/cat.run.llang` and expect normalized/value output for a fully-qualified core term.

ccc.llang + ccc.syntax.llang + ccc.run.llang define the CCC doctrine and a core syntax for it; run `examples/ccc.run.llang` to see normalized/value/cat output for a CCC expression.

ccc_surface/ (ccc.doctrine.llang, ccc.interface.llang, stlc.surface.llang, stlc.syntax.llang, stlc.runspec.llang, and stlc.*.run.llang) demonstrates the Surface2 STLC layer over CCC; run `examples/ccc_surface/stlc.run.llang` or the lam/pair variants to see surface input elaborate into core terms and print normalized/value/cat.

monoid.llang + monoid.syntax.llang + monoid.models.llang + monoid.run.llang show a monoid doctrine with computational rules and a string model; run `examples/monoid.run.llang` (or `examples/monoid.alt.run.llang`) and expect normalized/value/cat for a parsed monoid term.

peano.llang + peano.syntax.llang + peano.models.llang + peano.run.llang show Peano naturals with a model-backed evaluator; run `examples/peano.run.llang` to see normalized/value output for a Peano term (there is also `examples/peano.js.run.llang` using the JS model).

ski.llang + ski.syntax.llang + ski.run.llang demonstrate a tiny SKI combinator calculus; run `examples/ski.run.llang` and expect normalized output for a combinator term.

morphism_term.llang demonstrates morphism interpretation on terms; load it with the CLI to check that the morphism and its check pass (no run block output is expected).

runspec/multi.llang demonstrates multiple runs in a single file; run it to see the two runs execute in sequence with their respective outputs.

pushout/category_bool_nat_base.llang defines Category/BoolExt/NatExt and their pushout Both; other pushout examples import this as shared boilerplate.

pushout/pushout_basic.llang just imports the base pushout definitions; pushout/pushout_basic.run.llang runs a core term in doctrine Both to exercise pushout normalization and open resolution.

pushout/pushout_extend.llang extends Both and adds cross-fragment rules using qualified names; load it to confirm qualified sorts/ops parse and elaborate.

pushout/comm_monoid.llang demonstrates assembling a commutative monoid via pushout over a semigroup interface.

pushout/nat_bool.llang + pushout/nat_bool.models.llang + pushout/nat_bool.run.llang demonstrate model restriction: a Nat term is run using a NatBool model via the injection morphism; run `examples/pushout/nat_bool.run.llang` and expect normalized/value output for a Nat term.

pushout/nat_bool_plus.llang + pushout/nat_bool_plus.models.llang + pushout/nat_bool_plus.run.llang extend NatBool with a cross-fragment op (Nat -> Bool) and model it; run `examples/pushout/nat_bool_plus.run.llang` and expect normalized/value output.

pushout/ambiguous_model_restriction.llang demonstrates the expected error when multiple morphisms exist from a run doctrine to a model doctrine; load it to see the ambiguity failure.
