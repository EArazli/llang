cat.llang + cat.run.llang demonstrate a small category doctrine with a direct core run using CombDefault syntax; run `examples/cat.run.llang` and expect normalized/value output for a fully-qualified core term.

ccc.llang + ccc.syntax.llang + ccc.run.llang define the CCC doctrine and a core syntax for it; run `examples/ccc.run.llang` to see normalized/value/cat output for a CCC expression.

ccc_surface/ (ccc.doctrine.llang, ccc.interface.llang, stlc.surface.llang, stlc.syntax.llang, stlc.runspec.llang, and stlc.*.run.llang) demonstrates the Surface2 STLC layer over CCC; run `examples/ccc_surface/stlc.run.llang` or the lam/pair variants to see surface input elaborate into core terms and print normalized/value/cat.

monoid.llang + monoid.syntax.llang + monoid.models.llang + monoid.run.llang show a monoid doctrine with computational rules and a string model; run `examples/monoid.run.llang` (or `examples/monoid.alt.run.llang`) and expect normalized/value/cat for a parsed monoid term.

peano.llang + peano.syntax.llang + peano.models.llang + peano.run.llang show Peano naturals with a model-backed evaluator; run `examples/peano.run.llang` to see normalized/value output for a Peano term (there is also `examples/peano.js.run.llang` using the JS model).

ski.llang + ski.syntax.llang + ski.run.llang demonstrate a tiny SKI combinator calculus; run `examples/ski.run.llang` and expect normalized output for a combinator term.

morphism_term.llang demonstrates morphism interpretation on terms; load it with the CLI to check that the morphism and its check pass (no run block output is expected).

runspec/multi.llang demonstrates multiple runs in a single file; run it to see the two runs execute in sequence with their respective outputs.

pushout/pushout_basic.llang demonstrates pushout-based doctrine assembly over a shared interface; load it to confirm the pushout and generated morphisms elaborate without errors.

pushout/native_pushout.llang demonstrates a coproduct-style pushout over an empty interface for Nat and Bool; load it to confirm the pushout and injections exist.

pushout/pushout_extend.llang extends a pushout and adds cross-fragment rules using qualified names; load it to confirm qualified sorts/ops parse and elaborate.

pushout/comm_monoid.llang demonstrates assembling a commutative monoid via pushout over a semigroup interface; load it to confirm the pushout and generated morphisms.

pushout/nat_bool.llang + pushout/nat_bool.models.llang + pushout/nat_bool.run.llang demonstrate model restriction: a Nat term is run using a NatBool model via the injection morphism; run `examples/pushout/nat_bool.run.llang` and expect normalized/value output for a Nat term (no result line).
