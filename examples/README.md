Polygraph examples

This directory is split into reusable libraries and executable build files:

- `examples/build/**`: build-native example entrypoints.
- `examples/run/**`: restored legacy paths implemented on the build/module surface.
- `examples/lib/**`: shared doctrines, functor/apply examples, and templates used by tests.
- `examples/endtoend/**`: larger staged examples, including restored historic paths for standalone migrated programs.

Current build examples:

- `examples/build/hello_doc.llang`: minimal module/interface/doc emission path.
- `examples/build/bundle_docs.llang`: module linking, bundling, and host emission.
- `examples/build/doctrine_data_package.llang`: doctrine-backed module `data` packages plus opaque interface import/export.
- `examples/build/logic_full_adder_codegen.llang`: structured JS emission plus reflected quotation debug output.
- `examples/build/explicit_sharing_js_codegen.llang`: reflected quotation over a small arithmetic program.
- `examples/build/autodiff_times_sin.llang`: type-changing forward AD to JS plus a core-view build.
- `examples/build/autodiff_times_sin_pair_core.llang`: endomorphic pair-based AD with JS and reflected-IR builds.

For explicit canonical-target coverage mapping, see `docs/CANONICAL_COVERAGE.md`.
