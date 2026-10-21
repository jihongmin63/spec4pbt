# Native SpecTec property examples

Run commands from the repository root after building the translator.

| Example | Scope |
| --- | --- |
| [ordered](ordered/README.md) | Small certified properties with proof/generator templates and real external adapter execution. |
| [p4_progress](p4_progress/README.md) | Parse and plan instantiation progress against the complete pinned P4 specification. |

Each example keeps its specification/property inputs, observation metadata and
implementation-specific files together. Generated Lean bundles live under an
ignored `Generated*` path in the example; collected test artifacts belong in
`test_cases/`. Bundle paths determine their Lean module names and certificates,
so regenerate a bundle when changing its location.
