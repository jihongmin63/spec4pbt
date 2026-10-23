# Repository working rules

Use `P4-spectec-based` as the baseline. Read README.md for user inputs, commands,
implementation protocol, and the current full-P4 limitations.

## Responsibilities and boundaries

Users supply the specification selection, implementation details, and execution
conditions, including one concrete `observations.toml` catalog of every
permitted external relation and output field for the specification. Propose
properties and property-specific restrictions from that information;
users review their meaning and the resulting evidence. Users do not have to
write property syntax, proofs, or generators themselves.

- `properties/<name>/`: authored property, per-property `external.toml`, `Proof.lean`,
  and separate `Generator.lean`. `emit` may create explicit failing obligation
  templates for the author to complete; never treat those as proofs, add empty
  files, or claim fake full-P4 proofs.
- `specifications/<spec-id>/observations.toml`: user-provided catalog of all
  permitted external observations for that specification. Do not write it into
  the pinned `p4-spectec/` checkout.
- `implementations/`: shared flat `<implementation>.toml`, adapter `.py`, and
  optional external-type/JSON model `.lean`. Keep local checkouts/builds in
  ignored `implementations/local/`. Resolve `cwd` relative to the manifest parent.
- `scripts/`, `translator/`: automation and trusted audit infrastructure.
  A property-authoring task must not change these to make its property pass.
  Tool changes require a separate, explicitly scoped task and regression checks.
- `p4-spectec/`: pinned official submodule, pristine. Integration patches belong
  in `translator/patches/` and apply only to the copied build under `build/translator/`.
  Imported `translator/src/`, imported `translator/tests/`, and LICENSE must match
  `translator/SHA256SUMS`; do not edit them during property work.
- `scripts/tests/`: all maintained Python/Lean tests, test fixtures, and small ordered
  regression examples. `translator/tests/` contains only unchanged imports.
- `properties/<name>/bundle/` and `runs/`: ignored generated verification artifacts
  and saved execution evidence. Never erase runs while regenerating a bundle.
- `specifications/<spec-id>/translated/`: shared generated Lean specifications,
  keyed by source/tool/options identity. Do not put the whole spec in property bundles.
- `build/`: ignored native builds and temporary Lean modules/projects. Do not
  write temporary Lean source into `scripts/lean/Spec4Pbt/`.

## Property workflow

Run Python module commands from the repository root.

1. Choose a stable property name. Keep the folder, `--name`, proof/generator
   module prefix, bundle directory, and results directory consistent:
   `properties/<name>/`, `properties.<name>.Proof`, `properties/<name>/bundle/`,
   `properties/<name>/runs/<run>/`.
2. Propose `property.watsup` and its `external.toml` restriction together. Select
   only catalog IDs and output selectors allowed by the specification's shared
   `observations.toml`; a relation omitted from the restriction stays internal.
   A selected relation with `observe = []` still checks its success or failure.
   Never broaden the user's catalog to make a property pass. Explain any change
   to the user's intended premises or expected behavior.
   Format authored SpecTec declarations with the relation or rule name on its
   own header line, followed by the goal, optional hint, and each `--` premise
   on separate indented lines. Use the same line-separated layout for properties.
3. Run `python3 -m scripts.property plan` with `--config <catalog>` and
   `--external properties/<name>/external.toml` to classify inputs, internal
   witnesses, external calls, and observation dependencies. Report unsupported
   structures and missing implementation information.
4. Run `python3 -m scripts.property emit` (its default output is the property
   source sibling `bundle/`) at the fixed `properties/<name>/bundle/` path.
   This generates the contract and visible audit modules, and creates unfinished
   `Proof.lean` / `Generator.lean` declarations only when absent. Re-emission
   preserves authored code and results, refreshes generated files, and invalidates
   the certificate. A legacy bundle without emission metadata must first be
   removed after confirming its resolved generated path; preserve source/results.
5. Complete the exact `Contract.property` proof and `Contract.generator`
   value (`CorrectGen Contract.Premise`). Use no extra assumptions, `sorry`,
   unsupported axioms, or compiler substitutions. Exact support must cover the
   intended input domain. The generator may import the proof; the proof must not
   import the generator. Keep their source files separate.
6. Run `python3 -m scripts.property check --bundle properties/<name>/bundle` to perform the
   native AL execution audit, reconstruct and compare generated artifacts,
   compile the completed files, and audit proof,
   generator, executable code, and transport before issuing the joint certificate.
   Check failure preserves authored files and leaves no valid certificate. Changes
   to either authored module require a new check; source/config/tool changes
   require emit followed by check. Never repair certificate hashes manually.
7. Connect the actual implementation and explicit external-type/codec model.
   Run with `python3 -m scripts.property run`; it uses the generator already selected
   and certified by check, with freshness checks before use. Save each run to a
   fresh `properties/<name>/runs/<run>/` and explain pass/fail/error evidence. Use
   `recheck` for saved traces, `rerun` for fresh implementation calls. `collect`
   does not certify the input premise.
8. Report exactly what is proven and executed. Planning and ordered fixture
   success do not establish full-P4 certification. The checked-in
   `instantiation_progress` property currently has no completed proof, generator,
   or real implementation adapter.

## Tool maintenance

Repository/build/native executable paths are defined in `scripts/toolchain.py`;
maintained test roots are defined in `scripts/tests/__init__.py`. Import those definitions
instead of copying parent-depth calculations or executable paths. Locate property
Python sources for certificate fingerprints relative to their own `__file__`.
Temporary generated module names use `build.scratch.<name>`.

`Spec4Pbt` is the only default Lake target. The Lean regression is explicit:
`lake build scripts.tests.CorrectGenTests`. `properties`, `specifications`, and
`build` are explicit libraries; do not make unfinished proofs or historical
output part of `lake build`. Property-only work does not run the full tool suite.
For tool changes, run affected checks; run the full suite after integrating
changes to certification, translation, or repository layout.

After applicable tool changes run:

```sh
python3 -m scripts.toolchain build --switch <available-switch>
lake build
lake build scripts.tests.CorrectGenTests
python3 -m unittest discover -s scripts/tests -t . -v
(cd translator && sha256sum --check SHA256SUMS)
```

Also exercise real certification/execution when the changed boundary affects it.
Preserve negative proof, axiom, generator, compiler rewrite, transport, freshness,
and timeout checks. Keep local data when moving paths. Do not commit caches,
certificates, execution traces, or implementation checkouts.
