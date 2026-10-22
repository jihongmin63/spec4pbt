# Repository working rules

Use `P4-spectec-based` as the baseline. Read README.md for user inputs, commands,
implementation protocol, and the current full-P4 limitations.

## Responsibilities and boundaries

Users supply the specification selection, implementation details, and execution
conditions. Propose properties and observation criteria from that information;
users review their meaning and the resulting evidence. Users do not have to
write property syntax, proofs, or generators themselves.

- `properties/<name>/`: authored property, per-property observations, `Proof.lean`,
  and separate `Generator.lean`. Create proof/generator files when implementing
  them, never empty placeholders or fake full-P4 proofs.
- `implementations/`: shared flat `<implementation>.toml`, adapter `.py`, and
  optional external-type/JSON model `.lean`. Keep local checkouts/builds in
  ignored `implementations/local/`. Resolve `cwd` relative to the manifest parent.
- `pbt/`, `Spec4Pbt/`, `translator/`: automation and trusted audit infrastructure.
  A property-authoring task must not change these to make its property pass.
  Tool changes require a separate, explicitly scoped task and regression checks.
- `p4-spectec/`: pinned official submodule, pristine. Integration patches belong
  in `translator/patches/` and apply only to the copied build under `out/translator/`.
  Imported `translator/src/`, imported `translator/tests/`, and LICENSE must match
  `translator/SHA256SUMS`; do not edit them during property work.
- `tests/`: all maintained Python/Lean tests, test fixtures, and small ordered
  regression examples. `translator/tests/` contains only unchanged imports.
- `out/`: ignored generated bundles, results, translator builds, temporary Lean
  modules/projects. Do not write temporary Lean source into `pbt/` or `Spec4Pbt/`.

## Property workflow

Run Python module commands from the repository root.

1. Choose a stable property name. Keep the folder, `--name`, proof/generator
   module prefix, bundle directory, and results directory consistent:
   `properties/<name>/`, `properties.<name>.Proof`, `out/bundles/<name>/`,
   `out/results/<name>/<run>/`.
2. Propose `property.watsup` and `observations.toml` together. A relation may be
   external for one property and internal for another; never share a global
   observations file across unrelated properties. Explain any change to the
   user's intended premises or expected behavior.
3. Use `python3 -m pbt.property plan` to classify inputs, internal witnesses,
   external calls, and observation dependencies. Report unsupported structures
   and missing implementation information.
4. Write `Proof.lean` importing `out.bundles.<name>.Contract`. The contract can be
   absent initially: `build` generates it before compiling the proof module.
   Prove the exact `Contract.SpecProperty`, with no extra assumptions, `sorry`,
   unsupported axioms, or compiler substitutions that bypass certification.
5. Use `python3 -m pbt.property build` to create and audit the bundle. Rebuild at
   the same fixed path: remove only the intended `out/bundles/<name>/` first.
   Confirm the resolved target is that generated bundle before removing it;
   preserve authored source and existing results. Never repair stale certificate
   hashes manually. Directory existence is intentionally an error in `build`.
6. Write `Generator.lean` separately with `CorrectGen Contract.Premise` and exact
   support. It may import the proof; the proof must not import the generator.
   Adding generator code to an already certified proof changes its hash and
   invalidates certification. Do not narrow the input domain to hide failures.
7. Connect the actual implementation and explicit external-type/codec model.
   Run with `python3 -m pbt.property run`; the generator is audited before use.
   Save each run to a fresh `out/results/<name>/<run>/` and explain pass/fail/error
   evidence. Use `recheck` for saved traces, `rerun` for fresh implementation calls.
   `collect` does not certify the input premise.
8. Report exactly what is proven and executed. Planning and ordered fixture
   success do not establish full-P4 certification. The checked-in
   `instantiation_progress` property currently has no completed proof, generator,
   or real implementation adapter.

## Tool maintenance

Repository/build/native executable paths are defined in `translator/toolchain.py`;
maintained test roots are defined in `tests/__init__.py`. Import those definitions
instead of copying parent-depth calculations or executable paths. Locate property
Python sources for certificate fingerprints relative to their own `__file__`.
Temporary generated module names use `out.scratch.<name>`.

`Spec4Pbt` and the Lean regression test are default Lake targets. `properties` and
`out` are explicit libraries, built by module as needed; do not make unfinished
proofs or historical generated output part of `lake build`.

After applicable tool changes run:

```sh
python3 -m translator.toolchain build --switch <available-switch>
lake build
python3 -m unittest discover -s tests -t . -v
(cd translator && sha256sum --check SHA256SUMS)
```

Also exercise real certification/execution when the changed boundary affects it.
Preserve negative proof, axiom, generator, compiler rewrite, transport, freshness,
and timeout checks. Keep local data when moving paths. Do not commit caches,
certificates, execution traces, or implementation checkouts.
