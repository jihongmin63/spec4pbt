# spec4pbt

Propose properties from SpecTec specifications, verify them in Lean, and test external implementations with certified input generators.
The default branch is `P4-spectec-based`.

## Repository layout and responsibilities

```text
p4-spectec/                    Official specification: pinned Git submodule
specifications/
  p4/observations.toml         Shared catalog of permitted external P4 observations
properties/
  instantiation_progress/
    property.watsup            Agent-proposed property for user review
    external.toml              This property's selection from the shared catalog
    Proof.lean                emit creates the property proof obligation
    Generator.lean            emit creates the generator obligation
implementations/              Add implementations as needed
  <implementation>.toml        Execution manifest
  <implementation>.py          Adapter
  <implementation>.lean        Optional extra JSON declarations
  local/                       Local implementation sources and builds (Git-ignored)
pbt/                          Python tools for planning, certification, execution, and replay
Spec4Pbt/                     Lean audit kernel for proofs, generators, and execution code
translator/                   Translator sources, patches, native bridge, and provenance
  tests/                      Unmodified imported regression data only
tests/                        Maintained project tests, fixtures/, and ordered/
out/                          Regenerable work products (Git-ignored)
  translator/                 Translator build
  bundles/<property>/          Translated specification, contract, and certificate
  results/<property>/<run>/    Inputs, observations, verdicts, and replay traces
  scratch/                    Temporary Lean modules and projects
```

Keep the property folder name consistent with `--name`. For `instantiation_progress`, the proof module is
`properties.instantiation_progress.Proof` and the fixed bundle path is
`out/bundles/instantiation_progress`. The same relation can be an external observation for one property
and an internal witness for another. The specification's `observations.toml` lists all permitted
external observations; each property's `external.toml` selects only what it uses.
Adapters and execution manifests in `implementations/` are shared across properties.

The root contains this guide, [AGENTS.md](AGENTS.md), and the Git/Lake configuration. Lake manages
its dependencies and compilation cache in `.lake/`. `emit` creates unfinished `Proof.lean` and
`Generator.lean` declarations with explicit failing tactics. Complete them before `check`; they
are not certified examples. Existing authored files are never overwritten. The default `lake build` builds
only `Spec4Pbt` and the Lean regression test. Property and `out` modules are built explicitly as needed
for certification and execution.

## What users provide and review

| Item | Details |
| --- | --- |
| Specification | Version and path, feature or scope to check, and one concrete `observations.toml` catalog of all permitted external relations and output fields. The default source is `p4-spectec/spec/`. |
| Target implementation | Source or executable location, version, build and run commands, input/output formats, and failure criteria. |
| Execution conditions | Test count, size, seed, and timeouts; P4 architecture and external state type representations when needed. |
| Outputs to review | Proposed property, premises, external selection, observation criteria, implementation binding, and execution results. |

Users do not need to write property syntax, Lean proofs, or generators. An agent proposes properties
from the specification and testing goal, and writes an adapter and manifest when implementation details
are available. The current property is **successful instantiation of a type-checked P4 program**.
It assumes `Program_ok` and requires `Program_inst` to succeed. Because `observe = []`, it does not
compare output values. Checking success alone still requires a call to the actual implementation.

## Setup and property planning

### Authored helper relations

A `property.watsup` file may contain ordinary `relation` and `rule` declarations
alongside one or more `property` clauses. Authored rules may only define authored
relations; attempts to replace or extend a relation from the pinned specification
are rejected. `plan` computes the external helper set from relation dependencies
before checking whether each use reads only property inputs and observed outputs.
An observation catalog entry still names a primitive relation, not a helper.

### Shared catalog and property selection

Keep the user's catalog outside the pinned specification checkout. For the
included P4 source, it is `specifications/p4/observations.toml`. Each catalog
entry has an `id`, `relation`, and `observe` array. It grants a maximum external
capability; listing a relation does not make every property call it. A property
selects catalog IDs in `properties/<name>/external.toml`:

```toml
schema_version = 1

[[external]]
id = "instantiation"
observe = []
```

An omitted relation remains internal. A selected relation with `observe = []`
still calls the implementation to check success or failure. Selected output
fields may be narrower than the catalog allows: a selector must be the same as
or inside one catalog selector. `external = []` selects no external calls. The
property author writes this restriction for review; users provide the catalog
once with the specification. A shared implementation manifest may bind other
relations from the catalog, but execution calls only the relations selected by
this property's plan.

The executable subset currently covers zero-output helpers with one rule that
passes its inputs unchanged to one primitive call. Such wrappers can be chained
and can negate a zero-output helper with `:/`. A normal primitive relation failure
is inverted through negation; an adapter error remains an error. Helpers with
output constraints, guards, alternative rules, or recursion are reported as
unsupported at the execution-planning boundary. `emit` rejects a plan with
unsupported uses. A `:/` premise in a property clause becomes logical negation
in its Lean contract. At execution time, only a normal `relation_failure` is
inverted; `abort`, transport errors, and timeouts remain errors. The narrow
helper delegation is checked against typed SpecTec IL by the native audit; a
separate Lean theorem for general helper composition is not yet available.
The authored `ill_typed_rejection` property now plans without unsupported
structures, but has no full-P4 proof, exact-support generator, or real
implementation binding yet. In the ordered translation its `Rejected` helper
requires a normal `unmatch`; logical `¬ TypeChecks` alone does not establish
that outcome. The implementation outcome criteria do not discharge this Lean
proof obligation.

The default ordered translation gives each `extern syntax` its own Lean
inductive type with one nullary constructor, `mk`. No `SpecTecExternTypes`
instance or separate external-type model is required. This deliberately models
each external type as having exactly one value; it does not represent distinct
dynamic P4 states. JSON codecs are derived for types needed by the property.
The intended p4c implementation entry point is `p4test
--validate`, but a certified conversion from generated `p4program` inputs to
P4 source text is still needed before an adapter can bind that relation.
Observation metadata and codec dependency traversal allow nested generic types,
including `map` with different type arguments, and track complete instantiated
types under a 4096-type graph limit. Lean must still compile the derived codecs.
`emit` writes the obligations before native execution auditing. That audit covers
external requests, evaluated condition lets, observed checks, and native goals.
An internal premise such as `Program_ok` is retained in the proof obligation and
generator support, but its omitted relation body is not an execution-audit root.
Its `ir` witness is existential in the premise and is not a generated runtime
input. Executed internal relations still reject hidden external and function
calls. An emitted contract does not constitute a checked bundle; full-P4 proof,
generator, transport, and actual implementation support remain separate gates.

Linux, Python 3.12 or later, Git, opam/C build tools, and `elan`/`lake` are required. Use the Lean
version specified by `lean-toolchain`. Run all commands below from the repository root.

```sh
python3 -m translator.toolchain bootstrap
opam switch create spec4pbt 5.1.1
opam install --switch=spec4pbt --deps-only ./p4-spectec/p4spectec.opam
opam install --switch=spec4pbt yojson
python3 -m translator.toolchain build --switch spec4pbt
lake build

python3 -m pbt.property plan \
  --spec p4-spectec/spec \
  --property properties/instantiation_progress/property.watsup \
  --name instantiation_progress \
  --config specifications/p4/observations.toml \
  --external properties/instantiation_progress/external.toml
```

Reuse a compatible opam switch if one already exists. The official specification is pinned to
`2730cfd9e74048bb5439da0f8afcef124079a064`. Build patches apply only to the copy under
`out/translator/`; the official submodule is left unchanged. To translate directly, use
`python3 -m translator.toolchain translate <spec-path> <translator-options>`. Arguments after
`translate` are passed through to the native translator.

## Emit, check, run

The agent follows [AGENTS.md](AGENTS.md) to propose the property and external
selection, then uses three commands:

1. `emit` generates `Spec.lean`, `Transport.lean`, `Contract.lean`, both audit
   modules, and `emission.json`. It creates `Proof.lean` and `Generator.lean` beside
   the property source if those files do not exist.
2. Fill the proof of `Contract.property` and the value of
   `Contract.generator`. The generated alias is
   `abbrev generator := CorrectGen Premise`: the generator must have
   exactly the support specified by `Premise`.
3. `check` runs the native AL execution audit, reconstructs generated artifacts
   from the original inputs and compares their contents, then compiles and audits
   both authored declarations. Exact type,
   module ownership, permitted axioms, executable code, and transport audits all
   precede certificate creation. A failed check preserves the editable files and
   leaves no valid certificate.
4. `run` verifies certificate freshness and revalidates the recorded Lean audits
   when loading the certificate, then samples from the certified generator,
   calls the selected implementation, and saves traces and verdicts. Generator
   selection is recorded at emission and certified by check; run has no generator
   selection flags. Local certificate hashes are editable data, so loading retains
   independent Lean validation instead of trusting a manually repaired hash list.

```sh
python3 -m pbt.property emit \
  --spec p4-spectec/spec \
  --property properties/instantiation_progress/property.watsup \
  --name instantiation_progress \
  --config specifications/p4/observations.toml \
  --external properties/instantiation_progress/external.toml \
  --output out/bundles/instantiation_progress

# Complete properties/instantiation_progress/Proof.lean and Generator.lean.

python3 -m pbt.property check \
  --bundle out/bundles/instantiation_progress

python3 -m pbt.property run \
  --bundle out/bundles/instantiation_progress \
  --implementation implementations/target.toml \
  --output out/results/instantiation_progress/run-001 \
  --count 100 --size 10 --seed 0
```

The proof file imports `out.bundles.instantiation_progress.Contract`, which exists
before authoring begins. Default declaration names are
`properties.instantiation_progress.Proof.property_correct` and
`properties.instantiation_progress.Generator.generator`. Existing declarations can
be selected with emit's `--proof-module`, `--property-proof`, `--generator-module`,
and `--generator` options. Keep the proof and generator in separate files; the
proof must not import the generator. The generator may import the proof.

Re-running `emit` at the same bundle path refreshes generated files and removes
its certificate, while preserving authored files and unrelated files. Change only
proof/generator code, then re-run `check`. Change the specification, observations,
selection, transport model, or translator, then re-run `emit` and `check`. Never
repair certificate hashes manually. Use a fresh results directory for every run.

`ContractAudit.lean` and `GeneratorAudit.lean` expose the actual verification
commands. `emission.json` records inputs and declaration names; `certificate.json`
(schema 4) records the checked pair and dependency fingerprints. An emitted
bundle without a certificate cannot run. The old CLI `build` command is replaced
by emit/check; old proof-only bundles must be re-emitted and checked. To migrate a
bundle without emission metadata, confirm and remove only its generated bundle
directory first, preserving authored source and results. The legacy Python
`build_property` helper remains for proof-only regression consumers and cannot
certify a generator for run.

External types and codecs are generated automatically. Additional declarations
can be supplied with `emit --transport-model implementations/<implementation>.lean`;
they cannot replace generated external types.

The full-P4 proof, exact-support generator, and real adapter remain unfinished.
Emitting obligations or passing a small ordered fixture does not certify full P4.
The tools check authored proofs and generators; they do not solve them automatically.

## Binding an implementation and inspecting results

Write `implementations/target.toml` for the actual execution relation, file
locations, and classification criteria. New manifests use schema 2:

```toml
schema_version = 2
id = "target"
cwd = ".."

[[executions]]
relation = "Program_inst"
adapter = ["python3", "implementations/target.py"]
artifacts = ["implementations/local/target-binary"]

[executions.outcomes]
match = "the target completes and accepts the relation input"
unmatch = "the target completes and reports an ordinary relation failure"
abort = "the target cannot evaluate the relation input normally"
```

`cwd` is resolved relative to the manifest's parent; `..` above is the repository root. Adapter and
artifact paths are relative to that working directory. Register target executables and auxiliary files
that cannot be discovered from command arguments in `artifacts`. The launcher and script arguments are
fingerprinted automatically.

The three outcome descriptions must be present and are saved with the
implementation identity for review. The adapter applies those criteria to the
actual target result; the TOML descriptions do not classify target output by
themselves. Existing schema 1 manifests remain readable.

The adapter reads `plan_id`, `case_id`, `occurrence_id`, `relation_id`, canonical
`input`, and `observe` from a JSON request on stdin, then calls the actual
implementation. It returns the same four IDs and one of these statuses:
`"success"` (match) with an `observation` object, `"relation_failure"`
(unmatch), or `"abort"` with a nonempty `message`. For a successful response
with `observe = []`, the observation is `{}`. Anything outside the stated
criteria, including a crash or malformed adapter response, is an error. Write
additional diagnostics to stderr.

`result.json` records the verdict and cause. Each case's `trace.json` records the request, response,
observations, and implementation fingerprint. Run verdicts are `passed`/`failed`/`error`; case verdicts
are `pass`/`fail`/`error`. An observation constraint violation is `fail`. Communication, decoding,
abort, and timeout problems are `error`.

```sh
python3 -m pbt.property recheck \
  --bundle out/bundles/instantiation_progress \
  --trace out/results/instantiation_progress/run-001/case-000000/trace.json

python3 -m pbt.property rerun \
  --bundle out/bundles/instantiation_progress \
  --implementation implementations/target.toml \
  --case out/results/instantiation_progress/run-001/case-000000 \
  --output out/results/instantiation_progress/rerun-001
```

`recheck` checks a saved trace without calling the implementation again; `rerun` makes fresh calls to
the specified implementation. `collect --input FILE` uses manual input and does not certify the input
premise. Use `run` for certified inputs. Limit execution time with `--timeout` and `--adapter-timeout`.

## Tool verification

```sh
lake build
python3 -m unittest discover -s tests -t . -v
(cd translator && sha256sum --check SHA256SUMS)
```

See [translator/README.md](translator/README.md) for the translator's support and limitations.
Existing local results were moved to `out/results/`; old bundles are preserved under
`out/results/legacy/bundles/`. Certificates from before the path change must be regenerated in the
new layout rather than reused.
