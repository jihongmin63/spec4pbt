# spec4pbt — P4-spectec-based

Translate SpecTec specifications to Lean and test external implementations
against native SpecTec property clauses. Properties are authored in `.watsup`;
Lean checks the property proofs and exact-support generators, and the native
SpecTec AL runner checks the implementation's actual observations.

## Repository layout

```text
p4-spectec/                 Official P4-SpecTec submodule and P4 specification
translator/
  src/                     SpecTec-to-Lean backend and embedded Lean runtime
  bridge/                  Native metadata, property frontend and AL helpers
  patches/                 Frontend/executor extensions and compatibility patches
  toolchain.py             Bootstrap, build and source/binary identity
  translate.py             Checked translation and JSON transport generation
  tests/                   Native integration tests and imported backend regressions
pbt/
  property/                Planning, Lean contracts, certification, execution, replay
  tests/                   Python regressions and Lean generator tests
  CorrectGen.lean           Palamedes generator API
  GoalTools.lean            Lean goal reflection and proof audit
  Observable.lean           Observable-property contracts
examples/
  ordered/                 Complete proof-backed examples, adapters and templates
  p4_progress/             Full-P4 property and observation metadata for planning
scripts/                   Bootstrap, build and translation entrypoints
docs/                      Detailed property workflow
implementations/           Local implementation checkouts/builds (ignored)
test_cases/                Generated inputs, observations and traces (ignored)
```

The property pipeline is split by responsibility:

| Module in `pbt/property/` | Responsibility |
| --- | --- |
| `cli.py`, `__main__.py` | `python3 -m pbt.property`: inspect, plan, build, run, collect, recheck, rerun. |
| `plan.py` | Classify typed AL conditions, external calls and observation dependencies. |
| `emit.py` | Generate the Lean input, premise, and property contract. |
| `clause.py` | Build/audit certified bundles and reject stale dependencies. |
| `implementation.py`, `protocol.py` | Resolve implementation manifests, fingerprint targets and validate adapter communication. |
| `runner.py` | Sample certified inputs, collect outputs, save traces and invoke native AL checking. |

The common `pbt.observations`, `pbt.verify_observable`, `pbt.run_observable`,
`pbt.generate_goals` and `pbt.verify` APIs remain available. Generated P4
translations embed the runtime from `translator/src/lean/`. Each
independent translation has its own `SpecTec` declarations and must be used in a
separate Lean import closure.

## Build

The official [P4-SpecTec](https://github.com/kaist-plrg/p4-spectec) submodule is
pinned to `2730cfd9e74048bb5439da0f8afcef124079a064`. The maintained backend
and integration helpers are tracked in `translator/`; see its
[guide](translator/README.md) and [provenance](translator/PROVENANCE.md).

A fresh checkout needs Git, Python 3.12 or later, opam with a C build toolchain,
and Lean's `elan`/`lake`. The checked-in `lean-toolchain` selects Lean.

```sh
scripts/bootstrap-p4-spectec
opam switch create spec4pbt 5.1.1
opam install --switch=spec4pbt --deps-only ./p4-spectec/p4spectec.opam
opam install --switch=spec4pbt yojson
scripts/build-translator --switch spec4pbt
lake build
```

Use `--switch NAME` for an existing compatible switch. A build without that
option uses the active switch; later commands use the recorded build identity.
Bootstrap optionally accepts `--source PATH` for a local cache of the official
pin. The ignored `translator/_build/p4-spectec/` workspace combines the official
source, local backend and patches without modifying the submodule.

Translate a specification directly with:

```sh
scripts/translate-spec examples/ordered/spec.watsup > /tmp/Ordered.lean
```

`python3 -m translator.translate` additionally generates checked JSON transport
and observation metadata. The [translator guide](translator/README.md) covers
that interface, external-type models and full-P4 translation.

## Writing properties

Write properties with the SpecTec `property` clause extension supplied by this
repository's frontend patches. An explicit input list is followed by a goal and
`--` premises. The [ordered specification](examples/ordered/spec.watsup) defines:

```text
var n : nat

relation Copy: nat ~> nat
  hint(input %0)
rule Copy/value: n ~> n

relation Internal: nat ~> nat
  hint(input %0)
rule Internal/value: n ~> n
```

Its [property file](examples/ordered/properties.watsup) includes:

```text
property progress:
  (n : nat)
  Copy: n ~> y
  -- Internal: n ~> x
```

Only `n` is generated. `x` is an internal existential witness for the premise;
`y` is a goal output. With the supplied [observation metadata](examples/ordered/observations.toml),
`Internal` stays in proof-only conditions and `Copy` is collected externally.
Relation input slots come from `hint(input ...)`. Observation selectors choose
which outputs are exposed to the checker; a separate
[implementation manifest](examples/ordered/implementations/correct.toml) binds
the external relation to its adapter and target.

An observed output can also be constrained by a condition:

```text
property positive:
  (n : nat)
  v = v
  -- Copy: n ~> v
  -- if $(v > 0)
```

All source conditions remain in the generated Lean premise. This example's
certified generator supports exactly `n > 0`; the native checker also checks
`v > 0` against the actual observation, so returning zero fails. The `chain`
example feeds one observation into a later request. A condition mixing a
private internal witness with an observed value is currently rejected.

## Plan and run

Run these commands from the repository root after building:

```sh
python3 -m pbt.property plan \
  --spec examples/ordered/spec.watsup \
  --property examples/ordered/properties.watsup \
  --name progress --config examples/ordered/observations.toml

python3 -m examples.ordered.run \
  --property progress \
  --bundle examples/ordered/GeneratedProgress \
  --output test_cases/property-progress --count 4 --size 5 --seed 0
```

Use fresh bundle and output paths. The example runner instantiates supplied
Lean proof/generator templates. Supported examples are `positive`, `chain`,
`independent`, `internal_positive` and `progress`; `--mode zero` or `--mode reject`
selects intentionally incorrect implementations. Custom properties need a proof
of the generated `SpecProperty` and a `CorrectGen Contract.Premise` generator.
No arbitrary property is proved automatically.

The bundle path is a generated directory containing the translated SpecTec
specification, the property proof check, the relation call plan, and file hashes.
The example runner reads it when calling the selected implementation and
checking its responses. The case results go to the separate `--output` path.

The [full-P4 property](examples/p4_progress/progress.watsup) uses the same syntax:

```text
property instantiation_progress:
  (p : p4program)
  Program_inst: |- p : l s
  -- Program_ok: |- p : ir
```

Here `p` is generated, `ir` is the internal typing witness, and `l`/`s` are
instantiation outputs. Parse and plan it with:

```sh
python3 -m pbt.property plan \
  --spec p4-spectec/spec \
  --property examples/p4_progress/progress.watsup \
  --name instantiation_progress \
  --config examples/p4_progress/observations.toml
```

Certified full-P4 execution additionally requires a concrete implementation
adapter, external-type codecs, a property proof and a certified
generator. See the [property guide](docs/property-clauses.md) for custom
build/run, adapter contracts, saved-trace rechecking and rerunning implementations.

## Verification

```sh
lake build
python3 -m unittest discover -s translator/tests -t . -v
python3 -m unittest discover -s pbt/tests -t . -v
```

Imported backend regression commands and checksum verification are documented in
the [translator guide](translator/README.md#verification).
