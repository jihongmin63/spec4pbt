# Predicate reformulation

Test external implementations against a formal specification. An agent rewrites
its input predicate, proves each rewrite equivalent in Coq, and asks QuickChick
to derive a generator from the selected candidate.

```text
specification + Property.spectec
  → prepare → fixed Original.v
  → candidates + equivalence proofs
  → check → derive and sample
  → replay against an implementation / debug against the specification
```

## Files

| Location | Purpose |
| --- | --- |
| `specification/<spec>/` | Shared source specification and regenerated Coq translation (ignored); `Specification.toml` selects ordered sources and a profile. |
| `properties/<name>/` | `Property.spectec`, fixed `Original.v`, and `candidates/vNNN/{Candidate,Equivalence}.v`. |
| `adapters/<implementation>/` | Reusable `Adapter.toml` and implementation bindings. |
| `scripts/` | Commands and property processing code; native bridge code lives in `scripts/property/native/`. |
| `translator/` | AL-to-Coq backend, Coq support, profiles, and translator tests. |
| `environment/` | Installation, pinned dependencies, and compatibility checks. |
| `<property>/.runs/` | Fixed context, property-specific Coq publication, samples, and execution evidence (ignored). |
| `_opam-testing-theorems/` | Local installations, builds, archives, and tool logs (ignored). |

AL-to-Coq emits direct `Generated/InductiveRelations_*.v` relations. Public
predicates in `Relations_0000.v` use `*_execute` with input, `State`,
`Outcome`, and final `State`; `Spec.v` exports these modules. Common Coq
`Action` remains the result type of builtin functions.

Within `scripts/property/`, `cli.py` selects commands, `prepare.py` prepares a
property, `generation.py` derives and samples, and `commands.py` coordinates
replay/debug. `context.py` validates fixed identities. `legacy.py` preserves the
older explicit Pre/Goal workflow. `translator/` owns translation semantics.

## Environment

Use Coq **8.20.0**, OCaml **4.14.2**, and the official *Testing Theorems*
QuickChick fork, not stock QuickChick. The SpecTec frontend uses a separate
OCaml **5.1.1** switch. Versions and source hashes live in
`environment/env.sh` and `environment/opam-switch.export`.

Linux, Python 3.11+, opam, Git, make, C build tools, GMP, pkg-config, Perl,
and network access are needed for setup. Restore the pinned frontend snapshot
as described in [translator/profiles/README.md](translator/profiles/README.md)
before `setup-frontend`.

```sh
bash environment/env.sh setup
bash environment/env.sh setup-frontend
bash environment/env.sh coqc MyExperiment.v
bash environment/env.sh coqtop
```

Both switches and OPAMROOT stay inside this checkout. Preserve previous
installations and evidence, including `_opam-popl18/` if present.

## Write, generate, test

A property declares explicit generated inputs, a goal, and ordered conditions:

```spectec
property [external_result]:
  (x : nat)
  c = $(x + 4)
  -- External: x b u
  -- B: b c
```

Here only `x` is generated. The conditions define the input predicate; `b`, `u`,
and `c` are witnesses. The goal is checked during replay/debug, not generation.
The current syntax accepts one property and one line of typed binders per file.
Negated judgments such as `Exists:/ |- x` work in both the goal and conditions.
P4-spectec's type, binding, and side-condition passes check them: the negated
relation must have no output positions, and every argument must already be bound.
To test whether an output-producing relation has a result, call it inside a
zero-output helper such as `Exists`. Helpers may combine multiple calls, negation,
and native-valid `otherwise` rules. Negation inverts success and `no_match`;
adapter errors and timeouts retain their error status. Iteration and higher-order
callback observation analysis still have property-workflow limitations and are
diagnosed with source locations.

Use the shared demo to follow the complete workflow:

```sh
# 1. Prepare the property and its initial equivalent candidate.
python3 -B -m scripts.property.cli properties/unified_property_demo prepare --spec specification/shared_property_demo/Specification.toml

# 2. Add candidates/v002, v003, ... and check the complete equivalence chain.
python3 scripts/check.py properties/unified_property_demo

# 3. Select a candidate, verify its prefix, derive a generator, and save inputs.
python3 -B -m scripts.property.cli properties/unified_property_demo sample --candidate v001 --count 12 --size 16 --seed 7

# 4. Replace <id> with the sample directory reported above.
python3 -B -m scripts.property.cli properties/unified_property_demo replay --implementation adapters/shared_demo_actual/Adapter.toml --samples-file properties/unified_property_demo/.runs/sample-<id>/samples.json
python3 -B -m scripts.property.cli properties/unified_property_demo debug --samples-file properties/unified_property_demo/.runs/sample-<id>/samples.json
```

`Specification.toml` owns `id`, ordered `sources`, and translation `profile`.
`Adapter.toml` references that ID and supplies external relation commands,
`conversion = "json-v1"`, and zero-based `observed_outputs`. Paths are relative
to the manifest. The shared demo contains examples of both files. Property
authors need no TOML or `Generator.v`.

Each `Equivalence.v` proves `equivalent` against its immediate predecessor:
Original for v001, then v001 for v002, and so on. Keep the specification and
Original fixed. Proofs must close without extra axioms or admissions.
`run.py <property> --candidate vNNN --derive-only` checks that prefix and derives
without sampling; later incomplete candidates do not block it.

Generation and debug need no adapter. Saved inputs can be replayed against
another compatible implementation, such as `adapters/shared_demo_reference/`.
The demo's actual implementation fails the goal at x=7; the reference and
specification debug pass. A command's completion status is separate from the
property outcomes in `status_counts` and `results.json`. `no_generation` means
no input was produced, not a counterexample. Sampling proves neither generator
soundness/completeness nor implementation correctness.

Prepare stores new property translations in `.runs/publication/` and preserves
existing fixed contexts at their recorded locations. `.runs/` is durable local
state, not a disposable cache: it binds samples to the property, specification,
candidate, and tool versions. Changed identities require fresh samples; keep old
evidence. The legacy `property_replay_demo` retains its fixed source layout and
uses `prepare`, `sample`, `replay`, and `debug` through the same CLI. In a new
checkout, regenerate its ignored Coq sources and pass evidence before use:

```sh
python3 -B -m scripts.property.rocq
python3 -B -m scripts.property.rocq --candidate-helper
```

## Translation and maintenance

```sh
# Generate and compile a complete pinned specification (p4 or wasm).
python3 scripts/translate.py --profile wasm --check

# After environment changes, or property-tool changes, respectively:
bash environment/env.sh check
python3 -B -m unittest discover -s scripts/tests -v

# After translator changes:
python3 -B translator/tests/check.py --suite all
```

The translator compiles ignored copies before publishing final `.v` sources.
Use `--check --no-publish` to verify without updating the publication.
Compilation and native regression tests do not establish a general translator
semantic-equivalence theorem. Predicate equivalence remains mandatory;
generator soundness/completeness are outside this experiment's scope.

This branch is independent; do not merge it wholesale into `P4-spectec-based`
or `pbt-experiments`, or modify their worktrees.
