# Predicate reformulation

Test external implementations against properties of a formal specification,
using input generators that QuickChick derives from Coq predicates. To obtain more efficient generators, an agent
rewrites the input condition of a property as a sequence of predicates, each
proved equivalent to its predecessor in Coq, and QuickChick derives the
generator from a selected predicate in the sequence.

## Branch responsibilities

`predicate-reformulation` is an independent branch. It contains the pinned
Coq/QuickChick environment, an environment example, the AL-to-Coq translator,
and the tools that check predicate reformulation sequences. P4 and Wasm inputs
and the tools that regenerate their Coq specifications belong to this branch; the property
workflow also uses this branch. Do not merge this
branch wholesale into `P4-spectec-based` or `pbt-experiments`.

## Repository layout and responsibilities

```text
environment/
  env.sh                     Setup, execution, and environment checks
  opam-switch.export         Pinned package versions, sources, and checksums
specification/<spec-name>/
  Spec.v                     Generated public imports (ignored; created after check)
  Generated/*.v              Generated Coq sources (ignored)
translator/
  src/                       Typed AL lowering and Coq emission
  coq/                       Pure execution and builtin support
  profiles/                  Pinned inputs and authored execution policies
  tests/                     Real frontend, Coq and native comparison regressions
properties/<name>/
  Original.v                 Input type and original predicate (fixed)
  candidates/vNNN/
    Candidate.v              Reformulated predicate
    Equivalence.v            Equivalence with the preceding predicate
  .runs/                     Per-run snapshots, logs, and results (ignored)
adapters/                    Bindings to external implementations (reserved)
scripts/
  check.py                   Checks the entire equivalence chain
  run.py                     Checks a prefix; derives and samples its generator
  translate.py               Audits full AL generation; compiles and publishes
  tests/                     Regressions that run the real Coq toolchain
_opam-testing-theorems/      Dedicated opam root, two switches, sources and logs (ignored)
_opam-popl18/                Preserved earlier installation and evidence (ignored)
```

## What users provide and review

| Item | Details |
| --- | --- |
| Specification | Coq definitions in `specification/<spec-name>/Spec.v`. |
| Original property | `properties/<name>/Original.v`: the input type and the predicate that every test input must satisfy. |
| Target implementation | Location, version, build and run commands, input/output formats, and failure criteria. |
| Execution conditions | Sample count, size, seed, and timeouts. |
| Outputs to review | Candidate sequence, equivalence proofs, derived generator, samples, and execution results. |

An agent writes candidate reformulations and their equivalence proofs.
QuickChick's tactic derives an Input generator from the selected candidate.
Generator soundness and completeness are not proved by this workflow.

## Setup

| Component | Pinned version |
| --- | --- |
| Coq (former name of Rocq) | 8.20.0 |
| Coq switch OCaml | 4.14.2 |
| QuickChick | Official Testing Theorems artifact fork (`coq-quickchick.dev`) |
| MathComp ssreflect | 1.19.0 |
| Frontend switch OCaml | 5.1.1 |

The official source-context archive from [Zenodo record 22087774](https://zenodo.org/records/22087774)
is pinned by SHA-256
`876e30bf41477f9a90077e3876df08555c77b624b35e11508500f4ae01e7035a`.
This hash identifies the nested source-context archive, not the outer Docker
artifact. The script verifies it before extraction and pins that fork, without
substituting stock QuickChick. Coq dependencies and their source checksums are
recorded in `environment/opam-switch.export`.

The environment requires Linux, Python 3, Git, opam, make, a C compiler, Perl,
GMP development headers, pkg-config, and network access. Run from this checkout:

```sh
JOBS=2 bash environment/env.sh setup
JOBS=2 bash environment/env.sh setup-frontend
bash environment/env.sh check
bash environment/env.sh coqtop
bash environment/env.sh coqc MyExperiment.v
bash environment/env.sh frontend ocamlc -version
```

`setup` initializes a dedicated `OPAMROOT` at
`_opam-testing-theorems/opam-root/` and a Coq switch at
`_opam-testing-theorems/coq-switch/`. `setup-frontend` creates the separate
`frontend-switch/`, reads the pinned P4-SpecTec source's package declaration,
and installs its dependencies. The frontend source must first be present at
`_opam-testing-theorems/sources/p4-spectec/`. Both commands can be rerun and
default to two jobs. Every opam invocation explicitly selects the local root;
switch commands also select the appropriate switch. Initialization disables
opam's user-namespace sandbox in this dedicated root for container compatibility.
No global opam configuration or shell profiles are changed.

Sources, builds, temporary files, caches, opam logs, installation logs, and
checks remain under `_opam-testing-theorems/`. Earlier `_opam-popl18/`
installations and verification evidence are preserved.

## Environment check

`environment/checks/Generating2018.v` derives a generator for even natural numbers. The compatibility
examples in `environment/checks/` exercise generation, decision/enumeration,
merge, and the artifact's theorem-testing tactic. The tactic example aborts its
interactive theorem after testing; it does not provide a theorem proof.

`check` compiles copies of these files, requires a successful 10,000-sample
QuickChick result for each, and kernel-checks their compiled declarations with
`coqchk`. It writes a fresh `_opam-testing-theorems/checks/verification.*/`
directory and a log under `_opam-testing-theorems/logs/`, preserving previous
runs. Sampling checks do not prove generator soundness or completeness.
The property workflow uses the pinned tactic and checks predicate equivalence
with closed proofs without additional axioms or admissions. Sampling does not
prove generator soundness or completeness.

## Translate the complete P4 and Wasm specifications

The translator reads the pinned OCaml frontend's `Lang.Al` directly. P4 uses
revision `2730cfd9e74048bb5439da0f8afcef124079a064`; Wasm uses all 18 files
from wasm-ntt `4773b2b7abe56e61f279ec2340ac0d3c836b5033`, imported through
`16142ff23b30611a3fba1bb0ceb0dd7928187d58`. Source archives, checksums,
licenses, and the separate frontend switch stay under the dedicated environment.
The Wasm source copy and its provenance remain in `specification/wasm/source/`.

```sh
# Inspect the complete AL without claiming generation or compilation
python3 scripts/translate.py --profile p4 --inventory
python3 scripts/translate.py --profile wasm --inventory

# Regenerate, compile, then publish ignored local source files
python3 scripts/translate.py --profile p4 --check
python3 scripts/translate.py --profile wasm --check

# Real Coq, frontend, lowering, builtin and complete-specification regressions
python3 translator/tests/check.py --suite all
```

Without `--inventory` or `--check`, the driver generates and audits all source
files but leaves `coq_compiled` and `translation_complete` false. A successful
`--check` requires every emitted Coq file to compile before it copies `Spec.v`
and `Generated/*.v` into `specification/<profile>/`. These outputs are ignored by Git and must be regenerated after a fresh checkout.
Existing managed files are
archived byte for byte under the ignored run before a changed copy is written;
unrelated differing files stop publication. The Wasm `source/` directory and
other unrelated files are preserved.

Every run records source pins, tool versions, commands and return codes,
backend/runtime/source hashes, all output hashes, and a manifest in a fresh
`_opam-testing-theorems/logs/translate-<profile>-*/` directory. Its inventory
accounts for every AL declaration as a generated type, generated body, or
consumed variable metadata. Full generation requires no pending or skipped
declarations, exactly one body for every callable signature, and validated
bindings for all 47 P4 or 76 Wasm builtin declarations. The manifest separates
`code_generation_complete` from `coq_compiled`; only successful compilation
makes `translation_complete` true. Run manifests record the validated AL signatures and concrete source/runtime
binding locations. Input profiles remain unchanged by generation and checking.
Managed output hashes are stored in `_opam-testing-theorems/publication/<profile>.json`.

Source values and type parameters use Coq `Set`; source value dictionaries use
`ValueOps@{Set}`. Function-reference codes preserve the pinned AL's named
monomorphic targets while callbacks may carry free source type parameters.
The typed call family lives one universe above source values so its
constructors can quantify over source types. These choices keep the large
P4 call family and its dependent execution bodies within Coq's universe rules.

Source calls remain typed `Call` nodes. `Action` and the common `Eval` relation
preserve first success, explicit `Unmatch`, immediate error propagation, and
fresh-state consumption. Extern syntax has one constructor; extern callable
results permit every typed output. Ordinary empty syntax remains empty, and
ordinary bodyless functions fail by `Unmatch`. No unsupported builtin becomes
an extern or an arbitrary result. Wasm numeric traps, host conversion errors,
and structure errors remain distinct, including source-typed invalid numbers
and memory inputs.

Builtin regressions compare exact native results with Coq computation. The
Wasm suite covers scalar, floating, SIMD/relaxed and memory operations, with
its donor/license provenance in `translator/tests/builtins/wasm/`. Native
sampling and Coq compilation are regression evidence; they do not establish
whole-translator semantic equivalence or generator correctness/completeness.
`Generator.v` and generator proofs are outside this translation task. Predicate
equivalence proofs in the separate property workflow remain mandatory.

Each ignored suite/run report preserves its commands, results and source hashes. Full-profile success is established by the corresponding
successful `--check` manifest, rather than by an inventory or helper test.

## Reformulate, check, run

1. Keep the specification and `Original.v` fixed. `Original.v` provides
   `Input : Type`, `predicate : Input -> Prop`, and
   `encode_input : Input -> string` that emits typed JSON. If the input
   condition involves several values, define `Input` as a record. Provide a
   `Show Input` instance for tactic diagnostics.
2. The agent adds candidates `v001`, `v002`, … under `candidates/`. Each
   `Candidate.v` defines a `predicate` over the same input type, and each
   `Equivalence.v` proves `equivalent` against the immediately preceding
   predicate (`Original` for `v001`). Numbering is contiguous from 1.
   Intermediate candidates need not be derivable; the candidate selected for
   generation must be an inductive relation that the pinned QuickChick
   derivation supports.
3. `check.py` type-checks each link against its expected statement, composes
   the links into one equivalence between the original and the last candidate,
   and requires the result to be closed without additional axioms.
4. `run.py --candidate vNNN` re-checks the chain up to `vNNN`, renames the
   checked prefix in derivation-only copies, and applies the pinned `quickchick`
   tactic to the selected predicate. The tactic generates only the theorem's
   Input variable. The theorem, extracted generator, and supplied `encode_input`
   function are checked; generator soundness and completeness are not proved.
   Later incomplete candidates do not block the run. Unless `--derive-only` is
   given, it samples the generator.

Import the specification as `Specification.<spec-name>.Spec`, the original as
`Property.Original`, and a candidate as, for example,
`Property.candidates.v001.Candidate`. Directory and file names must therefore
be valid Coq identifiers (use `_` instead of `-`). The first `Equivalence.v`
has this interface:

```coq
Require Property.Original Property.candidates.v001.Candidate.

Theorem equivalent : forall x : Property.Original.Input,
  Property.Original.predicate x <->
  Property.candidates.v001.Candidate.predicate x.
Proof.
  (* the actual equivalence proof *)
Qed.
```

```sh
# Check the entire chain Original ↔ v001 ↔ v002 ↔ … without deriving generators
python3 scripts/check.py properties/<name>

# Check the chain up to v002, then derive and verify its tactic generator
python3 scripts/run.py properties/<name> --candidate v002 --derive-only

# Perform the same verification for v001, then sample its generator
python3 scripts/run.py properties/<name> --candidate v001 --samples 100 --size 30 --seed 0
```

Each run is stored in a new directory under the property's `.runs/`, containing
source snapshots, the derived `Derived.v`, command logs with timings, and
`result.json`. Sampling also writes `samples.json`: each value is typed JSON
emitted by `Original.encode_input`, and `null` records that the generator
returned no value, which is distinct from a property counterexample. A
diagnostic `Show Input` instance may still be needed by the tactic. If the
pinned extractor needs its integer type alias
workaround, it is applied identically to the `.ml` and `.mli` files, and the
unmodified files are kept.

The generator factory theorem is closed without assumptions; it does not state
generator correctness. Authored sources may not contain axioms, admissions,
execution commands, extraction
directives, load-path overrides, or directives that disable checking. A run
fails if any snapshotted source or tool changes while it is in progress, and
`--timeout` (default: 120 seconds) limits each subcommand. These checks are
intended for trusted local developments, not as a sandbox for malicious Coq
code, and they do not verify the extraction runtime that executes the
generator.

## Authoring a property

Write the inputs and goal on separate lines below the property header:

```spectec
property [external_result]:
  (x : nat)
  c = $(x + 4)
  -- External: x b u
  -- B: b c
```

The explicit binders define generated Input fields. The ordered conditions bind
local witnesses, here `b`, `u`, and `c`. The goal may be a boolean expression or
a relation judgment. Native SpecTec parsing, type checking, and binding analysis
check the conditions and goal. Only goal-needed witnesses cross the internal
Pre/Goal execution boundary; the example can observe `b` without observing `u`.
Goal is excluded from the generation predicate.

Shared setup belongs to the specification and implementation:

```text
specification/shared_property_demo/Specification.toml
specification/shared_property_demo/source/Relations.watsup
adapters/shared_demo_actual/Adapter.toml
adapters/shared_demo_actual/external.py
properties/unified_property_demo/Property.spectec
```

`Specification.toml` declares an `id`, ordered `sources`, and translation
`profile` (`fixture`, `p4`, or `wasm`); `namespace` may explicitly name the
profile's namespace. Paths are relative to the manifest. `Adapter.toml`
references that specification ID and supplies reusable `[[external]]` entries:

```toml
specification = "shared_property_demo"

[[external]]
relation = "External"
adapter = "external"
command = ["python3", "external.py"]
conversion = "json-v1"
observed_outputs = [0]
```

Commands are argv arrays. Local script paths are resolved relative to the
adapter manifest; explicit `dependencies` record additional implementation
files. Observed positions index relation outputs, starting at zero. Each
property's observation requirements are checked before execution. An unused
catalog mapping does not activate an external replacement boundary.

Prepare the property, check its equivalence chain, and generate inputs:

```sh
python3 -B -m scripts.property.cli properties/unified_property_demo prepare --spec specification/shared_property_demo/Specification.toml
python3 scripts/check.py properties/unified_property_demo
python3 scripts/run.py properties/unified_property_demo --candidate v001 --derive-only
python3 -B -m scripts.property.cli properties/unified_property_demo sample --candidate v001 --count 12 --size 16 --seed 7
```

The first prepare publishes checked relations under the selected specification's
`properties/<directory-name>/`, creates `Original.v` and an initial equivalent
`candidates/v001`, and saves an automatic `.runs/property-context.json` connection.
Authors do not supply a property TOML or Generator.v. Later commands validate
the fixed property, specification, publication, and Original. `check.py` and
`run.py` use the same validated publication connection.

Replay a saved batch against either implementation, or debug it using the
specification alone (replace `<id>` with the sample directory printed in the
sample report):

```sh
python3 -B -m scripts.property.cli properties/unified_property_demo replay --implementation adapters/shared_demo_actual/Adapter.toml --samples-file properties/unified_property_demo/.runs/sample-<id>/samples.json
python3 -B -m scripts.property.cli properties/unified_property_demo replay --implementation adapters/shared_demo_reference/Adapter.toml --samples-file properties/unified_property_demo/.runs/sample-<id>/samples.json
python3 -B -m scripts.property.cli properties/unified_property_demo debug --samples-file properties/unified_property_demo/.runs/sample-<id>/samples.json
```

Generation and debug need no adapter. Samples record fixed semantic identities,
the selected candidate's proof/publication dependencies, tools, and generation
parameters. Replay separately records implementation identities. Changing an
adapter permits another replay of the same semantic samples. A changed
specification, property, or selected candidate publication invalidates them.

For `x=7`, the actual adapter returns `b=20`, so `c=21` and the goal fails.
The reference adapter and debug produce `b=10`, `c=11`, and a passing goal.
The unused output `u` is never requested from either adapter. Source locations
and variable labels in diagnostics/traces refer to the authored files. The
top-level report status describes command completion; `status_counts` and each
entry in `results.json` describe property results.

`properties/unified_property_guard/` reuses the same setup and adds
`-- if x = 7`. Non-relation conditions become temporary AL relations, then Coq
inductive relations through the existing translator. Each successful premise is
a separate constructor arrow; intermediate values and states stay witnesses.
The ordinary demo permits every natural input and its goal is only true at 7;
the guarded demo restricts generation to 7. Generation may return `no_generation`
for an attempt; every generated input must still satisfy the predicate.

For example, the ordinary demo's generated `Original.v` has this constructor
structure (only generated variable names are shortened here):

```coq
Inductive predicate : Input -> Prop :=
| precondition : forall (x b u c : nat) (s1 s2 : State),
    g_fixture_rel_External_execute x {| next_fresh := 0 |}
      (Success (b, u)) s1 ->
    g_fixture_rel_B_execute b s1 (Success c) s2 ->
    predicate (mkInput x).
```

Both premises must hold to construct `predicate (mkInput x)`. They appear as
separate `->` arguments. The goal `c = x + 4` is checked during replay/debug.
Adding `-- if x = 7` inserts another constructor argument for the translated
temporary relation, before `External`, and threads its resulting state onward.
The encoded sample contains just `{"x":{"type":"nat","value":"7"}}`;
`b`, `u`, `c`, and states are predicate witnesses.

The current declaration supports one property per file and one line of typed
input binders. Iteration, negation, otherwise, and higher-order property forms
retain the existing explicit unsupported diagnostics. `()` supports zero-arity
properties, but the pinned grammar cannot represent zero explicit inputs with
witness outputs required by the goal. Predicate equivalence is checked without
additional axioms; generator soundness/completeness remain `not_checked`.

## Legacy Pre/Goal example

The demo property is in `properties/property_replay_demo/`. Its fixed SpecTec
source is published as checked Coq relations in
`specification/property_replay_demo/`. Candidate v002 adds a separate SpecTec
helper through the same frontend and translator passes. `PassEvidence.json`
records the source, AL pass, translator, and generated Coq hashes.
`scripts.property.rocq.translate_property` lowers the typed single-rule `Pre`.
Variable-only calls apply existing translated relations. Other premises and
computed returns become temporary AL relations and use the same translation
pipeline. `render_original` builds an Input record, existential constructor
witnesses, and a typed JSON encoder; Goal is excluded from generation.
Each premise receives the preceding final state, beginning with fresh_id 0.
First order function calls participate in observation analysis and replay
projection, including calls in computed returns. Trace wrappers retain native
expression evaluation order and carry each function's output dependencies.

Input transport supports nat, int, text, bool, and concrete constructor ADTs,
including nested values. Encoders use the translator's type metadata, with
exact decimal numbers and UTF-8 JSON text. Type generators supply valid UTF-8
strings; the pinned tactic derives the predicate generator. Neither `Show`
nor generator witnesses enter the wire format. The fixed demo sources and
Original remain unchanged.

Candidate helper publications can use separate `candidate_vNNN` profiles and
`CandidateVNNNSpec` namespaces. Their manifests retain the SpecTec source,
frontend AL output, backend manifest, generated Coq hashes, and translator hash.
Only the selected candidate prefix and its imported dependency closure are
compiled in ignored snapshots.

`scripts.property.cli` keeps generation, implementation replay, and
specification debug as separate commands. The native bridge uses the pinned
P4-SpecTec AL interpreter. Replay replaces only declared external relations
with adapter callbacks, checks their typed observed output slots and fresh
counter, and projects unused output slots in the AL execution copy. Debug runs
the full specification and starts no adapter.

```sh
# Regenerate checked legacy demo relations and helper evidence after checkout
python3 -B -m scripts.property.rocq
python3 -B -m scripts.property.rocq --candidate-helper
python3 -B -m scripts.property.cli properties/property_replay_demo prepare --target replay
python3 -B -m scripts.property.cli properties/property_replay_demo prepare --target debug
python3 -B -m scripts.property.cli properties/property_replay_demo sample --candidate v001 --count 12 --size 16 --seed 7
python3 -B -m scripts.property.cli properties/property_replay_demo replay --samples-file properties/property_replay_demo/.runs/sample-<id>/samples.json
python3 -B -m scripts.property.cli properties/property_replay_demo debug --samples-file properties/property_replay_demo/.runs/sample-<id>/samples.json
```

Each command writes a new property-local `.runs/` directory. The first validated
operation fixes the original sources in `.runs/fixed-original.json`; subsequent
operations reject changes to the specification, Property.toml, or Original.v.
Tool updates invalidate old batches but permit a new run with the same original. `sample` saves
only typed Input fields or `null`; the adapter is never run during generation.
The replay and debug commands consume the same saved Inputs independently.
Replay evidence includes adapter hashes and actual external calls. Debug
evidence contains specification bindings and no adapter hash. Both passes
record the exact instrumented AL's MD5 digest and reject a runtime digest
that differs from the compiled pass. Replay traces identify a failing premise
and its observed external dependencies; an independent unexpected premise
failure is reported as `execution_error`. Dependency traces preserve helper
control/status effects and distinguish each argument through mutual recursion.
Timeouts bound the entire Input execution, including adapter reads and writes.
Structured compile failures retain known variables, slot positions, source
locations, helper paths, and projection evidence. A fixed source
or observation contract change invalidates saved batch evidence. The demo
adapter returns `b=20`, so `x=7` produces `c=21` and a failed Goal; debug
computes `b=10`, `c=11`, and a passing Goal. These are finite execution
results, not proofs of generator or implementation correctness.

## Tool verification

```sh
bash environment/env.sh check
python3 -B -m scripts.property.rocq
python3 -B -m scripts.property.rocq --candidate-helper
python3 -B -m unittest discover -s scripts/tests -v
```

Run the environment check after changing the environment or the example. The
scripts are maintained verification infrastructure; run the regressions after
changing them.
`python3 -B translator/tests/check.py --suite all` compiles P4 and Wasm in
ignored evidence directories and checks that published specifications and
profiles stay unchanged. For a direct compilation without publication, use
`python3 scripts/translate.py --profile p4 --check --no-publish`.
