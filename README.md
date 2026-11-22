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
and their generated Coq specifications belong to this branch; properties and
external implementation adapters are separate experiments. Do not merge this
branch wholesale into `P4-spectec-based` or `pbt-experiments`.

## Repository layout and responsibilities

```text
environment/
  env.sh                     Setup, execution, and environment checks
  opam-switch.export         Pinned package versions, sources, and checksums
example.v                    Environment example: derived generator and sampling
specification/<spec-name>/
  Spec.v                     Public specification imports, published after check
  Generated/*.v              Generated types, calls, actions and Eval relations
translator/
  src/                       Typed AL lowering and Coq emission
  coq/                       Pure execution and builtin support
  profiles/                  Pinned inputs and validated builtin mappings
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

Users do not write candidates, proofs, or generators. An agent writes the
candidate reformulations and their equivalence proofs, and QuickChick derives
the generator and its correctness proof from the selected candidate.

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

`example.v` derives a generator for even natural numbers. The compatibility
examples in `environment/checks/` exercise generation, decision/enumeration,
merge, and the artifact's theorem-testing tactic. The tactic example aborts its
interactive theorem after testing; it does not provide a theorem proof.

`check` compiles copies of these files, requires a successful 10,000-sample
QuickChick result for each, and kernel-checks their compiled declarations with
`coqchk`. It writes a fresh `_opam-testing-theorems/checks/verification.*/`
directory and a log under `_opam-testing-theorems/logs/`, preserving previous
runs. Sampling checks do not prove generator soundness or completeness.
Generator proofs and property/QuickChick integration are outside the current
AL-to-Coq experiment scope. Predicate equivalence proofs still require closed
proofs without additional axioms or admissions.

The existing property scripts below are maintained separately and retain
legacy QuickChick proof-derivation assumptions; this environment migration does
not establish their compatibility with the artifact fork. Do not weaken them
to make an environment check pass.

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

# Generate, compile, then publish the verified source files
python3 scripts/translate.py --profile p4 --check
python3 scripts/translate.py --profile wasm --check

# Real Coq, frontend, lowering, builtin and complete-specification regressions
python3 translator/tests/check.py --suite all
```

Without `--inventory` or `--check`, the driver generates and audits all source
files but leaves `coq_compiled` and `translation_complete` false. A successful
`--check` requires every emitted Coq file to compile before it copies `Spec.v`
and `Generated/*.v` into `specification/<profile>/`. Existing managed files are
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
makes `translation_complete` true. Profile JSON files record the actual
validated AL signatures and concrete source/runtime binding locations.

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
Property/QuickChick integration, `Generator.v`, generator proofs, and the five
Derive-success experiment are outside this translation task. Predicate
equivalence proofs in the separate property workflow remain mandatory.

Implementation evidence is indexed in
`_opam-testing-theorems/logs/al-to-coq-final-report.json`; individual task and
suite/run reports preserve all intermediate results. Full-profile success is established by the corresponding
successful `--check` manifest, rather than by an inventory or helper test.

## Reformulate, check, run

1. Keep the specification and `Original.v` fixed. `Original.v` provides
   `Input : Type` and `predicate : Input -> Prop`; if the input condition
   involves several values, define `Input` as a record or a tuple.
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
4. `run.py --candidate vNNN` re-checks the chain up to `vNNN`, derives that
   candidate's generator and correctness proof using the legacy workflow, and
   transfers correctness to the original predicate through the chain. Later, incomplete candidates do
   not block the run. Unless `--derive-only` is given, it then samples the
   generator.

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

# Check the chain up to v002, then derive and verify only its generator
python3 scripts/run.py properties/<name> --candidate v002 --derive-only

# Perform the same verification for v001, then sample its generator
python3 scripts/run.py properties/<name> --candidate v001 --samples 100 --size 30 --seed 0
```

Each run is stored in a new directory under the property's `.runs/`, containing
source snapshots, the derived `Derived.v`, command logs with timings, and
`result.json`. Sampling also writes `samples.json`: each value is the string
rendered by `Show`, which requires a `Show Input` instance, and `null` records
that the generator returned no value, which is distinct from a property
counterexample. If the legacy extractor needs its integer type alias
workaround, it is applied identically to the `.ml` and `.mli` files, and the
unmodified files are kept.

Generator correctness may depend only on QuickChick's declared random-model
axioms. Authored sources may not contain execution commands, extraction
directives, load-path overrides, or directives that disable checking. A run
fails if any snapshotted source or tool changes while it is in progress, and
`--timeout` (default: 120 seconds) limits each subcommand. These checks are
intended for trusted local developments, not as a sandbox for malicious Coq
code, and they do not verify the extraction runtime that executes the
generator.

## Binding an implementation

This branch does not yet bind external implementations. `adapters/` is
reserved for adapters that pass generated inputs to an implementation and
report its outcome. Currently, `run.py` ends after sampling the derived
generator.

## Tool verification

```sh
bash environment/env.sh check
python3 -m unittest discover -s scripts/tests -v
```

Run the environment check after changing the environment or the example. The
scripts are maintained verification infrastructure; run the regressions after
changing them.
