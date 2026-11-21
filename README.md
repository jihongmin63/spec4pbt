# Predicate reformulation

Test external implementations against properties of a formal specification,
using input generators that QuickChick derives from Coq predicates together
with their correctness proofs. To obtain more efficient generators, an agent
rewrites the input condition of a property as a sequence of predicates, each
proved equivalent to its predecessor in Coq, and QuickChick derives the
generator from a selected predicate in the sequence.

## Branch responsibilities

`predicate-reformulation` is an independent branch. It contains the pinned
Coq/QuickChick environment, an environment example, and the tools that check
reformulation sequences and derive generators. It has no authored
specifications, properties, or implementation adapters: `specification/`,
`properties/`, and `adapters/` contain only a `.gitkeep` file. Experiments
build on this branch. Do not merge it wholesale into `P4-spectec-based` or
`pbt-experiments`.

## Repository layout and responsibilities

```text
environment/
  env.sh                     Setup, execution, and environment checks
  opam-switch.export         Pinned package versions, sources, and checksums
example.v                    Environment example: derived generator and proof
specification/<spec-name>/
  Spec.v                     Specification definitions
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
  tests/                     Regressions that run the real Coq toolchain
_opam-popl18/                Local opam switch and check logs (ignored)
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
| Coq (former name of Rocq) | 8.6.1 |
| QuickChick | `popl-ifc-eval`, local package `0.0.0+popl2018` |
| OCaml | 4.05.0 |
| MathComp ssreflect | 1.6.4 |
| Camlp5 | 7.14 |
| ocamlbuild | 0.14.3 |
| ocamlfind | 1.9.6 |

The QuickChick source is pinned to commit
`f2b2fc64bd2ca81ef677d9bb6f36d8ee0adb6217` and used without modification. The
version `0.0.0+popl2018` is a local package name introduced for
reproducibility, not an official release number. This version was chosen over
the latest release because it automatically derives both generators and their
soundness and completeness proofs.

The environment has been verified on Linux x86_64. It requires Python 3, Git,
opam, make, `/usr/bin/gcc`, Perl, and network access. If opam has never been
used on the machine, run `opam init --bare --disable-shell-hook --yes` first.
Run all commands from the root of a checkout of this branch.

```sh
bash environment/env.sh setup                  # install or restore the environment
bash environment/env.sh check                  # check the environment with example.v
bash environment/env.sh coqtop                 # interactive Coq session
bash environment/env.sh coqc MyExperiment.v    # compile your own file
```

`setup` creates a dedicated opam switch in `_opam-popl18/` and can be rerun
safely; set build parallelism with `JOBS` (default: 8). It registers the
required repositories in the shared opam repository list, but does not change
other switches, the global switch, or the shell configuration. Legacy Coq and
OCaml packages come from the official opam archive repository. Because OCaml
4.05 predates the C23 default of recent GCC releases, the script generates a
GCC wrapper inside the installation that selects `-std=gnu11` and adds
`-Wno-implicit-function-declaration`.

## Environment check

`example.v` derives a generator and its correctness proof for the relation
`Even` on natural numbers. The correctness theorem states:

```text
Some n is a possible output of the generator  ↔  Even n
```

Soundness is the left-to-right direction, and completeness is the
right-to-left direction. A possible output is defined over all sizes and all
random seeds; the theorem does not claim that any finite run produces every
even number. Derivability must be confirmed separately for every other
predicate.

`check` performs the derivation, an execution test with 10,000 samples, and a
kernel check with `coqchk`. Each check writes its logs to a new directory
`_opam-popl18/checks/verification.*/` and never deletes earlier results.

`Print Assumptions` lists `RandomSeed`, `randomSplit`,
`randomSplitAssumption`, `randomSeed_inhabited`, `randomRNat`, and
`ramdomRNatCorrect` (spelled as in the upstream source). These are the axioms
by which QuickChick models random number generation. The example introduces no
`Admitted` proof and no new `Axiom`, and its correctness proof does not depend
on any unfinished upstream lemma.

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
   candidate's generator and correctness proof, and transfers correctness to
   the original predicate through the chain. Later, incomplete candidates do
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
