# Predicate reformulation

Test external implementations against properties of a formal specification,
using input generators that QuickChick derives from Coq predicates together
with their correctness proofs. To obtain more efficient generators, an agent
rewrites the input condition of a property as a sequence of predicates, each
proved equivalent to its predecessor in Coq, and QuickChick derives the
generator from a selected predicate in the sequence.

## Branch responsibilities

`predicate-reformulation` is an independent branch. It contains the pinned
Coq/QuickChick environment and an environment example. It has no authored
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
specification/               Specifications under test
properties/                  Properties and their reformulations
adapters/                    Bindings to external implementations (reserved)
_opam-popl18/                Local opam switch and check logs (ignored)
```

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

The environment has been verified on Linux x86_64. It requires Git, opam,
make, `/usr/bin/gcc`, Perl, and network access. If opam has never been used on
the machine, run `opam init --bare --disable-shell-hook --yes` first.
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
