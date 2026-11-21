# Original Cedar premise validator

`validator.py` reads one JSON object per generated attempt:

```json
{"id": 17, "input_coq": "mkInput ...seven constructor fields..."}
```

Use `null` for `input_coq` when generation returns no input. The complete Coq
term must begin with `mkInput`, `Original.mkInput`, or
`Property.Original.mkInput`; it must use constructor applications, list and
tuple notation, strings, and numerals. The restricted grammar rejects Coq
commands, comments, tactic quotations, `let`, type annotations, and `::`.
Coq type checking confirms the seven field types and constructor arity. It is
not a general parser for arbitrary Coq expressions.

```sh
python3 scripts/cedar/validator.py \
  --input attempts.jsonl --output verdicts.jsonl \
  --evidence-dir properties/cedar_no_type_error/.runs/validator-evidence
```

`--env-script` can select an already installed, pinned `environment/env.sh`
when running from an isolated source copy. The default is this source tree's
script. The driver enforces Coq 8.20.0 and OCaml 4.14.2.

The output preserves row order and `id`. For each generated input it contains
the SHA-256 of the **exact complete input expression**, the five premise
verdicts (`valid`, `invalid`, or `unknown`), an aggregate verdict, and paths to
the source, logs, and Coq object that establish it. Duplicate expressions use
the same cached verdict and evidence. Cache identity includes the frozen
specification, Original predicate, Coq tactics, Python driver, environment
script, Coq version, and fixed bounds. Existing output files, failed logs,
and corrupt cache records are never overwritten. A null input has aggregate
`no_generation` and no premise verdicts. The aggregate is `valid` only when
all five are valid, `invalid` when any is disproved, and `unknown` otherwise.

For each premise `P`, the emitted Coq source defines a transparent value of
type `option ({P}+{~P})`. Bounded tactic search constructs `Some (left proof)`
for valid, `Some (right proof)` for invalid, or `None` for unknown. Its tag is
computed from that retained value. Each batch prints `Print Assumptions` for
every verdict, requires the closed global context, compiles with `coqc`, and
passes `coqchk` before a valid or invalid result is accepted. The fixed search
limit is depth 12, with one second for positive and one second for negative
search per premise. Batches contain at most 500 unique inputs and have a
1,200 second outer limit; an outer timeout marks its whole batch unknown.
The driver runs up to four independent batches at once by default. It assigns
each batch number before starting workers, keeps Coq sources and logs separate,
and writes cache entries and the final JSONL in input order after all workers
settle. `--batch-workers 1` enables serial comparison in regressions; the
selected worker count is part of the cache fingerprint and evidence manifest.
An exception cancels queued batches and waits for running batches to finish,
preserving their logs without publishing a partial output.

Proof search is incomplete: an `unknown` verdict neither establishes nor
refutes a premise. A Coq compile error aborts the run with its source and log
preserved; it never becomes `valid`. This validator does not prove generator
soundness or completeness. Its throughput at 50,000 attempts per target has
not yet been measured; runtime depends on the number and complexity of unique
expressions. Candidate predicates, Show output, and the Rust checker do not
affect these verdicts.
