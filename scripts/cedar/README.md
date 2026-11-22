# Cedar experiment coordinator

`execute.py` runs the fixed three-run experiment after a scripted tool review.
It calls fresh `gpt-6-sol` roles through `roles.run_role` for the two authoring
roles only: the Reformulator and the Prover, both at `xhigh` effort.
Independent inspection is deterministic and lives in `inspection.py`; it is no
longer a model role. Its command is:

```sh
python3 scripts/cedar/execute.py \
  --experiment-id cedar-YYYYMMDD-unique \
  --tool-review properties/cedar_no_type_error/.runs/tool-review-unique/review.json
```

Create the tool review at the exact commit to be run, after the full tools and
tests are ready:

```sh
python3 -B scripts/cedar/inspection.py tool-review \
  --output-dir properties/cedar_no_type_error/.runs/tool-review-unique
```

The review runs every `scripts/tests/test_*.py` module with `python3 -B -m
unittest`, keeps the complete log, and writes `review.json`:

```json
{
  "kind": "scripted_tool_review",
  "status": "passed",
  "frozen": "the exact object returned by execute.frozen_manifest()",
  "tests_run": 0,
  "commands": [{"command": [], "returncode": 0, "log": "...", "log_sha256": "..."}]
}
```

`frozen` above stands for the JSON object, not a string. The coordinator
accepts the review only if it is property-local private evidence, its status
is `passed`, its regression run exited 0 with at least one test, its log is
unchanged, and `frozen` equals the current commit, source, tool, environment,
seed, size, and validator settings. A changed tool or source requires a new
review and experiment ID.

Each candidate that passes syntax, proof, and the whole-prefix audit is then
inspected by `inspection.inspect_candidate` before measurement. The inspection
is append-only evidence in `<attempt>/inspection/` and fails the proposal
(`inspection_failed`) unless every check passes:

1. `frozen_tools`: the frozen tool hashes still match.
2. `snapshot`: the staged `Original.v` matches the frozen source, each adopted
   `Candidate.v` and `Equivalence.v` is byte-identical to the run chain, the
   versions are the adopted ones followed by the new one, the new
   `Candidate.v` has the proved hash, and no extra file was staged.
3. `syntax`: `syntax.py` passes on a fresh copy that holds only `.v` sources.
4. `equivalence_chain`: `scripts/check.py` passes on that copy with an empty
   assumption audit and `coqchk`.
5. `derivation_probe`: `benchmark.py --test-mode --attempts 20 --seed 101`
   completes on that copy through the official scheduler, and the tactic's
   internal QuickChick result is `passed` or `gave_up`, never `failed`.
6. `sources_unchanged` and `tools_unchanged`: nothing changed while inspecting.

All Python subprocesses run with `-B` and `PYTHONDONTWRITEBYTECODE=1`, so the
inspection never leaves bytecode caches in the source tree. A report is
accepted only when it lists exactly these checks, all passed, with unchanged
command logs. An error that prevents inspection from running stops the run;
it is never recorded as a candidate verdict.

An experiment ID is never resumed or overwritten. Its private evidence is
`properties/cedar_no_type_error/.runs/EXPERIMENT_ID/`; its three versioned
property chains are
`properties/cedar_no_type_error/experiments/EXPERIMENT_ID/run-NNN/`. Each
chain begins with a byte-identical `Original.v`. Rejected attempts remain in
the private `.runs` staging directories and never enter a chain. Every role
invocation uses a fresh workspace, and no old worker session is resumed.

The coordinator measures P0 on seeds 101, 202, 303, 404, and 505 before any
proposal. Each run has at most ten proposals, including failed ones. The
Reformulator receives only its run's numeric evaluation, short failure
summaries, transformation identifiers, fixed source, and last adopted
predicate definitions. The Prover receives the frozen Candidate, predecessor
definitions, and exact `equivalent` theorem type. It receives no performance
feedback or Reformulator dialogue. Each proposed candidate passes syntax,
proof, whole-prefix Coq audit, and scripted independent inspection before five
benchmark and original-predicate validator batches. Adoption occurs only
after all five batches complete. The last adopted candidate remains the next
predecessor even if its measured ratio is worse.

Measurement runs the five fixed seeds concurrently, with each seed's
benchmark, validator output, command logs, and count record in its own evidence
paths. Each validator runs at most six independent Coq batches concurrently,
for a maximum of thirty active batch tasks across the five seeds. Seeds and
generated attempts retain their fixed order in returned results and JSONL.
The five seed workers and six validator batch workers are explicit frozen
conditions. A seed failure cancels queued work, waits for running work to
settle, and prevents adoption of a partial measurement; completed peers'
evidence remains available for audit. Runtime is operational only and is not
a research metric.

After all exploration runs stop, P0 and each run's last adopted candidate are
reevaluated on seeds 1101, 1202, 1303, 1404, and 1505. These results never
enter worker feedback. `summary.json` preserves seed and overall confirmed
valid ratios, comparisons with P0 and predecessor, per-attempt role wall time
and actual token usage, best versus last, proposal/adoption counts, and stop
reasons. Raw benchmark rows, validator verdicts, proof checks, role events,
and source snapshots stay in their evidence directories. An operational
failure writes `operational-failure.json` and a stopped summary. Interrupted
proposals count as rejected and retain available role cost; an uncalled Prover
is `not_run`. Incomplete batches never become completed measurements.

No research result is produced by this script's unit tests. Run them with
`python3 -m unittest scripts.tests.test_cedar_execute -v`; they replace model
and benchmark boundaries with controlled evidence to test the gates.
