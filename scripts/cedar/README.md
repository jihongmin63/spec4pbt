# Cedar experiment coordinator

`execute.py` runs the fixed three-run experiment after an independent tool
inspection. It calls fresh `gpt-6-sol` roles through `roles.run_role`; the
Reformulator and Prover use `xhigh` effort and the Inspector uses `high`.
Its command is:

```sh
python3 scripts/cedar/execute.py \
  --experiment-id cedar-YYYYMMDD-unique \
  --tool-review properties/cedar_no_type_error/.runs/tool-review-unique/review.json
```

The tool review is an actual fresh Inspector call, completed before the
experimental baseline. The Inspector's input bundle contains the exact files
listed by `execute.SOURCE_FILES + execute.tool_files(execute.ROOT)`, including
the fixed experiment prompt, authored scripts, regression tests, and tool
documents. Its context is
`{"frozen": execute.frozen_manifest(), "purpose": "independent_tool_review"}`.
It checks the complete source and tools by running its own commands from
copies under its `scratch/` directory. The review envelope has only the
following fields:

```sh
python3 - <<'PY'
from pathlib import Path
from scripts.cedar import execute, roles

root = execute.ROOT
review_dir = execute.PROPERTY / ".runs" / "tool-review-UNIQUE"
review_dir.mkdir(parents=True, exist_ok=False)
frozen = execute.frozen_manifest(root)
inputs = {name: root / name
          for name in execute.SOURCE_FILES + execute.tool_files(root)}
result = roles.run_role(
    "inspector", root, review_dir, inputs,
    {"frozen": frozen, "purpose": "independent_tool_review"},
    forbidden_paths=[], switch=execute.SWITCH)
if result["status"] != "accepted" or result["answer"]["status"] != "passed":
    raise SystemExit("tool review failed; inspect its private evidence")
execute.write_new(review_dir / "review.json", {
    "frozen": frozen,
    "inspector_result": str(Path(result["manifest"]["evidence"]) / "result.json")})
print(review_dir / "review.json")
PY
```

Use a unique review directory and run this only after the full tools and tests
are ready. It is an actual fresh Inspector call and may consume model tokens.
The Inspector must run checks on scratch copies, leaving its bundled source
unchanged. The resulting JSON has this shape:

```json
{
  "frozen": "the exact object returned by execute.frozen_manifest()",
  "inspector_result": "/absolute/property-local/.runs/path/to/private-evidence/result.json"
}
```

`frozen` above stands for the JSON object, not a string. The result must be an
accepted `inspector` role with a `passed` answer, raw role events, commands,
and evidence paths in its own scratch area. The coordinator checks the
Inspector's input and context hashes, model and effort, and the frozen commit,
source, tool, environment, seed, size, and validator settings. A changed tool
or source requires a new review and experiment ID. A review envelope alone
cannot claim that an inspection passed.

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
proof, whole-prefix Coq audit, and fresh independent inspection before five
benchmark and original-predicate validator batches. Adoption occurs only
after all five batches complete. The last adopted candidate remains the next
predecessor even if its measured ratio is worse.

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
