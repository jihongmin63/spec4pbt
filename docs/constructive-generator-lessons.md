# Generator component plans and the Wasm fine graph

## Semantic contract and checking

Each component has exactly four semantic fields: `input`, `output`, `require`,
`ensure`. The named inputs and outputs are typed shared values. A value has one
producer and keeps one Lean binder across all uses. `require` may mention only
inputs; `ensure` may mention inputs and outputs. IDs, source locations,
projections, execution frames, and recursion descriptions are representation
metadata, not further semantic contract fields.

A connection names the producers whose `ensure` facts discharge a consumer's
`require`. The checker verifies producer coverage for every input and rejects
cycles. It elaborates and audits each implication in Lean:

```lean
∀ (all typed values), ensure_source₁ ∧ ... ∧ ensure_sourceₙ → require_target
```

A source can contribute to several consumers, and several sources can jointly
establish one requirement. Every component's requirement must be discharged,
including an initial producer's. The final audited theorem uses all component
ensures to establish the **original** `Contract.Premise` of the final value,
whose type must be exactly `Contract.Input`. The maintained property frontend
reparses the original `.watsup` property with the original catalog and
restriction, reconstructs the contract, and checks source and Lean module
fingerprints. The generated theorems go through the existing
`#spec4pbt_verify` proof audit. A missing proof, wrong type, `sorry`, forbidden
axiom, stale contract, or substituted premise fails. `plan-check` leaves
`emit/check/run` and certification behavior untouched. It imposes no new
soundness, completeness, or nonemptiness prerequisite on individual generators.

Schema 2 adds source correspondence and nested execution metadata. A call site
is checked against a pinned Lean declaration body: its bound call expression,
direct argument expressions, and result projections are checked. Projections
from a `Result` structure must name declared fields. A `condition` input is a
semantic prerequisite that is not claimed to be a direct source argument.
Schema 1 remains usable for contract-only plans; it rejects component source
claims because its symbol-and-hash reference cannot establish a call boundary.
Frames cover every node exactly once and pin their enclosing invocation. Loop
records pin an entry, base branch, step branch, and syntactically smaller Nat
predecessor or list tail. A typed recursive template has its own four-field
components, connection discharges, Lean-audited empty case and one-step
summary. The template's recursive call must match a loop's tail source site.
Source binding anchors also check the `prefixGen`, prelude, and final
generation result tuples, plus the recursive function-list cons. They record
where the same bound results are assembled.
The CLI shows nodes, edges, conditions, frames, loops, and templates with
source locations. Errors name the affected source declaration or graph node.

These checks establish a **conditional plan**, source-call shape, and premise
matching. They do not prove that a source generator satisfies a component's
`ensure`, that a projected source result has the planning type, or that the
recursive implementation obeys the template summary for all executions.
Source matching uses pinned file hashes and a conservative declaration/fragment
parser, not Lean elaboration of the original generator closure. Subtype `.val`
projections are checked as source shapes without re-elaborating their return
types. In particular,
`assembly.ensure` assumes `Nonempty (Validity.ModuleOkTrace module)`; the
checker proves that this full trace implies the exact original `Module_ok`
premise, while the implication from the source code to the trace remains an
implementation obligation. The reference generator has separate original
proofs, but this planning tool does not import or recertify them.

## Actual Wasm execution graph

The source is the implemented generator at commit
`33e314af20717d44709f5ad2c0862d6ec02d057b`. The former six-node example
confused enclosing calls with their children and is replaced by
[`component-plan.json`](../properties/wasm_module_ok/component-plan.json).
Its 18 main nodes and 52 dependency edges are:

| Execution frame | Nodes and actual source action |
| --- | --- |
| `prefix` | `types` via `ConstructiveTypes.fromEmpty`; `imports` from `ts.after`; `headers` from `is.after` and type metadata |
| `prelude_generate` | `bounded_context`; `tables` → `memories` → `globals` → `tags` → `elements` → `data` → `exports`, each from the prior result context |
| `prelude_projection` | `raw` assembles the ten section projections; `free` computes `moduleFree (raw p)`; `final_context` sets `REFS` from that same computed free summary |
| `generation` | `function_list` uses the shared header types and final context; `start` reuses that context; `assembly` replaces the raw module's `FUNCS` and `START` |
| `root` | `input_projection` maps the module syntax through `modules` and `Generator.generator` to the exact `Contract.Input` |

`Prelude.generate` invokes `prefixGen` internally and is only an enclosing
frame. It is not a second sampler. `finalContext` returns one context;
`free` is the expression computed within it, not a second return value.
`assembly` is the pure `module` projection of `Generation.Result`, and
`modules` maps that projection over `generate`. The source anchors reject
mapping `Prelude.generate` as a consumer of already sampled headers or
mapping `Generation.generate` directly as the final module projection.

The section stages conditionally preserve the same `REFS` identity through
the context chain. Each next stage requires the previous equality and its
producer's ensure discharges it; `final_context` requires the final data
context's equality. `raw` connects all syntax lists to the same module
fields. The final assembly requires every one of these raw field equalities,
so omitting a section fact breaks the Lean discharge. `function_list` uses
the shared header list and final context;
`start` uses that context again. Their facts join at `assembly`. The final
Lean theorem uses `Validity.module_ok_of_full_trace` to prove the exact
`SpecTec.«Module_ok»` premise, including every original free, context, section,
body, START, and export check in order. No observation catalog or premise was
weakened.

`FunctionList.generate` is a list recursion, not a fixed number of functions.
Its reusable `per_header` template has `signature`, `locals`, `body`, `finish`,
`recursive_tail`, and `cons` nodes. The empty case and the conditional
one-step equality of the generated `FTYPE` list to `head :: rest_headers` are
Lean-checked. The tail node is explicitly the inductive hypothesis and is
source-linked to `generate c env xs`; it is not a fresh independent sample.
Type, import, header, table, memory, global, tag, element, data, and export
generators are also potentially repeated; their 0/successor source shapes are
pinned by loop records. Exports follow `Prelude.exports` through
`ConstructiveExports.exports` to the unbounded `exactCount` recursion. The
instruction body generator's depth recursion is pinned as
an atomic leaf below `body`. Its many opcode productions, nested control
blocks, and completeness arguments are outside this planning graph; modelling
them would require a separate instruction-level graph, not a fixed list of
instructions.

## Reproducibility and limits

The original SpecTec source/property, frozen typed
[`Spec.lean`](../specifications/wasm/PlanReference/Spec.lean), reconstructed
[`Contract.lean`](../properties/wasm_module_ok/PlanReference/Contract.lean), and
[`Validity.lean`](../properties/wasm_module_ok/Validity.lean) are fingerprinted
in the plan. The source snapshots in
[`wasm_plan_reference`](../scripts/tests/fixtures/wasm_plan_reference/) are
byte-for-byte copies from the cited reference commit. The baseline translator
cannot emit the Wasm builtin `$lsl_`, so the frozen Lean translation is an
explicit dependency, not a fresh baseline translation. No original
implementation checkout, certificate, generated cache, or run trace is part
of this plan.

From the repository root:

```sh
python3 -m scripts.property plan-check \
  --plan properties/wasm_module_ok/component-plan.json --timeout 900 --format text
python3 -m unittest scripts.tests.test_component_plan scripts.tests.test_fine_component_plan -v
```

The analysis output begins and ends as follows (the command prints every
intermediate node, edge, condition, and loop):

```text
checked: 18 nodes, 52 edges; premise properties.wasm_module_ok.PlanReference.Contract.Premise; remaining require 0
execution frames:
  root: generation, input_projection
  generation: prelude_generate, prelude_projection, function_list, start, assembly
  prelude_generate: prefix, bounded_context, tables, memories, globals, tags, elements, data, exports
  prefix: types, imports, headers
  prelude_projection: raw, free, final_context
...
source result bindings:
  scripts/tests/fixtures/wasm_plan_reference/ConstructiveModuleGeneration.lean:generate / pure ⟨p,fs,s⟩
...
typed recursive templates:
  per_header -> function_list: recursive_tail, signature, locals, body, finish, cons; base and step checked
conditional contracts; generator implementations not certified
```

Implementation workflow: write typed values and four-field contracts; attach
source sites and pure projections; record nested frames and decreasing
recursive templates; connect facts with Lean discharge proofs; run
`plan-check --format text`; review any remaining implementation obligations
separately from planning. The present example meets the plan-to-premise check
and source-shape checks. It is not a new full-P4 certificate or a proof that
every declared component ensure follows from executable generator code.
