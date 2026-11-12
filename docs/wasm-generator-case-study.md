# Haskell generator toward the pinned Wasm `Module_ok`

## Constructive domain and remaining distance

The actual `experiments/generator-haskell/src/WasmGenerator.hs` now builds typed stack programs, with independent type/function/export counts and configurable parameter, result, and local counts. It constructs candidates without invoking or filtering through the validator. The ultimate target remains the pinned `Module_ok`; this implementation is still an intermediate restriction, with concrete full-target counterexamples below. No soundness, completeness, or translation-preservation theorem has been attempted.

The independently described intermediate domain is:

- Arbitrary finite lists of singleton, final, supertype-free i32 function-type recursion groups. Function parameter/result lists may be empty or contain multiple i32s. Types may be duplicated, unused, or shared by functions; type indices and list order are preserved.
- Arbitrary finite functions with valid type indices and initialized i32 locals. Parameters precede declared locals in local-index space; function bodies start with an empty operand stack and finish at the declared result count. Bodies are ordinary stack-typed sequences of constants in `0..4294967295`, local.get/set/tee, nop/drop, i32 add/sub/mul, direct calls, block, loop, and if. Every instruction consumes its required stack inputs. Structured bodies use their declared input/output stacks and cannot consume the surrounding stack prefix. Both inline block types (empty or i32) and indexed function block types are distinct supported AST forms. Unreachable-stack polymorphism and branches are excluded.
- Function exports have arbitrary target order, aliases, and count, including zero. Export position `i` has the unique ASCII name `f` followed by decimal `i`; names beyond `f9` are encoded correctly. An optional start names a `[] -> []` function. Empty modules and type-only modules are included. All other sections are empty.

This grammar is defined by syntax, contexts and stack effects, not by the generator's image. There is no fixed 0/1/2-arity split, six-function saturation, or depth-four saturation. The complete function context is available before bodies, so forward, self, and mutual calls are available. Generation fuel does **not** bound execution of generated Wasm: calls can recurse indefinitely. These tests validate modules; they do not execute Wasm bodies.

Full `Module_ok` still includes imports, globals, tables, memories, tags, data/elements, general names, recursive/subtyping type groups, other value types, references/GC, exceptions, branches, unreachable and many other instructions. Even this numeric AST differs from the usual binary intuition: pinned `i32` is `nat`, and `Instr_ok/const` does not enforce a 32-bit range. The unchanged oracle accepts an i32 constant **4294967296**, an empty export name, and an i64-result function, all outside current support. These three explicit counterexamples are saved in `build/wasm/haskell-generality/known-exclusions.jsonl`. Further AST, context and section expansion is necessary; the research goal of full-specification completeness remains unfinished.

## Executable interfaces and support

```haskell
data Config = Config
  { maxTypes, maxFunctions, maxParameters, maxResults,
    maxLocals, maxExports, instructionBudget :: Int }
data ChoiceSource = Seeded Word64 | Replay [Int]
generateModule :: Config -> ChoiceSource -> Either GenError (WasmModule, ChoiceSource)
generateSample :: Int -> Config -> Word64 -> Either GenError WasmModule
replayModule :: Config -> [Int] -> Either GenError WasmModule
```

All maxima are inclusive and independently configured. If no type exists, the only function count is zero; with no functions, exports and start are absent. Structural counts use explicit list fuel. Instruction generation tracks the available local count, complete function/type contexts, current stack height and requested result height. It chooses only applicable instructions. Children and following instructions share one decreasing decision budget per function. A stop decision consumes one unit. At stop or fuel zero, the defined base construction drops surplus values or appends zero constants to obtain the requested result height. It makes no further choices. This may emit more instructions than the decision budget; the budget is neither an exact AST size nor an execution-step bound. Shared accounting prevents exponential copying of a depth allowance across branches.

Both choice sources execute the **same translated AST-building code**. A seeded request uses existing SplitMix64 modulo selection; sample `i` starts from wrapping `seed + i`. Replay consumes one integer for each exclusive-bound request, including bound one. Exhaustion and negative/out-of-range choices return specific errors; no modulo reduction, resampling, or seeded recovery occurs. Successful `replayModule` requires an empty remainder; any unused suffix is an error. The lower-level `generateModule` explicitly returns the remainder for composition. Native tape files contain whitespace-separated signed decimal Int values; malformed or overflowing tokens fail before core execution.

For a fixed configuration, support means successful outputs of the actual translated entry point over its specified inputs. Seeded support ranges over `Word64`; replay support ranges over finite Int tapes. These are different executable interfaces: finite seed sampling does not establish arbitrary independent choice reachability. Their unions across configurations also differ from fixed-configuration support and from any finite test corpus. For example, a zero-budget one-result function can only obtain its result from the zero-constant base construction. A potential witness construction for longer target bodies would select their instructions and explicit stops with a sufficient shared budget; this has not been proved. A fixed-fuel target needs its own independently stated instruction/sequence bounds, accounting for stops and base construction, before asserting equality with support.

The native platform uses signed 64-bit `Int`. Core configuration validation uses `Integer` arithmetic before allocation to reject negative fields and unsafe count, candidate-list and stack-height arithmetic. These are representational restrictions, not an unbounded-natural interface. The grammar above allows arbitrary finite lengths, so sizes beyond representable configurations remain additional counterexamples to an unrestricted size claim. Rocq's `Z` representation does not remove that native restriction. Successful finite replay comparisons do not establish coverage of even all representable target bodies.

The CLI retains `COUNT SIZE SEED`, with `sizeConfig SIZE` setting all seven fields to SIZE, including zero. It also exposes:

```text
wasm-sample sample COUNT SEED TYPES FUNCS PARAMS RESULTS LOCALS EXPORTS FUEL
wasm-sample replay TYPES FUNCS PARAMS RESULTS LOCALS EXPORTS FUEL TAPE_FILE
```

Seeds accept `0..2^64-1`. CLI safety policy explicitly rejects COUNT outside `1..1000000`, structural fields outside `0..1000000`, fuel above 512, and batches exceeding the conservative 10,000,000 allocation estimate in `checkResources`. It never silently clamps configuration. These execution-policy limits are separate from core arithmetic checks: a completeness statement for unrestricted core replay would not automatically describe CLI support, which still excludes, for example, arbitrarily deep bodies. Physical memory/time limits impose further finite execution boundaries.

## Reproduction and finite evidence

From the repository root with installed pinned toolchains and cached dependencies:

```sh
PYTHONPATH=. python3 experiments/generator-haskell/run-wasm-case-study.py
```

The runner locks heavy subprocesses individually with `/tmp/spec4pbt-wasm-build.lock`; do not wrap it in another flock. It sets single-process/thread resource variables, bounds the GHC compiler heap, and uses command timeouts. It builds the native binary, translates the actual core and error paths, compiles the **unedited tool-generated** `build/generator-haskell/translated/WasmGenerator.v`, and invokes the unchanged SpecTec AL `Module_ok` oracle. No production translator, pinned specification/catalog, or common oracle changes are required.

Evidence is stored in `build/wasm/haskell-generality/`: exact replay tapes, whole-module JSONL, negative and excluded-target inputs, `CompleteOutputs.v`, per-command logs/timings and `result.json`. The corpus contains 108 shorthand seeded modules (sizes 0, 1, 2, 4, 8, 13; six seeds including the Word64 endpoints; three samples each), three independently configured seeded modules, and ten hand-authored replay witnesses checked against independently authored whole-module ASTs. Replay covers eight functions, four-argument calls, five locals, shared/unused/duplicate types, zero/multiple results, start, aliased/reordered exports including `f10`, full u32 boundaries, parameterized multivalue block/if, loop, eight nested blocks, 64 sequential instructions, and shared-budget exhaustion.

The final run passed **121/121 `Module_ok` generated-module checks and 121/121 complete native/Rocq output equalities** (61 distinct modules). Thirteen final invalid mutations were rejected, including the original seven negative cases, valid-callee argument underflow, local.set underflow and indexed-block failures; the reviewed corpus is saved in `negative-final.jsonl`. Nine native/Rocq error checks cover tape exhaustion/range/unused suffix, Int endpoints and invalid/overflowing configurations; seven additional CLI parsing/resource checks reject invalid requests. Four translated entry points report closed assumptions. The three full-target counterexamples above are separately accepted by the oracle and are not counted as generated outputs. Existing native Haskell compatibility, translated toy-generator comparisons and unchanged oracle regressions also pass. Repeated empty modules and overlapping seeded samples reduce distinct output count; these results are finite evidence, not coverage theorems.

## Translation and future obligations

`wasm.edits` only supplies library/name mappings and inlines `continueCode` so the generated `generateCode` fixpoint recurses structurally on list fuel. Safe explicit indexing returns `InvalidIndex`; no default signature is used to recover from invalid indices. `Integer` maps to the installed `GHC.Num.Integer` (`Z`). Existing `SequenceOps.replicate -> SequenceBridge.replicate` and wrapping `Word64Bridge` mappings remain. Generated code has no admitted proofs, axioms, deferred fixes, or disabled guard checking. Rocq constructor renames avoid source type/constructor name collisions.

The CLI, `WasmJson.hs`, inverse comparison codec, native SpecTec interpreter, GHC/Rocq libraries, hs-to-rocq and library bridges remain trusted execution boundaries. Complete finite AST comparisons check exact section contents, subtype/group structure, block-type variants, indices, names and starts through the codec; they do not prove serialization, source translation or bridge correspondence.

Future obligations are typed-context/stack preservation for each instruction, module/type/start/export validity, budget and machine-arithmetic invariants, exact source-AST embedding into pinned Wasm, and native/Rocq/bridge correspondence. Completeness additionally needs constructive witnesses for the independently defined target in the **actual replay program**, explicit fixed-config versus union quantifiers, input-range and resource assumptions, and a separate account of seed-only support. Extending toward full `Module_ok` requires resolving the exhibited counterexamples and omitted features; narrowing a theorem to this intermediate grammar would not complete that ultimate task.
