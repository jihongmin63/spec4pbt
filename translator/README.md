# SpecTec-to-Lean toolchain

This package contains the semantic translator and the native observation/property
integration. The official frontend and interpreter libraries come from the
[P4-SpecTec submodule](../p4-spectec); builds leave that source unchanged.

| Location | Responsibility |
| --- | --- |
| `src/` | Imported OCaml Lean backend and embedded Lean execution libraries. |
| `bridge/metadata.ml` | Typed relation metadata and JSON transport generation. |
| `bridge/property_cli.ml`, `bridge/property_al.ml` | Typed native property frontend and normalized AL metadata. |
| `bridge/property_exec.ml` | Native AL execution with saved external observations. |
| `toolchain.py` | Build identity, source fingerprints and native translation CLI. |
| `patches/` | Local frontend and property-executor extensions. |
| `tests/` | Unchanged imported backend regressions; maintained tests live in `../tests/`. |

The backend's original [README](src/README.md) describes its semantics and flags;
use `python3 -m translator.toolchain translate` in place of its original executable paths.
[PROVENANCE.md](PROVENANCE.md) records the imported source and license.

## Build and dependency provenance

After installing the OCaml dependencies described in the [root README](../README.md):

```sh
python3 -m translator.toolchain bootstrap
python3 -m translator.toolchain build --switch spec4pbt
python3 -m translator.toolchain check
```

Bootstrap fetches the official [kaist-plrg/p4-spectec](https://github.com/kaist-plrg/p4-spectec)
submodule at `2730cfd9e74048bb5439da0f8afcef124079a064`. An optional
`--source PATH` uses a local Git cache containing that public commit.

The backend was imported from `d150aa6e53e3f572bc4b02299c05d6d6cee9d6c0` and is
now tracked under `translator/src/`. Its original revision is provenance; current
source hashes identify the code being built. The official pin is that revision's
upstream base, with an identical P4 specification tree. The tracked compatibility
patch exposes the backend's per-definition AL conversion helper.

`python3 -m translator.toolchain build` exports the clean official Git revision into
`out/translator/p4-spectec`, applies the compatibility patch there, and adds
the tracked backend and metadata helper. Dune compiles the translator, metadata helper, property frontend and AL
executor against the same frontend libraries. The submodule is never patched.
The build requires no external checkout, donor executable, or installed copy of
the P4-SpecTec libraries. `--switch NAME` selects an opam switch; a build without
that option uses the active switch. Translation uses the switch recorded at build
time, without selecting a Docker installation.

The build identity records the official revision, backend origin, current source
hashes, selected switch, and native executable hashes. Missing or stale builds are
rejected with a rebuild instruction. Each build reconstructs the workspace from
source, so manual changes to the ignored workspace are not a maintained patch.
The runtime checks identify inputs and binaries; they do not prove compiler
correctness.

## Property integration

`python3 -m translator.toolchain translate` forwards native options and exit status
unchanged. Typed property planning, transport/contract generation, Lean proof
certification, execution, and replay are provided by `python3 -m pbt.property`.
See the [root workflow](../README.md). Generated bundles are fixed at
`out/bundles/<property>/`; build refuses an existing output directory. Sources,
toolchain, proof dependencies, and generated artifacts are fingerprinted.

## Observation transport boundary

For native property clauses, the bridge relation manifest supplies input slots
and types, while observation metadata supplies external selectors. Execution
adapters are bound later through an implementation TOML; see the
[native property workflow](../README.md).

The bridge supports primitive types, closed records/variants and aliases,
lists/options/tuples, recursive data, and supported closed generic variant/alias
instantiations. Codecs are derived only for the dependency closure of inputs and
selected observation leaves. A hidden record field does not itself require a
JSON codec. The property contract retains internal witnesses and the original
conditions in its premise; execution uses only the configured external observations.

Manifest v1 adds `kind: "opaque"` for types selected as whole values (such as a
list or tuple). It does not permit field selectors on opaque values. Record field
selectors retain source field names, with the donor's Lean field spelling.
`%0` cannot select an input slot; duplicate/overlapping selections, unknown
relations/fields, malformed config and wrong schema versions fail explicitly.

Polymorphic records, nonuniform recursive transport, function-valued transport,
and unrepresentable field names are rejected. The metadata graph has a 4096-type
limit. JSON derivation must succeed in Lean, including dependencies; no codec or
semantics is replaced by an axiom. This boundary is distinct from the original
translator's larger language support.

## External types

In the default ordered mode, every `extern syntax` declaration becomes a
distinct Lean inductive type with one nullary constructor:

```lean
inductive archState : Type where
  | mk : archState
deriving DecidableEq
```

This is a deliberate singleton model: every value of `archState` equals
`archState.mk`. Each external type has its own constructor and remains distinct
from other external types. The names are taken from the specification, without
the old restriction to `json`, `archState`, and `objectState`. No external-type
class, user axiom, or concrete type model is required. Extern relations keep their
unconditional `allowed` constructors over these types. The singleton model does
not express differences between external states or establish full-P4 correctness.

The metadata helper derives JSON codecs for the input and selected observation
dependency closure, including external types and records that contain them.
The singleton's JSON encoding is the string `"mk"`; other values are rejected.
Hidden fields still do not require codecs. Native AL execution retains its
existing supported value subset; deriving a Lean codec does not add support
for an opaque value in that executor.

`--transport-model FILE` remains an optional hook for extra Lean declarations
inside the transport namespace, after importing the raw specification. It cannot
replace the generated types. The file contains declarations, not imports or
namespace-closing commands. Its bytes and hash are recorded, and its declarations
remain subject to the checker audit. Old `SpecTecExternTypes` instance files are
not compatible with ordered output and must no longer be supplied.

The legacy `--relation-semantics declarative` mode retains the imported backend's
external-type class and validity models. Property bundles always use ordered mode.
The local change is applied by `patches/extern-singleton.patch` to the build copy;
the imported source and its checksums remain unchanged.

## Using the whole P4 specification

The original translator can still be called directly with all of its existing
options; its `--manifest` means a P4 case TSV, **not** an observation manifest.

```sh
python3 -m translator.toolchain translate \
  p4-spectec/spec > /tmp/P4.lean

python3 -m translator.toolchain translate \
  --emit-modules /tmp/P4Modules p4-spectec/spec
```

The default is ordered logical output. The original backend deliberately uses
noncomputable plans for large specifications because a single executable call
datatype can exceed native compiler limits. Observable property checkers do not
need an executable reference evaluator: they consume actual implementation
observations. `--executable` is available for specifications within donor limits.

The earlier integration validation translated the entire P4 specification without `--keep-going`: 11,087,987 bytes
in a monolith, or 446 modules. That input tree is identical to the official pin's
`spec/` tree used in the commands above. The only donor
warning was the clause-less `$sink`. Fresh Lean checks passed for Core, Support
and declarations 0000–0132 (135 modules); declaration 0133 exceeded the 120-second
per-module check limit. Entire-spec kernel validation is therefore not claimed.

Every standalone donor output embeds root runtime declarations and namespace
`SpecTec`. Combine source files in one translator invocation when they belong to
one specification. Do not import two independent donor outputs into the same
Lean import closure. This integration
preserves donor limitations, including bugs that were separately fixed while
porting the other branch's backend. Ordered external types use the singleton
model described above; the official submodule is not patched.

## Verification

From the repository root:

```sh
python3 -m unittest discover -s tests -t . -v
export ELAN_TOOLCHAIN="$(cat lean-toolchain)"
python3 translator/tests/check_direct_relations.py \
  --exe out/translator/p4-spectec/_build/default/p4spec/lib/lean-skeleton/main.exe
```

From `translator/`, `sha256sum --check SHA256SUMS` verifies the unchanged imported
backend and original regression files. Maintained integration tests and fixtures live in root `tests/`.
The archived ordered/case suites in `translator/tests/` describe the donor's
class-based external model; their old instance proofs are not the singleton
regressions. Current singleton tests live in `tests/test_metadata.py` and
`tests/test_property_clause_examples.py`.
