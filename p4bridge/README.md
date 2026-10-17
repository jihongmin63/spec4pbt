# Direct P4-SpecTec observation bridge

The semantic translator is the dev Docker donor's original executable, pinned
independently from the official P4-SpecTec specification submodule. This folder
contains dependency checks, a typed metadata helper, and a bundle orchestrator.
It contains no copied frontend, execution lowering, or Lean emitter for relation
semantics.

## Build and dependency provenance

```sh
scripts/bootstrap-p4-spectec
scripts/build-translator
python3 -m p4bridge.toolchain check
```

Bootstrap fetches the official [kaist-plrg/p4-spectec](https://github.com/kaist-plrg/p4-spectec)
submodule at `2730cfd9e74048bb5439da0f8afcef124079a064`. This commit is publicly
fetchable. `scripts/bootstrap-p4-spectec --source PATH` optionally uses a local
Git cache containing that commit.

The prebuilt Lean translator is separately pinned to Docker revision
`d150aa6e53e3f572bc4b02299c05d6d6cee9d6c0`. The official pin is its upstream base;
both have the identical `spec/` tree `8267673fcb54b5ee858fec6ac70104398312097e`.
The official repository has no `p4spec/lib/lean-skeleton` backend and cannot
supply the donor revision. A public submodule checkout therefore reproduces the
specification, while Lean regeneration still requires the dev Docker donor or
an equivalent prebuilt checkout of that exact revision.

`--donor-root` and `P4_SPECTEC_ROOT` select a prebuilt donor checkout; the default
is `/home/p4-spectec`. `--switch` defaults to `spectecx` because that installed
switch contains OCaml 5.1.1 and matches the Docker compiled libraries. The switch
named `default` in this image is different. The helper links the donor's
installed-build `p4spectec.pass` and `yojson` through `OCAMLPATH`. Source revision,
tracked cleanliness and the translator/helper fingerprints are checked before
generation. Changing the selected checkout requires rebuilding the metadata
helper. A prebuilt binary is trusted as a build of its matching clean checkout;
hashes identify it but are not a compiler proof.

`scripts/build-translator` compiles only the metadata helper against the donor's
existing executable and libraries. It does not build the Lean translator from
the official submodule. The required OCaml packages must already be installed
in the selected switch. The shared `/home/p4-spectec` source is not modified.

## Data flow

1. Run the original translator with source paths in caller order; directories
   are accepted by the donor and contain `.watsup` files.
2. Independently elaborate the same inputs with donor `Pass.elab`. Select the
   configured relations and read their authoritative input slots and types.
3. Emit a v1 observation manifest and a separate transport importing the untouched
   generated specification. Aliases provide ordinary Lean identifiers for source
   names and concrete compound types.
4. Compile the raw translation, transport and each typed observation view in an
   isolated staging project. Publish the complete fresh output directory only
   after all checks and input freshness checks succeed.
5. Use the existing observation/view/checker/runner tools with the **Transport**
   module as `--spec-module`.

`translation.json` records mode, source paths/hashes, config/model hash, donor
revision and executable hash, generated artifact hashes and donor diagnostics.
Its independent `p4_spectec` field records the official submodule URL and revision.
The actual checker certification additionally binds the generated Lean source
and compiled dependency closure. This does not prove that the OCaml translator
preserves every source execution.

Bundle publication uses Linux `renameat2(RENAME_NOREPLACE)`, including protection
against racing destinations. The supported dev environment is Linux. The output
must be a fresh directory inside the selected Lean project, with ordinary Lean
module path components. The `lean-toolchain` in that project selects Lean.

## Observation transport boundary

The bridge supports primitive types, closed records/variants and aliases,
lists/options/tuples, recursive data, and supported closed generic variant/alias
instantiations. Codecs are derived only for the dependency closure of inputs and
selected observation leaves. A hidden record field does not itself require a
JSON codec. The complete relation output remains present in `FullOutput` and is
existentially hidden by `Specification`.

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

## Explicit external type model

Actual full P4 has a `SpecTecExternTypes` class, including `json`, `archState` and
`objectState`. A concrete model is a user choice. Supply Lean declarations with
`--transport-model FILE`; they are inserted inside the generated transport
namespace after importing the raw specification, before deriving codecs/aliases.
For example, this test model chooses natural numbers for the donor class
fields (use the representations appropriate to the actual implementation):

```lean
@[reducible] local instance concrete : SpecTecExternTypes where
  json := Nat
  archState := Nat
  objectState := Nat
  decEqJson := inferInstance
  decEqArchState := inferInstance
  decEqObjectState := inferInstance

-- When archState is an input or a selected observation:
instance : Lean.ToJson SpecTec.archState :=
  inferInstanceAs (Lean.ToJson Nat)
instance : Lean.FromJson SpecTec.archState :=
  inferInstanceAs (Lean.FromJson Nat)
```

The class field names come from the donor translation. Definitional equality
with a concrete representation does not always make codec typeclass search
unfold the donor alias; forward the instances explicitly as above. If external types occur
in an input or selected observation, their representation must also supply the
necessary JSON instances. Donor data whose definitions depend on this class
require concrete codecs in the model; automatic deriving is reserved for data
without external class parameters. If they are hidden, no JSON codec is required for them.
The file is declaration text, not a module: it should not contain imports or
namespace-closing commands. Its bytes are included in the generated transport
and its hash is recorded. The model is trusted user-supplied Lean code subject
to the same later checker audit; no default type representation is silently used.

## Using the whole P4 specification

The original translator can still be called directly with all of its existing
options; its `--manifest` means a P4 case TSV, **not** an observation manifest.

```sh
/home/p4-spectec/_build/default/p4spec/lib/lean-skeleton/main.exe \
  external/p4-spectec/spec > /tmp/P4.lean

/home/p4-spectec/_build/default/p4spec/lib/lean-skeleton/main.exe \
  --emit-modules /tmp/P4Modules external/p4-spectec/spec
```

The default is ordered logical output. The original backend deliberately uses
noncomputable plans for large specifications because a single executable call
datatype can exceed native compiler limits. Observable property checkers do not
need an executable reference evaluator: they consume actual implementation
observations. `--executable` is available for specifications within donor limits.

The earlier Docker-era integration validation used `/home/p4-spectec/spec` and
translated the entire P4 specification without `--keep-going`: 11,087,987 bytes
in a monolith, or 446 modules. That input tree is identical to the official pin's
`spec/` tree used in the commands above. The only donor
warning was the clause-less `$sink`. Fresh Lean checks passed for Core, Support
and declarations 0000–0132 (135 modules); declaration 0133 exceeded the 120-second
per-module check limit. Entire-spec kernel validation is therefore not claimed.

Every standalone donor output embeds root runtime declarations and namespace
`SpecTec`. Combine source files in one translator invocation when they belong to
one specification. Do not import two independent donor outputs, or the legacy
copied `pbt.SpectecRuntime`, into the same Lean import closure. This integration
preserves donor semantics and limitations, including bugs that were separately
fixed while porting the other branch's backend; it does not patch the submodule.
