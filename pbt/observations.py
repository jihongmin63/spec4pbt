"""Validate observation sidecars and publish kernel-checked typed Lean views."""

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import tomllib

from pbt.lean_tools import elaborate, rebuild_modules, require_timeout, run_checked


# This deliberately supports the ordinary ASCII subset emitted by the translator.
# Quoting each validated component below also prevents keyword/namespace shadowing.
_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
_RESERVED = set("_ axiom abbrev by check class def deriving do else end example export false for forall fun if import in inductive instance let macro match mutual namespace noncomputable notation opaque open partial private protected section set_option structure syntax theorem then true universe unsafe variable where with Type Prop Sort".split())
_SELECTOR = re.compile(r"%(0|[1-9][0-9]*)(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


def _name(value, source, *, dotted=True):
    if not isinstance(value, str) or not value:
        raise ValueError(f"{source}: expected a Lean identifier")
    parts = value.split(".") if dotted else [value]
    if any(_IDENTIFIER.fullmatch(part) is None or part in _RESERVED for part in parts):
        raise ValueError(f"{source}: invalid Lean identifier {value!r}")
    return value


def _lean(value):
    return ".".join("«" + part + "»" for part in value.split("."))


def _reference(value):
    return "_root_." + _lean(value)


def _object(value, required, source):
    if not isinstance(value, dict):
        raise ValueError(f"{source}: expected a table/object")
    missing, extra = set(required) - value.keys(), value.keys() - set(required)
    if missing:
        raise ValueError(f"{source}: missing fields {sorted(missing)}")
    if extra:
        raise ValueError(f"{source}: unknown fields {sorted(extra)}")
    return value


def _text(value, source):
    if not isinstance(value, str) or not value:
        raise ValueError(f"{source}: expected a nonempty string")
    return value


def _version(value, source):
    if type(value) is not int or value != 1:
        raise ValueError(f"{source}: unsupported schema_version {value!r}; expected 1")


def _resolve_alias(types, key, source="manifest"):
    seen = set()
    while types[key]["kind"] == "alias":
        if key in seen:
            raise ValueError(f"{source}: alias type cycle involving {key!r}")
        seen.add(key)
        key = types[key]["type"]
    return key


def validate_manifest(value, source="manifest"):
    """Check the complete v1 manifest, including entries unused by this view."""
    _object(value, ("schema_version", "namespace", "types", "relations"), source)
    _version(value["schema_version"], source)
    _name(value["namespace"], source + ".namespace")
    types = value["types"]
    relations = value["relations"]
    if not isinstance(types, dict) or not isinstance(relations, dict):
        raise ValueError(f"{source}: types and relations must be objects")
    for key, item in types.items():
        context = f"{source}.types[{key!r}]"
        _text(key, context)
        if not isinstance(item, dict):
            raise ValueError(f"{context}: expected an object")
        kind = item.get("kind")
        if kind not in ("primitive", "variant", "record", "alias", "opaque"):
            raise ValueError(f"{context}: unsupported type kind {kind!r}")
        required = ("kind", "lean")
        if kind == "record":
            required += ("fields",)
        elif kind == "alias":
            required += ("type",)
        _object(item, required, context)
        _name(item["lean"], context + ".lean")
        if kind == "alias":
            _text(item["type"], context + ".type")
            if item["type"] not in types:
                raise ValueError(f"{context}: unknown type {item['type']!r}")
        if kind == "record":
            if not isinstance(item["fields"], dict):
                raise ValueError(f"{context}.fields: expected an object")
            lean_fields = set()
            for field, data in item["fields"].items():
                field_context = f"{context}.fields[{field!r}]"
                _text(field, field_context)
                _object(data, ("type", "lean"), field_context)
                _text(data["type"], field_context + ".type")
                _name(data["lean"], field_context + ".lean", dotted=False)
                if data["type"] not in types:
                    raise ValueError(f"{field_context}: unknown type {data['type']!r}")
                if data["lean"] in lean_fields:
                    raise ValueError(f"{field_context}: duplicate Lean field name {data['lean']!r}")
                lean_fields.add(data["lean"])
    for key in types:
        _resolve_alias(types, key, source)
    for key, item in relations.items():
        context = f"{source}.relations[{key!r}]"
        _text(key, context)
        _object(item, ("lean", "inputs", "arguments"), context)
        _name(item["lean"], context + ".lean")
        arguments, inputs = item["arguments"], item["inputs"]
        if not isinstance(arguments, list) or not isinstance(inputs, list):
            raise ValueError(f"{context}: inputs and arguments must be arrays")
        for index, argument in enumerate(arguments):
            _object(argument, ("type",), f"{context}.arguments[{index}]")
            _text(argument["type"], context + ".type")
            if argument["type"] not in types:
                raise ValueError(f"{context}.arguments[{index}]: unknown type {argument['type']!r}")
        if any(type(index) is not int or not 0 <= index < len(arguments) for index in inputs):
            raise ValueError(f"{context}.inputs: each input must be an in-range integer slot")
        if len(set(inputs)) != len(inputs):
            raise ValueError(f"{context}.inputs: duplicate input slot")
    return value


def _json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON field {key!r}")
        result[key] = value
    return result


def load_manifest(path):
    path = Path(path)
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_json_object)
    except (ValueError, UnicodeError) as error:
        raise ValueError(f"{path}: {error}") from error
    return validate_manifest(value, str(path))


def load_config(path):
    path = Path(path)
    try:
        with path.open("rb") as stream:
            return tomllib.load(stream)
    except (ValueError, UnicodeError) as error:
        raise ValueError(f"{path}: {error}") from error


@dataclass(frozen=True)
class Selector:
    slot: int
    fields: tuple[str, ...]
    lean_fields: tuple[str, ...]
    type_key: str


@dataclass(frozen=True)
class Observation:
    id: str
    relation: str
    selectors: tuple[Selector, ...]
    config: dict


def validate_observation(value, observation_id, manifest, source="config"):
    """Resolve selected fields against output slots without changing relation roles."""
    validate_manifest(manifest)
    _object(value, ("schema_version", "observations"), source)
    _version(value["schema_version"], source)
    entries = value["observations"]
    if not isinstance(entries, list):
        raise ValueError(f"{source}.observations: expected an array")
    seen = set()
    selected = None
    # Validate every sidecar entry so typos cannot hide in unselected profiles.
    for index, entry in enumerate(entries):
        context = f"{source}.observations[{index}]"
        _object(entry, ("id", "relation", "observe"), context)
        identity = _text(entry["id"], context + ".id")
        if identity in seen:
            raise ValueError(f"{context}: duplicate observation id {identity!r}")
        seen.add(identity)
        relation_name = _text(entry["relation"], context + ".relation")
        if relation_name not in manifest["relations"]:
            raise ValueError(f"{context}: unknown relation {relation_name!r}")
        relation = manifest["relations"][relation_name]
        observed = entry["observe"]
        if not isinstance(observed, list):
            raise ValueError(f"{context}.observe: expected an observation selector array")
        selectors = []
        for raw in observed:
            selector_context = f"{context}.observe[{raw!r}]"
            if not isinstance(raw, str) or _SELECTOR.fullmatch(raw) is None:
                raise ValueError(f"{selector_context}: invalid selector")
            head, *fields = raw.split(".")
            if len(head) - 1 > len(str(len(relation["arguments"]))):
                raise ValueError(f"{selector_context}: slot out of range")
            slot = int(head[1:])
            if slot >= len(relation["arguments"]):
                raise ValueError(f"{selector_context}: slot out of range")
            if slot in relation["inputs"]:
                raise ValueError(f"{selector_context}: cannot observe an input slot")
            for previous in selectors:
                common = min(len(previous.fields), len(fields))
                if previous.slot == slot and previous.fields[:common] == tuple(fields[:common]):
                    raise ValueError(f"{selector_context}: duplicate/overlapping selectors")
            type_key = relation["arguments"][slot]["type"]
            lean_fields = []
            for field in fields:
                item = manifest["types"][_resolve_alias(manifest["types"], type_key)]
                if item["kind"] != "record":
                    raise ValueError(f"{selector_context}: field selector requires a record type")
                if field not in item["fields"]:
                    raise ValueError(f"{selector_context}: unknown field {field!r}")
                data = item["fields"][field]
                type_key = data["type"]
                lean_fields.append(data["lean"])
            selectors.append(Selector(slot, tuple(fields), tuple(lean_fields), type_key))
        if identity == observation_id:
            selected = Observation(identity, relation_name, tuple(selectors), dict(entry))
    if selected is None:
        raise ValueError(f"{source}: missing observation {observation_id!r}")
    return selected


def load_observation(path, observation_id, manifest):
    return validate_observation(load_config(path), observation_id, manifest, str(path))


def _product(expressions):
    if not expressions:
        return "Unit"
    if len(expressions) == 1:
        return expressions[0]
    return f"({expressions[0]} × {_product(expressions[1:])})"


def _tuple(expressions):
    if not expressions:
        return "()"
    if len(expressions) == 1:
        return expressions[0]
    return f"({expressions[0]}, {_tuple(expressions[1:])})"


def _component(name, index, count):
    if count == 1:
        return name
    if index == 0:
        return f"({name}).1"
    return _component(f"({name}).2", index - 1, count - 1)


def render_view(manifest, observation, spec_module, namespace, profile_id):
    """Render the selected existential relation and its executable output projection."""
    validate_manifest(manifest)
    validated = validate_observation(
        {"schema_version": 1, "observations": [observation.config]}, observation.id, manifest)
    if observation != validated:
        raise ValueError("Observation selector objects disagree with their validated configuration")
    _name(spec_module, "spec module")
    _name(namespace, "view namespace")
    if re.fullmatch(r"[0-9a-f]{64}", profile_id) is None:
        raise ValueError("profile_id must be a SHA-256 hexadecimal digest")
    relation = manifest["relations"][observation.relation]
    arguments = relation["arguments"]
    # Roles are a set; tuple ordering always follows the original relation order.
    inputs = [index for index in range(len(arguments)) if index in relation["inputs"]]
    outputs = [index for index in range(len(arguments)) if index not in relation["inputs"]]
    type_of = lambda key: _reference(manifest["types"][key]["lean"])
    input_type = _product([type_of(arguments[index]["type"]) for index in inputs])
    output_type = _product([type_of(arguments[index]["type"]) for index in outputs])
    observation_type = _product([type_of(item.type_key) for item in observation.selectors])
    projected = []
    for item in observation.selectors:
        expression = _component("full", outputs.index(item.slot), len(outputs))
        for field in item.lean_fields:
            expression = f"({expression}).{_lean(field)}"
        projected.append(expression)
    relation_args = []
    for index in range(len(arguments)):
        roles, variable = (inputs, "input") if index in inputs else (outputs, "full")
        relation_args.append("(" + _component(variable, roles.index(index), len(roles)) + ")")
    return "\n".join([
        "import Lean", f"import {_lean(spec_module)}", "", f"namespace {_lean(namespace)}", "",
        f"abbrev Input := {input_type}", f"abbrev Observation := {observation_type}",
        f"abbrev FullOutput := {output_type}", "",
        "def encodeInput : Input → _root_.Lean.Json := _root_.Lean.ToJson.toJson",
        "def decodeInput : _root_.Lean.Json → _root_.Except _root_.String Input := _root_.Lean.FromJson.fromJson?",
        "def decodeObservation : _root_.Lean.Json → _root_.Except _root_.String Observation := _root_.Lean.FromJson.fromJson?", "",
        "def project (full : FullOutput) : Observation :=", f"  {_tuple(projected)}", "",
        "def Specification (input : Input) (observation : Observation) : Prop :=",
        "  ∃ full : FullOutput,", f"    ({_reference(relation['lean'])} {' '.join(relation_args)}) ∧",
        "    project full = observation", "", f'def profileId : String := "{profile_id}"', "",
        f"end {_lean(namespace)}", "",
    ])


def _source_fingerprints(project, spec_module, timeout_seconds):
    """Hash local source imports as reported by Lean, rather than parsing Lean text.

    Source files outside the Lake project (the pinned standard library) are bound
    by the toolchain identity. Direct external imports are also source-hashed.
    """
    source = project.joinpath(*spec_module.split(".")).with_suffix(".lean")
    if not source.is_file():
        raise ValueError(f"spec module source not found: {source}")
    toolchain = Path(run_checked(["lake", "env", "lean", "--print-prefix"], project, timeout_seconds).strip()).resolve()
    if not toolchain.is_dir():
        raise ValueError(f"Lean toolchain prefix is unavailable: {toolchain}")
    pending = [source.resolve()]
    fingerprints = {}
    while pending:
        current = pending.pop()
        label = str(current.relative_to(project)) if current.is_relative_to(project) else str(current)
        if label in fingerprints:
            continue
        fingerprints[label] = hashlib.sha256(current.read_bytes()).hexdigest()
        dependencies = run_checked(["lake", "env", "lean", "--src-deps", str(current)], project, timeout_seconds)
        for dependency in dependencies.splitlines():
            imported = Path(dependency)
            if not imported.is_absolute():
                imported = project / imported
            imported = imported.resolve()
            if not imported.is_file():
                raise ValueError(f"Lean import source unavailable: {imported}")
            if imported.is_relative_to(project):
                pending.append(imported)
            elif imported.is_relative_to(toolchain):
                label = "lean-toolchain:/" + imported.relative_to(toolchain).as_posix()
                fingerprints[label] = hashlib.sha256(imported.read_bytes()).hexdigest()
            else:
                raise ValueError(f"Unsupported external Lean source dependency outside project/toolchain: {imported}")
    for name in ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json"):
        path = project / name
        if path.is_file():
            fingerprints[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    return fingerprints


def _profile(project, manifest, selected, spec_module, timeout_seconds):
    value = {
        "view_schema_version": 1, "manifest": manifest,
        "configuration": {"schema_version": 1, "observation": selected.config},
        "spec_module": spec_module,
        "sources": _source_fingerprints(project, spec_module, timeout_seconds),
    }
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()).hexdigest()


def recompute_profile_id(project, manifest, config, observation_id, spec_module, timeout_seconds=60):
    """Recompute identity from current validated metadata and actual source closure.

    ``manifest``/``config`` accept paths or already-loaded objects. This does not
    publish files or trust a prior generated artifact, and does not hash properties.
    """
    project = Path(project).resolve()
    require_timeout(timeout_seconds)
    _name(spec_module, "spec module")
    data = load_manifest(manifest) if isinstance(manifest, (str, Path)) else validate_manifest(manifest)
    configuration = load_config(config) if isinstance(config, (str, Path)) else config
    selected = validate_observation(configuration, observation_id, data)
    return _profile(project, data, selected, spec_module, timeout_seconds)


def validate_generated_view(project, manifest, config, observation_id, spec_module,
                            view_module, namespace, timeout_seconds=60):
    """Bind a view's complete source to fresh metadata, rather than trusting profileId.

    Metadata may be paths or already-loaded dictionaries. As with generation,
    module names resolve relative to the Lake project's root source directory.
    """
    project = Path(project).resolve()
    require_timeout(timeout_seconds)
    _name(spec_module, "spec module")
    _name(view_module, "view module")
    _name(namespace, "view namespace")
    data = load_manifest(manifest) if isinstance(manifest, (str, Path)) else validate_manifest(manifest)
    configuration = load_config(config) if isinstance(config, (str, Path)) else config
    selected = validate_observation(configuration, observation_id, data)
    profile_id = _profile(project, data, selected, spec_module, timeout_seconds)
    expected = render_view(data, selected, spec_module, namespace, profile_id).encode("utf-8")
    source = project.joinpath(*view_module.split(".")).with_suffix(".lean")
    if not source.is_file() or source.read_bytes() != expected:
        raise ValueError(f"{source}: generated view differs from the selected metadata, source or namespace")
    return profile_id


def generate_view(project, manifest, config, observation_id, spec_module, namespace, output, timeout_seconds=60):
    """Compile first, then atomically create a fresh destination; return profileId."""
    project = Path(project).resolve()
    output = Path(output)
    if not output.is_absolute():
        output = project / output
    require_timeout(timeout_seconds)
    _name(spec_module, "spec module")
    _name(namespace, "view namespace")
    if os.path.lexists(output):
        raise FileExistsError(f"Refusing to overwrite existing observation view: {output}")
    data = load_manifest(manifest)
    selected = load_observation(config, observation_id, data)
    rebuild_modules(project, [spec_module], timeout_seconds)
    profile_id = _profile(project, data, selected, spec_module, timeout_seconds)
    source = render_view(data, selected, spec_module, namespace, profile_id)
    elaborate(project, source, timeout_seconds)
    if profile_id != _profile(project, data, selected, spec_module, timeout_seconds):
        raise ValueError("Spec module dependencies changed during view compilation")
    if data != load_manifest(manifest) or selected != load_observation(config, observation_id, data):
        raise ValueError("Observation metadata changed during view compilation")
    output.parent.mkdir(parents=True, exist_ok=True)
    # link is exclusive and atomic: even a racing writer or dangling symlink is
    # never replaced, and observers cannot see partially written Lean source.
    descriptor, temporary = tempfile.mkstemp(prefix=".observation-", suffix=".lean", dir=output.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(source)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, output)
    finally:
        os.unlink(temporary)
    return profile_id


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--observation", required=True)
    parser.add_argument("--spec-module", required=True)
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--timeout-seconds", type=float, default=60)
    args = parser.parse_args()
    identity = generate_view(args.project, args.manifest, args.config, args.observation,
                             args.spec_module, args.namespace, args.output, args.timeout_seconds)
    print(f"Generated and compiled observation view: {args.output}\nprofileId: {identity}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, TypeError, ChildProcessError, TimeoutError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
