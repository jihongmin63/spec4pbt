"""Validate typed relation manifests and observation selectors."""

from dataclasses import dataclass
import re


# This deliberately supports the ordinary ASCII subset emitted by the translator.
_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
_RESERVED = set("_ axiom abbrev by check class def deriving do else end example export false for forall fun if import in inductive instance let macro match mutual namespace noncomputable notation opaque open partial private protected section set_option structure syntax theorem then true universe unsafe variable where with Type Prop Sort".split())
SELECTOR = re.compile(r"%(0|[1-9][0-9]*)(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


def _name(value, source, *, dotted=True):
    if not isinstance(value, str) or not value:
        raise ValueError(f"{source}: expected a Lean identifier")
    parts = value.split(".") if dotted else [value]
    if any(_IDENTIFIER.fullmatch(part) is None or part in _RESERVED for part in parts):
        raise ValueError(f"{source}: invalid Lean identifier {value!r}")
    return value


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
    """Check the complete v1 manifest, including unselected entries."""
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
            if not isinstance(raw, str) or SELECTOR.fullmatch(raw) is None:
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
