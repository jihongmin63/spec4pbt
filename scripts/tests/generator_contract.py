"""Independent checker for exact-size, closed, typed generator experiment ASTs.

The JSON grammar has int/bool literals, de Bruijn variables, neg/not, add/eq,
if, and typed let. Even sample indices request int; odd indices request bool.
Node counts include expression constructors only. The digest uses wrapping
64-bit arithmetic and multiplier 1000003. This executable check is not a proof.
"""

from __future__ import annotations

from typing import NamedTuple, cast


TAGS: tuple[str, ...] = ("int", "bool", "var", "neg", "not", "add", "eq", "if", "let")
MASK: int = (1 << 64) - 1
Inspection = NamedTuple("Inspection", [("type", str), ("nodes", int), ("depth", int),
                                      ("histogram", tuple[int, ...]), ("digest", int)])


def fold_digest(values: tuple[int, ...]) -> int:
    """Force a deterministic traversal checksum using unsigned 64-bit arithmetic."""
    result: int = 0
    for value in values:
        result = (result * 1_000_003 + value) & MASK
    return result


def inspect_expr(value: object, context: tuple[str, ...]) -> Inspection:
    """Independently check syntax, scoping and typing and measure the complete AST."""
    if not isinstance(value, list) or not value or type(value[0]) is not str:
        raise ValueError(f"expression must be a nonempty tagged JSON array: {value!r}")
    items = cast(list[object], value)
    tag = cast(str, items[0])
    if tag not in TAGS:
        raise ValueError(f"unknown expression tag: {tag!r}")
    arity: int = {"int": 2, "bool": 2, "var": 2, "neg": 2, "not": 2,
                  "add": 3, "eq": 3, "if": 4, "let": 4}[tag]
    if len(items) != arity:
        raise ValueError(f"{tag}: expected array length {arity}, got {len(items)}")
    children: tuple[Inspection, ...] = ()
    payloads: tuple[int, ...] = ()
    result_type: str
    if tag == "int":
        number = items[1]
        if type(number) is not int or not 0 <= number <= 255:
            raise ValueError(f"int literal out of byte range: {number!r}")
        result_type, payloads = "int", (number,)
    elif tag == "bool":
        boolean = items[1]
        if type(boolean) is not bool:
            raise ValueError(f"bool literal must be JSON boolean: {boolean!r}")
        result_type, payloads = "bool", (int(boolean),)
    elif tag == "var":
        index = items[1]
        if type(index) is not int or not 0 <= index < len(context):
            raise ValueError(f"variable index {index!r} outside context {context!r}")
        result_type, payloads = context[index], (index,)
    elif tag == "let":
        binder = items[1]
        if binder not in ("int", "bool"):
            raise ValueError(f"invalid let binder type: {binder!r}")
        binder_type = cast(str, binder)
        rhs = inspect_expr(items[2], context)
        body = inspect_expr(items[3], (binder_type,) + context)
        if rhs.type != binder_type:
            raise ValueError(f"let expected RHS {binder_type}, got {rhs.type}")
        children, result_type, payloads = (rhs, body), body.type, (int(binder_type == "bool"),)
    else:
        children = tuple(inspect_expr(child, context) for child in items[1:])
        actual = tuple(child.type for child in children)
        expected: tuple[str, ...]
        if tag == "if":
            expected, result_type = ("bool", children[1].type, children[1].type), children[1].type
        elif tag in ("neg", "not"):
            result_type = "int" if tag == "neg" else "bool"
            expected = (result_type,)
        else:
            expected, result_type = ("int", "int"), "int" if tag == "add" else "bool"
        if actual != expected:
            raise ValueError(f"{tag}: expected child types {expected}, got {actual}")
    tag_id: int = TAGS.index(tag) + 1
    histogram = tuple(int(i == tag_id - 1) + sum(c.histogram[i] for c in children)
                      for i in range(len(TAGS)))
    return Inspection(result_type, 1 + sum(c.nodes for c in children),
                      1 + max((c.depth for c in children), default=0), histogram,
                      fold_digest((tag_id,) + payloads + tuple(c.digest for c in children)))


def inspect_record(value: object, index: int, nodes: int) -> Inspection:
    """Validate required sample fields while ignoring unrelated JSON fields."""
    if not isinstance(value, dict):
        raise ValueError(f"sample {index}: expected JSON object")
    record = cast(dict[str, object], value)
    expected_type: str = "int" if index % 2 == 0 else "bool"
    if type(record.get("index")) is not int or record["index"] != index:
        raise ValueError(f"sample index mismatch: expected {index}, got {record.get('index')!r}")
    if record.get("type") != expected_type or "expr" not in record:
        raise ValueError(f"sample {index}: required type={expected_type} and expr missing or incorrect")
    checked = inspect_expr(record["expr"], ())
    if checked.type != expected_type or checked.nodes != nodes:
        raise ValueError(f"sample {index}: expected ({expected_type}, {nodes} nodes), got {checked}")
    return checked
