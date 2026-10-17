#!/usr/bin/env python3
"""Generate a total-coverage P4 syntax renderer from SpecTec constructors.

The generated Lean lives outside specifications/p4. It renders every syntax
constructor reachable from p4program, but rejects constructors whose generated
AST discarded a lexical identifier (for example `_TID '.' %`).
"""

from __future__ import annotations

import json
import pathlib
import re


ROOT = pathlib.Path(__file__).resolve().parents[3]
SOURCES = [ROOT / f"specifications/p4/SpecTecDecl{i:04d}.lean" for i in range(9)]
OUTPUT = ROOT / "pbt/p4/UnparseGenerated.lean"
TEXT = "\n".join(path.read_text() for path in SOURCES)
BLOCKS = dict(
    re.findall(
        r"^inductive ([^ :]+) : Type where\n(.*?)(?=\n(?:deriving|\ninductive|\nend\n))",
        TEXT,
        re.M | re.S,
    )
)
ALIASES = dict(re.findall(r"^abbrev (\w+) : Type := (.+)$", TEXT, re.M))
PRIMITIVES = {"_root_.Nat", "_root_.Int", "_root_.String", "_root_.Bool"}


def constructors(typ: str) -> list[tuple[str, list[str]]]:
    result = []
    for line in BLOCKS[typ].splitlines():
        if not line.strip().startswith("|"):
            continue
        name, signature = line.strip()[2:].split(" : ", 1)
        result.append((name, signature.split(" → ")[:-1]))
    return result


def canonical(typ: str) -> str:
    while typ in ALIASES:
        typ = ALIASES[typ]
    return typ


reachable: set[str] = set()


def visit(typ: str) -> None:
    typ = canonical(typ)
    if typ in PRIMITIVES or typ in reachable:
        return
    if typ not in BLOCKS:
        raise ValueError(f"Unknown syntax type {typ}")
    reachable.add(typ)
    for _, fields in constructors(typ):
        for field in fields:
            visit(field)


visit("p4program")
TYPES = [typ for typ in BLOCKS if typ in reachable]
RESERVED = sorted(
    {
        name.lower()
        for typ in ("annotationToken", "name")
        for name, fields in constructors(typ)
        if not fields and re.fullmatch(r"[A-Z][A-Z0-9_]*", name)
    }
)


def function_name(typ: str) -> str:
    typ = canonical(typ)
    return "render" + typ[0].upper() + typ[1:]


def literal(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def grammar_tokens(name: str, fields: list[str]) -> list[str]:
    if name.startswith("«") and name.endswith("»"):
        return name[1:-1].split()
    if name == "_EMPTY":
        return []
    if name in {"_ID", "_TID", "D"}:
        return ["%"]
    if name == "TRANSITION" and fields:
        return ["TRANSITION", "%"]
    if fields:
        raise ValueError(f"Unrecognized constructor with fields: {name} {fields}")
    return [name]


def render_literal_token(token: str) -> str:
    if token.startswith("'") and token.endswith("'"):
        return token[1:-1]
    if token.startswith("`"):
        return token[1:]
    if token in {"_ID", "_TID"}:
        raise ValueError("Identifier placeholder has no payload")
    if token in {"W", "S"}:
        raise ValueError("Width literal must be handled as one token")
    return token.lower()


def field_expression(field: str, name: str, variable: str, typ: str) -> str:
    field = canonical(field)
    if field == "_root_.String":
        if name not in {"_ID", "_TID"}:
            raise ValueError(f"Unexpected raw String field in {typ}.{name}")
        return f"renderIdentifier {literal(typ + '.' + name)} {variable}"
    if field == "_root_.Int":
        return f"renderNonnegativeInt {literal('SpecTec.' + typ + '.' + name)} {variable}"
    if field == "_root_.Nat":
        return f"pure (toString {variable})"
    if field == "_root_.Bool":
        return f"pure (if {variable} then \"true\" else \"false\")"
    return f"{function_name(field)} {variable}"


def case_lines(typ: str, name: str, fields: list[str]) -> list[str]:
    variables = [f"x{i}" for i in range(len(fields))]
    pattern = f".{name}" + (" " + " ".join(variables) if variables else "")
    head = f"  | {pattern} =>"

    if typ == "annotationToken" and name == "UNEXPECTED_TOKEN":
        return [head,
                '      .error "SpecTec.annotationToken.UNEXPECTED_TOKEN is a parser sentinel, not P4 source"']

    if typ == "p4program":
        if name == "_EMPTY":
            return [head, '      pure ""']
        if name == "«% %»":
            return [head, "      do", "        let prior ← renderP4program x0",
                    "        let declaration ← renderDeclaration x1",
                    '        pure (prior ++ declaration ++ "\\n")']
        if name == "«% ';'»":
            return [head, "      do", "        let prior ← renderP4program x0",
                    '        pure (prior ++ ";\\n")']
        raise ValueError(f"Unexpected p4program constructor: {name}")

    if name == "«'\"' % '\"'»":
        if fields != ["_root_.String"]:
            raise ValueError(f"Unexpected string-literal fields in {typ}.{name}")
        return [head,
                f'      renderRawStringLiteral {literal("SpecTec." + typ + "." + name)} x0']

    if name in {"«% W %»", "«% S %»"}:
        if fields != ["_root_.Nat", "_root_.Int"]:
            raise ValueError(f"Unexpected width-literal fields in {typ}.{name}")
        marker = "w" if name == "«% W %»" else "s"
        return [head, "      do",
                f"        let magnitude ← renderNonnegativeInt {literal('SpecTec.' + typ + '.' + name)} x1",
                f'        pure (toString x0 ++ "{marker}" ++ magnitude)']

    tokens = grammar_tokens(name, fields)
    if tokens.count("%") != len(fields):
        raise ValueError(f"Template arity mismatch in {typ}.{name}: {tokens} {fields}")

    if "_ID" in tokens or "_TID" in tokens:
        return [head, "      .error " + literal(
            f"SpecTec.{typ}.{name} discarded an identifier lexeme")]

    lines = [head, "      do"]
    for i, field in enumerate(fields):
        lines.append(
            f"        let s{i} ← {field_expression(field, name, variables[i], typ)}"
        )
    parts: list[str] = []
    field_index = 0
    for token in tokens:
        if token == "%":
            # Braces fix the association of an outer ELSE when its THEN arm is
            # itself an IF without ELSE. They are valid for both control and
            # parser statements and keep the AST's branch nesting explicit.
            if name == "«IF `( % `) % ELSE %»" and field_index == 1:
                parts.append('joinTokens ["{", s1, "}"]')
            else:
                parts.append(f"s{field_index}")
            field_index += 1
        else:
            parts.append(literal(render_literal_token(token)))
    joined = f"joinTokens [{', '.join(parts)}]"
    operator_expression = (
        (name == "«% %»" and fields and canonical(fields[0]) == "unop")
        or (name == "«% % %»" and len(fields) == 3 and canonical(fields[1]) == "binop")
        or name == "«% '?' % ':' %»"
        or (name == "«`( % `) %»" and fields == ["type", "expression"])
    )
    if operator_expression:
        joined = f'joinTokens ["(", {joined}, ")"]'
    lines.append(f"        pure ({joined})")
    return lines


lines = [
    "import SpecTecAll\n\n",
    "-- Generated by `python3 pbt/p4/tools/unparse_codegen.py`.\n",
    "-- Do not edit this file directly; generated SpecTec sources are unchanged.\n\n",
    "set_option autoImplicit false\n",
    "set_option linter.unusedVariables false\n",
    "set_option maxRecDepth 8192\n",
    "set_option maxHeartbeats 0\n\n",
    "namespace Spec4Pbt.P4.Generated\n\n",
    "private def joinTokens (parts : List String) : String :=\n",
    '  " ".intercalate (parts.filter (· != ""))\n\n',
    "private def isIdentifierStart (c : Char) : Bool :=\n",
    "  let n := c.toNat\n",
    "  decide (n = 95 ∨ (65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122))\n\n",
    "private def isIdentifierContinue (c : Char) : Bool :=\n",
    "  isIdentifierStart c || decide (48 ≤ c.toNat ∧ c.toNat ≤ 57)\n\n",
    "private def validIdentifier (s : String) : Bool :=\n",
    "  match s.toList with\n",
    "  | [] => false\n",
    "  | first :: rest => isIdentifierStart first && rest.all isIdentifierContinue\n\n",
    "private def reservedIdentifiers : List String :=\n",
    "  [" + ", ".join(literal(name) for name in RESERVED) + "]\n\n",
    "private def renderIdentifier (context s : String) : Except String String :=\n",
    "  if s != \"_\" && validIdentifier s && !(reservedIdentifiers.contains s) then pure s\n",
    '  else .error (context ++ " contains an invalid, reserved, or empty P4 identifier: " ++ s)\n\n',
    "private def renderNonnegativeInt (context : String) (value : Int) : Except String String :=\n",
    "  if value < 0 then .error (context ++ \" contains a negative raw P4 integer literal\")\n",
    "  else pure (toString value)\n\n",
    "private def safeRawStringPayload (s : String) : Bool :=\n",
    "  s.toList.all (fun c =>\n",
    "    let n := c.toNat\n",
    "    decide (32 ≤ n ∧ n ≤ 126 ∧ n ≠ 34 ∧ n ≠ 92))\n\n",
    "private def renderRawStringLiteral (context s : String) : Except String String :=\n",
    '  if safeRawStringPayload s then pure ("\\\"" ++ s ++ "\\\"")\n',
    '  else .error (context ++ " contains bytes that cannot be represented exactly as a raw P4 string literal")\n\n',
    "mutual\n\n",
]

for typ in TYPES:
    lines.append(
        f"def {function_name(typ)} (value : SpecTec.{typ}) : "
        "Except String String :=\n"
    )
    lines.append("  match value with\n")
    for name, fields in constructors(typ):
        lines.extend(line + "\n" for line in case_lines(typ, name, fields))
    lines.append("\n")

lines.extend(["end\n\n", "end Spec4Pbt.P4.Generated\n"])
OUTPUT.write_text("".join(lines))
print(
    f"generated {len(TYPES)} renderers, "
    f"{sum(len(constructors(typ)) for typ in TYPES)} constructors"
)
