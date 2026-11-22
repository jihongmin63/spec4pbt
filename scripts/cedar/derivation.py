"""Derivation copies of checked Cedar candidates for the official scheduler.

The pinned Testing Theorems plugin has two behaviours that change what is
measured, both reproduced on the frozen environment:

* It treats the global constant ``Original.entity_names`` in a premise as a
  variable and generates it, so most generated schemas are built over a
  different entity-name list.  Writing the literal list, as the upstream
  theorem does, restores the upstream schedule.
* It identifies inductive relations by their unqualified name.  A candidate
  ``predicate`` whose constructor delegates to the predecessor's
  ``predicate`` is compiled as a recursive call to itself, so the
  predecessor's generator is never derived or used.

The equivalence chain is always checked on the unmodified candidates.  Only
the copy given to the scheduler is rewritten: every inductive and constructor
declared in ``candidates/vNNN/Candidate.v`` gets the suffix ``_vNNN`` and every
reference to the fixed entity list becomes :data:`ENTITY_NAMES_LITERAL`.
:func:`verify_rewrite` re-tokenizes the written text and requires it to equal
the original token sequence except for exactly these substitutions.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping

def coq_string(text: str) -> str:
    """A notation-free Coq string term, valid without string_scope."""
    term = "Coq.Strings.String.EmptyString"
    for char in reversed(text.encode("ascii")):
        bits = " ".join("Coq.Init.Datatypes.true" if char >> bit & 1 else
                        "Coq.Init.Datatypes.false" for bit in range(8))
        term = f"(Coq.Strings.String.String (Coq.Strings.Ascii.Ascii {bits}) {term})"
    return term


def _entity_name(text: str) -> str:
    return (f"(Specification.cedar.Spec.MkName {coq_string(text)} "
            "(@Coq.Init.Datatypes.nil Coq.Strings.String.string))")


# The fixed list of Original.entity_names, written only with constructors so
# that it parses in any candidate file regardless of open scopes or imports.
ENTITY_NAMES_LITERAL = (
    "(@Coq.Init.Datatypes.cons Specification.cedar.Spec.EntityName "
    f"{_entity_name('EntityType1')} "
    "(@Coq.Init.Datatypes.cons Specification.cedar.Spec.EntityName "
    f"{_entity_name('EntityType2')} "
    "(@Coq.Init.Datatypes.nil Specification.cedar.Spec.EntityName)))")
ENTITY_NAME_FORMS = {"Original.entity_names", "Property.Original.entity_names", "entity_names"}
LITERAL_TOKEN = "<ENTITY_NAMES_LITERAL>"
VERSION_RE = re.compile(r"v[0-9]{3}\Z")
CANDIDATE_MODULE = re.compile(r"Property\.candidates\.(v[0-9]{3})\.Candidate\.([A-Za-z_][A-Za-z0-9_']*)\Z")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


class RewriteError(ValueError):
    pass


@dataclass(frozen=True)
class Token:
    kind: str  # ident, string, comment, space, other
    text: str
    line: int


def tokenize(source: str) -> list[Token]:
    """Split Coq source into identifiers, strings, comments, and other text.

    A qualified identifier is a dot-separated sequence of identifiers; a dot
    followed by anything else is a sentence terminator and stays separate.
    """
    tokens: list[Token] = []
    i, line, n = 0, 1, len(source)
    while i < n:
        c = source[i]
        start, start_line = i, line
        if source.startswith("(*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if source.startswith("(*", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("*)", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise RewriteError(f"unterminated comment at line {start_line}")
            kind = "comment"
        elif c == '"':
            i += 1
            while True:
                if i >= n:
                    raise RewriteError(f"unterminated string at line {start_line}")
                if source[i] == '"':
                    if i + 1 < n and source[i + 1] == '"':
                        i += 2
                        continue
                    i += 1
                    break
                i += 1
            kind = "string"
        elif c.isspace():
            while i < n and source[i].isspace():
                i += 1
            kind = "space"
        elif IDENT.match(source, i):
            i = IDENT.match(source, i).end()
            while i + 1 < n and source[i] == "." and IDENT.match(source, i + 1):
                i = IDENT.match(source, i + 1).end()
            kind = "ident"
        else:
            i += 1
            kind = "other"
        text = source[start:i]
        line += text.count("\n")
        tokens.append(Token(kind, text, start_line))
    return tokens


def declared_names(source: str) -> list[str]:
    """Inductive and constructor names declared by a candidate file."""
    names: list[str] = []
    tokens = [t for t in tokenize(source) if t.kind not in ("space", "comment")]
    in_inductive = False
    for index, token in enumerate(tokens):
        following = tokens[index + 1] if index + 1 < len(tokens) else None
        if token.kind == "ident" and token.text in ("Inductive", "with"):
            if following is None or following.kind != "ident" or "." in following.text:
                raise RewriteError(f"cannot read inductive name at line {token.line}")
            names.append(following.text)
            in_inductive = True
        elif token.kind == "other" and token.text == "|" and in_inductive:
            if following is None or following.kind != "ident" or "." in following.text:
                raise RewriteError(f"cannot read constructor name at line {token.line}")
            names.append(following.text)
        elif (token.kind == "other" and token.text == "." and in_inductive
              and (following is None or following.kind == "ident")):
            in_inductive = False
    # A constructor may be written without a leading bar after ``:=``.
    for index, token in enumerate(tokens[:-2]):
        if (token.kind == "other" and token.text == ":" and tokens[index + 1].text == "="
                and tokens[index + 2].kind == "ident"):
            following = tokens[index + 3] if index + 3 < len(tokens) else None
            if following is not None and following.text == ":":
                names.append(tokens[index + 2].text)
    if len(set(names)) != len(names):
        raise RewriteError(f"duplicate declared names: {names}")
    return names


def _suffix(name: str, version: str) -> str:
    return f"{name}_{version}"


def rewrite_candidate(source: str, version: str,
                      declared: Mapping[str, Iterable[str]]) -> tuple[str, list[dict]]:
    """Return the scheduler copy of ``version`` and its substitution list."""
    if not VERSION_RE.fullmatch(version) or version not in declared:
        raise RewriteError(f"unknown candidate version: {version}")
    own = set(declared[version])
    earlier = {other: set(names) for other, names in declared.items() if other < version}
    generated = {_suffix(name, other) for other, names in declared.items() for name in names}
    output, substitutions = [], []
    for token in tokenize(source):
        new = token.text
        if token.kind == "ident":
            text = token.text
            if text in generated:
                raise RewriteError(f"name {text} collides with a generated derivation name")
            match = CANDIDATE_MODULE.fullmatch(text)
            if text in ENTITY_NAME_FORMS:
                new = ENTITY_NAMES_LITERAL
            elif text in own:
                new = _suffix(text, version)
            elif match:
                other, name = match.groups()
                if other not in earlier:
                    raise RewriteError(f"{version} refers to non-predecessor {other}")
                if name in earlier[other]:
                    new = f"Property.candidates.{other}.Candidate.{_suffix(name, other)}"
            elif "." not in text and any(text in names for names in earlier.values()):
                raise RewriteError(f"unqualified reference to predecessor name {text} "
                                   f"at line {token.line}")
            elif "." in text and text.split(".")[-1] in set().union(own, *earlier.values()) \
                    and not text.startswith(("Original.", "Property.Original.")):
                raise RewriteError(f"partially qualified candidate reference {text} "
                                   f"at line {token.line}")
        if new != token.text:
            substitutions.append({"line": token.line, "from": token.text, "to": new})
        output.append(new)
    return "".join(output), substitutions


def _collapse_literal(tokens: list[Token]) -> list[Token]:
    pattern = [t.text for t in tokenize(ENTITY_NAMES_LITERAL) if t.kind != "space"]
    result, i = [], 0
    while i < len(tokens):
        window = [t.text for t in tokens[i:i + len(pattern)]]
        if window == pattern:
            result.append(Token("ident", LITERAL_TOKEN, tokens[i].line))
            i += len(pattern)
        else:
            result.append(tokens[i])
            i += 1
    return result


def verify_rewrite(original: str, rewritten: str, version: str,
                   declared: Mapping[str, Iterable[str]]) -> None:
    """Independently re-tokenize ``rewritten`` and allow only the two substitutions."""
    own = set(declared[version])
    allowed = {name: _suffix(name, version) for name in own}
    for other, names in declared.items():
        if other < version:
            for name in names:
                allowed[f"Property.candidates.{other}.Candidate.{name}"] = \
                    f"Property.candidates.{other}.Candidate.{_suffix(name, other)}"
    for form in ENTITY_NAME_FORMS:
        allowed[form] = LITERAL_TOKEN
    before = [t for t in tokenize(original) if t.kind != "space"]
    after = _collapse_literal([t for t in tokenize(rewritten) if t.kind != "space"])
    if len(before) != len(after):
        raise RewriteError(f"{version}: rewritten token count differs")
    for old, new in zip(before, after):
        if old.text == new.text:
            if old.kind == "ident" and old.text in allowed:
                raise RewriteError(f"{version}: {old.text} at line {old.line} was not rewritten")
            continue
        if old.kind != "ident" or allowed.get(old.text) != new.text:
            raise RewriteError(f"{version}: unexpected change at line {old.line}: "
                               f"{old.text!r} -> {new.text!r}")
    for token in after:
        if token.kind == "ident" and token.text in ENTITY_NAME_FORMS:
            raise RewriteError(f"{version}: entity_names constant remains at line {token.line}")


def inductive_references(source: str) -> dict[str, set[str]]:
    """Map each inductive declared in ``source`` to identifiers used in its body."""
    tokens = [t for t in tokenize(source) if t.kind not in ("space", "comment")]
    bodies: dict[str, set[str]] = {}
    current: str | None = None
    for index, token in enumerate(tokens):
        if token.kind == "ident" and token.text in ("Inductive", "with"):
            current = tokens[index + 1].text
            bodies[current] = set()
            continue
        if current is None:
            continue
        if token.kind == "other" and token.text == "." and (
                index + 1 == len(tokens) or tokens[index + 1].kind == "ident"):
            current = None
            continue
        if token.kind == "ident":
            bodies[current].add(token.text)
    return bodies


def reachable_relations(rewritten: Mapping[str, str], selected: str) -> list[str]:
    """Renamed inductives reachable from the selected predicate's definition."""
    bodies: dict[str, set[str]] = {}
    for version, source in rewritten.items():
        for name, used in inductive_references(source).items():
            qualified = {text.rsplit(".", 1)[-1] for text in used}
            bodies[name] = qualified
    root = _suffix("predicate", selected)
    if root not in bodies:
        raise RewriteError(f"selected relation {root} is not declared")
    seen, frontier = {root}, [root]
    while frontier:
        for name in bodies.get(frontier.pop(), ()):
            if name in bodies and name not in seen:
                seen.add(name)
                frontier.append(name)
    return sorted(seen)


def write_derivation_copy(checked: Path, sequence: list[str], destination: Path) -> dict:
    """Write rewritten Candidate.v files for ``sequence`` under ``destination``."""
    declared: dict[str, list[str]] = {}
    originals: dict[str, str] = {}
    for version in sequence:
        source = (checked / "candidates" / version / "Candidate.v").read_text()
        originals[version] = source
        declared[version] = declared_names(source)
        if "predicate" not in declared[version]:
            raise RewriteError(f"{version} declares no predicate")
    rewritten, record = {}, {"versions": {}}
    for version in sequence:
        text, substitutions = rewrite_candidate(originals[version], version, declared)
        target = destination / "candidates" / version / "Candidate.v"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        verify_rewrite(originals[version], target.read_text(), version, declared)
        rewritten[version] = text
        record["versions"][version] = {"declared": declared[version],
                                       "substitutions": substitutions}
    record["reachable_relations"] = reachable_relations(rewritten, sequence[-1])
    record["selected_relation"] = _suffix("predicate", sequence[-1])
    return record
