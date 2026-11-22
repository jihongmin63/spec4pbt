#!/usr/bin/env python3
"""Compile and inspect a Cedar candidate before an equivalence proof exists.

The gate accepts only new Prop-valued inductive relations. Every constructor
premise must elaborate to an application of a fixed Spec relation or another
new inductive relation. The separate benchmark performs generator derivation.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_ENV = ROOT / "environment/env.sh"
FLAGS = ["-R", "specification", "Specification", "-R", "property", "Property"]
VERSION = re.compile(r"v[0-9]{3}\Z")
IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9']*\Z")
HEAD = re.compile(r"@?([A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*)")
UNSAFE = re.compile(
    r"\b(?:Axiom|Axioms|Parameter|Parameters|Admitted|admit|Extract|Extraction|Load)\b"
    r"|\bDeclare\s+ML\b|\b(?:Add|Remove)\s+(?:Rec\s+)?(?:LoadPath|ML\s+Path)\b"
    r"|\bUnset\s+(?:Guard|Positivity|Universe)\s+Checking\b"
)
BAD_TERM = re.compile(r"\b(?:forall|fun|match|if|let|fix|cofix|Prop|SProp)\b|=>|->")
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
DATA_IMPORTS = {
    "Bool", "Coq.Bool.Bool", "List", "Coq.Lists.List",
    "String", "Coq.Strings.String", "Coq.Init.Datatypes",
}
DATA_SCOPES = {"bool_scope", "list_scope", "string_scope", "nat_scope"}
DATA_NOTATIONS = {"ListNotations", "StringNotations"}


class GateError(Exception):
    pass


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def code_only(source):
    """Mask nested comments and strings before checking authored directives."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "(*":
                depth += 1
                i += 2
            elif pair == "*)":
                depth -= 1
                i += 2
            else:
                i += 1
            out.append(" ")
        elif quoted:
            if pair == '""':
                i += 2
            else:
                quoted = source[i] != '"'
                i += 1
            out.append(" ")
        elif pair == "(*":
            depth = 1
            i += 2
            out.append(" ")
        elif source[i] == '"':
            quoted = True
            i += 1
            out.append(" ")
        else:
            out.append(source[i])
            i += 1
    if depth or quoted:
        raise GateError("Unterminated Coq comment or string")
    return "".join(out)


def candidate_commands(source):
    """Separate vernacular commands, keeping dots inside qualified names."""
    start = 0
    for index, char in enumerate(source):
        if char == "." and (index + 1 == len(source) or source[index + 1].isspace()):
            command = source[start:index].strip()
            if not command:
                raise GateError("Empty candidate command")
            yield command
            start = index + 1
    if source[start:].strip():
        raise GateError("Unterminated candidate command")


def check_candidate_commands(source, version):
    """Allow only fixed/data imports and inductive relations in a candidate."""
    predecessor = {f"Property.candidates.v{index:03d}.Candidate"
                   for index in range(1, int(version[1:]))}
    permitted = DATA_IMPORTS | predecessor | {
        "Property.Original", "Specification.cedar.Spec",
    }
    for command in candidate_commands(source):
        match = re.fullmatch(r"(?:From\s+([A-Za-z_][\w'.]*)\s+)?Require\s+Import\s+(.+)", command, re.S)
        if match:
            prefix, imports = match.groups()
            for module in imports.split():
                if not MODULE.fullmatch(module):
                    raise GateError(f"Unsupported candidate import: {module}")
                name = f"{prefix}.{module}" if prefix else module
                if name not in permitted:
                    raise GateError(f"Unsupported candidate import: {name}")
            continue
        match = re.fullmatch(r"Import\s+(.+)", command, re.S)
        if match and match.group(1).split() and set(match.group(1).split()) <= DATA_NOTATIONS:
            continue
        match = re.fullmatch(r"Open\s+Scope\s+([A-Za-z_][A-Za-z_0-9']*)", command)
        if match and match.group(1) in DATA_SCOPES:
            continue
        if re.match(r"Inductive\s", command):
            continue
        raise GateError(f"Unsupported candidate command: {command[:160]}")


def split_top(source, separator):
    """Split Coq's printed term at punctuation outside (), {}, and []."""
    parts, start, stack = [], 0, []
    opening = {"(": ")", "{": "}", "[": "]"}
    for i, char in enumerate(source):
        if char in opening:
            stack.append(opening[char])
        elif char in ")}]":
            if not stack or stack.pop() != char:
                raise GateError("Unbalanced elaborated Coq output")
        elif char == separator and not stack:
            parts.append(source[start:i].strip())
            start = i + 1
    if stack:
        raise GateError("Unbalanced elaborated Coq output")
    parts.append(source[start:].strip())
    return parts


def peel_foralls(term):
    binders = []
    term = term.strip()
    while re.match(r"forall\s", term):
        rest = term[len("forall"):].strip()
        pieces = split_top(rest, ",")
        if len(pieces) < 2:
            raise GateError(f"Cannot parse elaborated forall: {term[:160]}")
        prefix, term = pieces[0], ",".join(pieces[1:]).strip()
        while prefix:
            prefix = prefix.strip()
            if prefix.startswith("("):
                stack = 0
                end = None
                for index, char in enumerate(prefix):
                    if char == "(":
                        stack += 1
                    elif char == ")":
                        stack -= 1
                        if stack == 0:
                            end = index
                            break
                if end is None:
                    raise GateError("Malformed printed binder")
                group, prefix = prefix[1:end], prefix[end + 1:]
            else:
                group, prefix = prefix, ""
            pair = split_top(group, ":")
            if len(pair) < 2:
                raise GateError(f"Cannot parse elaborated binder: {group[:160]}")
            names, typ = pair[0], ":".join(pair[1:])
            for name in names.split():
                if not (IDENT.fullmatch(name) or name == "_"):
                    raise GateError(f"Unsupported elaborated binder: {name}")
                binders.append((name, typ))
    return binders, term


def relation_head(term):
    term = term.strip()
    while term.startswith("(") and term.endswith(")"):
        try:
            if len(split_top(term[1:-1], ",")) != 1:
                break
            term = term[1:-1].strip()
        except GateError:
            break
    match = HEAD.match(term)
    return match.group(1) if match else None


def declaration_names(glob):
    names = []
    for line in glob.splitlines():
        if not line or line.startswith(("DIGEST ", "F", "R")):
            continue
        kind = line.split(" ", 1)[0]
        if kind in {"binder", "constr", "scheme"}:
            continue
        if kind != "ind":
            raise GateError(f"Candidate declares unsupported {kind}: {line}")
        match = re.fullmatch(r"ind \d+:\d+ <> ([A-Za-z_][A-Za-z_0-9']*)", line)
        if not match:
            raise GateError(f"Cannot identify new inductive: {line}")
        names.append(match.group(1))
    if not names or names.count("predicate") != 1 or len(set(names)) != len(names):
        raise GateError("Candidate must declare exactly one inductive named predicate")
    return names


def printed_inductive(output, name):
    pattern = re.compile(r"\b(?:Inductive|with)\s+" + re.escape(name)
                         + r"\s*:\s*(.*?)\s*:=\s*(.*?)(?=\n\s+with\s+\w+\s*:|\.\s*\n|\Z)", re.S)
    match = pattern.search(output)
    if not match:
        raise GateError(f"Could not inspect elaborated inductive {name}")
    header, body = match.groups()
    header_binders, sort = peel_foralls(header)
    if sort.strip() != "Prop":
        raise GateError(f"{name} must be a Prop-valued inductive relation")
    constructors = []
    for piece in split_top(body, "|") if body.strip() else []:
        pair = split_top(piece, ":")
        if len(pair) < 2 or not IDENT.fullmatch(pair[0]):
            raise GateError(f"Cannot parse elaborated constructor of {name}")
        binders, result = peel_foralls(":".join(pair[1:]))
        constructors.append((pair[0], binders, result))
    return header_binders, constructors


def printed_sort(output, name):
    pattern = re.compile(r"\b(?:Inductive|with)\s+" + re.escape(name) + r"\s*:\s*(.*?)\s*:=", re.S)
    match = pattern.search(output)
    if not match:
        raise GateError(f"Could not inspect elaborated sort of {name}")
    _, sort = peel_foralls(match.group(1))
    return sort.strip()


class Gate:
    def __init__(self, property_root, candidate, evidence, env, timeout):
        self.property = property_root.resolve()
        self.candidate = candidate
        self.evidence = evidence.resolve()
        self.env = env.resolve()
        self.timeout = timeout
        self.evidence.mkdir(parents=True, exist_ok=False)
        self.sources = self.evidence / "sources"
        self.sources.mkdir()
        self.report = {"status": "running", "property": str(self.property),
                       "candidate": candidate, "source_hashes": {}, "commands": [],
                       "env_script": str(self.env), "env_sha256": sha256(self.env.read_bytes()),
                       "syntax_sha256": sha256(Path(__file__).read_bytes())}
        self.write_report()

    def write_report(self):
        (self.evidence / "result.json").write_text(json.dumps(self.report, indent=2) + "\n")

    def run(self, arguments, label, expect_success=True):
        command = ["bash", str(self.env), *arguments]
        log = self.evidence / f"{label}.log"
        error_log = self.evidence / f"{label}.stderr.log"
        entry = {"command": command, "stdout": log.name, "stderr": error_log.name}
        self.report["commands"].append(entry)
        self.write_report()
        start = time.monotonic()
        with log.open("w") as output, error_log.open("w") as errors:
            process = subprocess.Popen(command, cwd=self.sources, stdout=output,
                                       stderr=errors, start_new_session=True)
            try:
                code = process.wait(timeout=self.timeout)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                raise GateError(f"{label} timed out; see {log}")
        entry.update(returncode=code, seconds=round(time.monotonic() - start, 6))
        self.write_report()
        if (code == 0) != expect_success:
            tail = (log.read_text() + error_log.read_text())[-1500:]
            raise GateError(f"{label} {'failed' if expect_success else 'unexpectedly succeeded'}: {tail}")
        return log.read_text()

    def snapshot(self):
        if not VERSION.fullmatch(self.candidate):
            raise GateError("Candidate must be named vNNN")
        number = int(self.candidate[1:])
        if number < 1:
            raise GateError("Candidate sequence begins with v001")
        paths = [(self.property / "Original.v", Path("property/Original.v"))]
        for index in range(1, number + 1):
            name = f"v{index:03d}"
            paths.append((self.property / "candidates" / name / "Candidate.v",
                          Path("property/candidates") / name / "Candidate.v"))
        spec = ROOT / "specification"
        for path in sorted(spec.rglob("*.v")):
            relative = path.relative_to(spec)
            if not all(IDENT.fullmatch(part) for part in (*relative.parts[:-1], relative.stem)):
                raise GateError(f"Unsupported specification path: {relative}")
            paths.append((path, Path("specification") / relative))
        for source, relative in paths:
            if not source.is_file() or source.is_symlink():
                raise GateError(f"Missing regular source: {source}")
            data = source.read_bytes()
            if relative == Path("property/Original.v"):
                fixed_original = (ROOT / "properties/cedar_no_type_error/Original.v").read_bytes()
                if data != fixed_original:
                    raise GateError("Staged Original.v differs from the fixed repository Original.v")
            try:
                stripped = code_only(data.decode("utf-8"))
            except UnicodeError as error:
                raise GateError(f"Invalid UTF-8 source: {source}") from error
            if UNSAFE.search(stripped):
                raise GateError(f"Unsafe authored Coq directive: {source}")
            if relative.parts[:2] == ("property", "candidates"):
                check_candidate_commands(stripped, relative.parts[2])
            target = self.sources / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            self.report["source_hashes"][str(relative)] = sha256(data)
        self.write_report()

    def compile_sources(self):
        files = sorted(str(p.relative_to(self.sources)) for p in self.sources.rglob("*.v"))
        order = self.run(["coqdep", "-sort", *FLAGS, *files], "dependencies").split()
        order = [str(Path(item).with_suffix(".v")) for item in order]
        if len(order) != len(files) or set(order) != set(files):
            raise GateError("Coq could not determine an acyclic source compilation order")
        for index, file in enumerate(order):
            self.run(["coqc", "-q", *FLAGS, file], f"compile-{index:03d}")

    def inspect(self):
        fixed = set()
        spec_glob = self.sources / "specification/cedar/Spec.glob"
        spec_names = []
        for line in spec_glob.read_text().splitlines():
            match = re.fullmatch(r"ind \d+:\d+ <> ([A-Za-z_][A-Za-z_0-9']*)", line)
            if match:
                spec_names.append(match.group(1))
        spec_inspect_name = "SyntaxSpecInspect.v"
        (self.sources / spec_inspect_name).write_text(
            "Require Import Specification.cedar.Spec.\nSet Printing All.\n"
            + "\n".join(f"Print Specification.cedar.Spec.{name}." for name in spec_names) + "\n")
        spec_printed = self.run(["coqc", "-q", *FLAGS, spec_inspect_name], "fixed-spec-sorts")
        for name in spec_names:
            if printed_sort(spec_printed, name) == "Prop":
                fixed.add("Specification.cedar.Spec." + name)
        predecessor = set()
        verified = {}
        for index in range(1, int(self.candidate[1:]) + 1):
            version = f"v{index:03d}"
            module = f"Property.candidates.{version}.Candidate"
            relative = Path("property/candidates") / version / "Candidate"
            glob = (self.sources / relative).with_suffix(".glob")
            names = declaration_names(glob.read_text())
            inspect_name = f"SyntaxInspect_{version}.v"
            inspect_file = self.sources / inspect_name
            inspect_file.write_text("Require Import " + module + ".\nSet Printing All.\n"
                                    + "\n".join(f"Print {module}.{name}." for name in names) + "\n"
                                    + f"Check ({module}.predicate : Property.Original.Input -> Prop).\n")
            printed = self.run(["coqc", "-q", *FLAGS, inspect_name], f"elaborated-{version}")
            permitted = fixed | predecessor | {module + "." + name for name in names}
            resolved_heads = {}
            def resolve_head(head):
                if head not in resolved_heads:
                    path = self.sources / f"SyntaxResolve_{version}_{len(resolved_heads):03d}.v"
                    path.write_text(f"Require Import {module}.\nAbout {head}.\n")
                    try:
                        output = self.run(["coqc", "-q", *FLAGS,
                                           path.name],
                                          f"resolve-{version}-{len(resolved_heads):03d}")
                    except GateError:
                        # A printed local binder or sort need not be a global.
                        # The following Prop probe still rejects any condition.
                        resolved_heads[head] = None
                    else:
                        identities = re.findall(
                            r"^Expands to:\s+Inductive\s+([A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*)\s*$",
                            output, re.M)
                        resolved_heads[head] = identities[0] if len(identities) == 1 else None
                return resolved_heads[head]
            checks = []
            for name in names:
                header, constructors = printed_inductive(printed, name)
                checks.append((name, "relation", header))
                for constructor, binders, result in constructors:
                    result_head = relation_head(result)
                    if (not result_head or
                            result_head in {binder for binder, _ in binders} or
                            resolve_head(result_head) != module + "." + name):
                        raise GateError(f"Constructor of {name} has unexpected result: {result}")
                    checks.append((name, constructor, binders))
            probe = 0
            for relation, context, binders in checks:
                prefix = []
                for binder, typ in binders:
                    if BAD_TERM.search(typ):
                        raise GateError(f"{version}.{relation}.{context}: higher-order or nested condition in {typ}")
                    head = relation_head(typ)
                    # Resolve under the candidate's Coq import scope. Textual
                    # aliases from Print All are not declaration identities.
                    # A preceding binder shadows any global of the same name.
                    local_names = {name for name, _ in prefix}
                    identity = (resolve_head(head) if head and
                                head not in local_names and head not in {"Set", "Type"}
                                else None)
                    expected_prop = identity in permitted
                    lambda_prefix = "".join(f"fun ({n} : {t}) => " for n, t in prefix)
                    if expected_prop:
                        source = f"Check ({lambda_prefix}({typ} : Prop)).\n"
                    else:
                        source = f"Check ({lambda_prefix}{typ}).\nFail Check ({lambda_prefix}({typ} : Prop)).\n"
                    probe_name = f"SyntaxProbe_{version}_{probe:03d}.v"
                    path = self.sources / probe_name
                    path.write_text("Require Import " + module + ".\nSet Printing All.\n" + source)
                    try:
                        self.run(["coqc", "-q", *FLAGS, probe_name], f"probe-{version}-{probe:03d}")
                    except GateError as error:
                        if not expected_prop and "The command has not failed!" in str(error):
                            raise GateError(f"{version}.{relation}.{context}: proposition premise is not a permitted inductive relation application: {typ}") from error
                        raise
                    classification = "relation premise" if expected_prop else "data binder"
                    self.report.setdefault("binders", []).append({"version": version,
                        "relation": relation, "constructor": context, "name": binder,
                        "type": typ, "classification": classification,
                        **({"resolved_relation": identity} if expected_prop else {})})
                    prefix.append((binder, typ))
                    probe += 1
            verified[version] = names
            predecessor.update({f"Property.candidates.{version}.Candidate.{name}" for name in names})
        self.report["new_relations"] = verified[self.candidate]
        self.report["verified_relations"] = verified
        self.report["fixed_spec_relations"] = sorted(fixed)
        self.write_report()

    def check_fresh(self):
        for relative, expected in self.report["source_hashes"].items():
            if relative.startswith("specification/"):
                source = ROOT / relative
            else:
                source = self.property / relative.removeprefix("property/")
            if not source.is_file() or sha256(source.read_bytes()) != expected:
                raise GateError(f"Source changed during gate: {source}")
        if sha256(self.env.read_bytes()) != self.report["env_sha256"]:
            raise GateError("Environment script changed during gate")
        if sha256(Path(__file__).read_bytes()) != self.report["syntax_sha256"]:
            raise GateError("Syntax gate changed during verification")

    def execute(self):
        self.snapshot()
        version = self.run(["coqc", "--version"], "version")
        if "version 8.20.0" not in version or "OCaml 4.14.2" not in version:
            raise GateError("Expected Coq 8.20.0 and OCaml 4.14.2")
        self.compile_sources()
        self.inspect()
        self.check_fresh()
        self.report["status"] = "passed"
        self.write_report()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("property", type=Path)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--evidence-dir", required=True, type=Path)
    parser.add_argument("--env-script", type=Path, default=DEFAULT_ENV)
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    gate = None
    try:
        if args.timeout <= 0:
            raise GateError("Timeout must be positive")
        gate = Gate(args.property, args.candidate, args.evidence_dir,
                    args.env_script, args.timeout)
        gate.execute()
        print(gate.evidence / "result.json")
        return 0
    except (GateError, OSError) as error:
        if gate:
            gate.report.update(status="failed", error=str(error))
            gate.write_report()
            print(gate.evidence / "result.json", file=sys.stderr)
        print(error, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
