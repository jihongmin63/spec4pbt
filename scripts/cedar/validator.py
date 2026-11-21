#!/usr/bin/env python3
"""Classify the five *Original* Cedar premises with retained Coq proofs.

Input is JSONL with an ``id`` and a complete ``input_coq`` constructor term.
``null`` denotes a generator attempt that returned no input.  The output is
JSONL in the same order.  Repeated byte-identical terms share one Coq verdict
and one evidence reference.  All files needed to audit verdicts stay under
``--evidence-dir``; this tool never invokes the candidate predicate or Rust.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PREMISES = (
    "WfSchema",
    "ActionSchemaToRequestTypes",
    "SchemaToEnvironments",
    "WfCedarType",
    "HasType",
)
DEFAULT_BATCH_SIZE = 500
DEFAULT_BATCH_WORKERS = 4
MAX_BATCH_SECONDS = 1200
PROOF_DEPTH = 12  # Fixed in Validator.v; repeated here for the manifest.
TACTIC_TIMEOUT_SECONDS = 1  # Per positive and negative search, in Validator.v.
TAG_RE = re.compile(
    r'=\s*\("([0-9a-f]{64}):(\w+)"\s*,\s*"(valid|invalid|unknown)"\s*\)',
    re.M,
)
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")
NUMBER_RE = re.compile(r"[0-9]+(?:%[A-Za-z][A-Za-z_0-9]*)?")
FORBIDDEN_WORDS = {
    "let", "in", "fun", "match", "with", "fix", "cofix", "ltac", "eval",
    "compute", "admit", "admitted", "axiom", "parameter", "definition",
    "require", "import", "include", "set", "unset", "fail", "succeed",
    "refine", "exact", "pose", "proof", "qed", "defined", "abort",
}


class ValidationError(Exception):
    pass


class CoqTimeout(ValidationError):
    def __init__(self, message: str, stdout: str = "", stderr: str = ""):
        super().__init__(message)
        self.stdout = stdout
        self.stderr = stderr


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def capture_group(command: list[str], cwd: Path | None, timeout: int) -> tuple[int, str, str]:
    process = subprocess.Popen(
        command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        raise CoqTimeout(
            f"Coq command timed out after {timeout}s: {command[-1]}", stdout, stderr
        ) from exc
    return process.returncode, stdout, stderr


def check_constructor_term(term: str) -> None:
    """Accept constructor applications, lists, tuples, strings and numerals.

    Only a standalone full ``mkInput`` application is accepted.  A period can
    occur inside a qualified identifier or a quoted Coq string, never as a
    vernacular command terminator.  Colon, comments, tactic quotation and
    definition syntax are excluded.  Coq type checking then verifies the
    seven field types and exact constructor arity.
    """
    if not isinstance(term, str) or not term.strip():
        raise ValidationError("input_coq must be a nonempty Coq constructor term")
    words: list[str] = []
    stack: list[str] = []
    i = 0
    while i < len(term):
        c = term[i]
        if c.isspace():
            i += 1
            continue
        if c == '"':
            i += 1
            while i < len(term):
                if term[i] == '"':
                    if i + 1 < len(term) and term[i + 1] == '"':
                        i += 2
                        continue
                    i += 1
                    break
                if ord(term[i]) < 32:
                    raise ValidationError("control character in Coq string")
                i += 1
            else:
                raise ValidationError("unterminated Coq string")
            continue
        match = IDENT_RE.match(term, i)
        if match:
            word = match.group()
            if word.lower() in FORBIDDEN_WORDS or any(
                part.lower() in FORBIDDEN_WORDS for part in word.split('.')
            ):
                raise ValidationError(f"forbidden Coq term word: {word}")
            words.append(word)
            i = match.end()
            continue
        match = NUMBER_RE.match(term, i)
        if match:
            i = match.end()
            continue
        if c in '([':
            stack.append(c)
        elif c in ')]':
            if not stack or stack.pop() != {')': '(', ']': '['}[c]:
                raise ValidationError("unbalanced Coq constructor term")
        elif c == ';':
            if not stack or stack[-1] != '[':
                raise ValidationError("list separator outside Coq list")
        elif c == ',':
            if not stack or stack[-1] != '(':
                raise ValidationError("tuple separator outside parentheses")
        elif c not in '%-+':
            raise ValidationError(f"forbidden Coq term character: {c!r}")
        i += 1
    if stack:
        raise ValidationError("unbalanced Coq constructor term")
    if not words or words[0] not in {
        "mkInput", "Original.mkInput", "Property.Original.mkInput"
    }:
        raise ValidationError("input_coq must begin with the Original.mkInput constructor")


def premise_term(sample: str, name: str) -> str:
    fields = {
        "WfSchema": f"WfSchema entity_names (MkSchema (ets {sample}) (acts {sample}))",
        "ActionSchemaToRequestTypes": f"ActionSchemaToRequestTypes (acts {sample}) [] (rs {sample})",
        "SchemaToEnvironments": (
            f"SchemaToEnvironments (MkSchema (ets {sample}) (acts {sample})) "
            f"(rs {sample}) (e {sample} :: es {sample})"
        ),
        "WfCedarType": f"WfCedarType entity_names (ty {sample})",
        "HasType": f"HasType (somepaths []) (e {sample}) (expr {sample}) (ty {sample})",
    }
    return fields[name]


def batch_source(items: list[tuple[str, str]]) -> str:
    lines = [
        "Require Import String ZArith List.",
        "Require Import Specification.cedar.Spec.",
        "Require Import Property.Original.",
        "Require Import CedarValidator.Validator.",
        "Import ListNotations.",
        "Open Scope string_scope.",
        "Open Scope Z_scope.",
    ]
    for index, (digest, expression) in enumerate(items):
        sample = f"sample_{index}"
        lines.append(f"Definition {sample} : Input := ({expression}).")
        for p_index, name in enumerate(PREMISES):
            prop = f"premise_{index}_{p_index}"
            verdict = f"verdict_{index}_{p_index}"
            lines.append(f"Definition {prop} : Prop := {premise_term(sample, name)}.")
            lines.append(
                f"Definition {verdict} : option ({{{prop}}}+{{~{prop}}}) "
                ":= ltac:(cedar_verdict)."
            )
            lines.append(
                f'Eval lazy in ("{digest}:{name}", cedar_verdict_tag {verdict}).'
            )
            lines.append(f"Print Assumptions {verdict}.")
    return "\n".join(lines) + "\n"


def run_coq(command: list[str], cwd: Path, log: Path, timeout: int) -> str:
    if log.exists():
        raise ValidationError(f"refusing to overwrite prior Coq log: {log}")
    log.touch(exist_ok=False)
    try:
        return_code, stdout, stderr = capture_group(command, cwd, timeout)
    except CoqTimeout as error:
        log.write_text(error.stdout + error.stderr + "\nTIMEOUT\n")
        raise
    log.write_text(stdout + stderr)
    if return_code:
        raise ValidationError(f"Coq command failed ({return_code}); see {log}")
    log.with_suffix(log.suffix + ".ok").touch(exist_ok=False)
    return stdout


def prepare_build(root: Path, evidence: Path, env_script: Path,
                  coq_version: str, batch_size: int, batch_workers: int) -> tuple[Path, str]:
    coq_sources = {
        Path("specification/cedar/Spec.v"): root / "specification/cedar/Spec.v",
        Path("property/Original.v"): root / "properties/cedar_no_type_error/Original.v",
        Path("validator/Validator.v"): root / "scripts/cedar/Validator.v",
    }
    sources = {
        **coq_sources,
        Path("tool/validator.py"): Path(__file__).resolve(),
        Path("tool/env.sh"): env_script,
    }
    configuration = json.dumps({
        "coq_version": coq_version,
        "batch_size": batch_size,
        "batch_workers": batch_workers,
        "max_batch_seconds": MAX_BATCH_SECONDS,
        "proof_depth": PROOF_DEPTH,
        "tactic_timeout_seconds": TACTIC_TIMEOUT_SECONDS,
    }, sort_keys=True).encode()
    fingerprint = sha256(configuration + b"".join(
        str(relative).encode() + b"\0" + path.read_bytes() for relative, path in sources.items()
    ))
    build = evidence / f"build-{fingerprint[:16]}"
    build.mkdir(parents=True, exist_ok=True)
    for relative, source in sources.items():
        destination = build / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.exists():
            if destination.read_bytes() != source.read_bytes():
                raise ValidationError(f"evidence source changed: {destination}")
        else:
            shutil.copyfile(source, destination)
    flags = ["-q", "-R", "specification", "Specification", "-R", "property", "Property",
             "-R", "validator", "CedarValidator"]
    for relative in coq_sources:
        log = build / f"{relative.stem}.coqc.log"
        if not (build / relative.with_suffix(".vo")).is_file():
            run_coq(["bash", str(env_script), "coqc", *flags, str(relative)], build,
                    log, 120)
        elif not log.with_suffix(log.suffix + ".ok").is_file():
            raise ValidationError(f"compiled object has no successful build log: {log}")
    base_kernel_log = build / "Validator.coqchk.log"
    if not base_kernel_log.is_file():
        run_coq(["bash", str(env_script), "coqchk", "-silent", *flags[1:],
                 "CedarValidator.Validator"], build, base_kernel_log, 120)
    elif not base_kernel_log.with_suffix(base_kernel_log.suffix + ".ok").is_file():
        raise ValidationError(f"previous kernel check did not pass: {base_kernel_log}")
    return build, fingerprint


def validate_batch(items: list[tuple[str, str]], build: Path, env_script: Path,
                   sequence: int, fingerprint: str) -> dict[str, dict]:
    batch_name = f"batch_{sequence:06d}"
    source = build / f"{batch_name}.v"
    try:
        with source.open("x") as stream:
            stream.write(batch_source(items))
    except FileExistsError as error:
        raise ValidationError(f"refusing to overwrite prior evidence: {source}") from error
    flags = ["-q", "-R", "specification", "Specification", "-R", "property", "Property",
             "-R", "validator", "CedarValidator"]
    coqc_log = build / f"{batch_name}.coqc.log"
    coqchk_log = build / f"{batch_name}.coqchk.log"
    try:
        stdout = run_coq(["bash", str(env_script), "coqc", *flags, source.name],
                         build, coqc_log, MAX_BATCH_SECONDS)
        run_coq(["bash", str(env_script), "coqchk", "-silent", *flags[1:], batch_name],
                build, coqchk_log, MAX_BATCH_SECONDS)
    except CoqTimeout as error:
        if not coqchk_log.exists():
            coqchk_log.write_text("not_run: earlier Coq timeout\n")
        return {
            digest: {
                "input_sha256": digest,
                "premises": {name: "unknown" for name in PREMISES},
                "overall": "unknown",
                "reason": str(error),
                "evidence": {
                    "source": str(source),
                    "coqc_log": str(coqc_log),
                    "coqchk_log": str(coqchk_log),
                    "vo": str(source.with_suffix(".vo")) if source.with_suffix(".vo").is_file() else None,
                    "sample_definition": f"sample_{index}",
                    "verdict_definitions": [f"verdict_{index}_{j}" for j in range(len(PREMISES))],
                },
                "source_fingerprint": fingerprint,
            }
            for index, (digest, _) in enumerate(items)
        }
    tags = TAG_RE.findall(stdout)
    if len(tags) != len(items) * len(PREMISES):
        raise ValidationError(f"incomplete verdict output in {coqc_log}")
    if stdout.count("Closed under the global context") != len(tags):
        raise ValidationError(f"a verdict has assumptions; see {coqc_log}")
    by_digest: dict[str, dict[str, str]] = {digest: {} for digest, _ in items}
    for digest, premise, verdict in tags:
        if digest not in by_digest or premise not in PREMISES or premise in by_digest[digest]:
            raise ValidationError(f"duplicate or unexpected verdict in {coqc_log}")
        by_digest[digest][premise] = verdict
    output = {}
    for index, (digest, _) in enumerate(items):
        statuses = by_digest[digest]
        if set(statuses) != set(PREMISES):
            raise ValidationError(f"missing verdict for {digest} in {coqc_log}")
        aggregate = ("invalid" if "invalid" in statuses.values() else
                     "valid" if all(value == "valid" for value in statuses.values()) else
                     "unknown")
        output[digest] = {
            "input_sha256": digest,
            "premises": statuses,
            "overall": aggregate,
            "evidence": {
                "source": str(source),
                "coqc_log": str(coqc_log),
                "coqchk_log": str(coqchk_log),
                "vo": str(source.with_suffix(".vo")),
                "sample_definition": f"sample_{index}",
                "verdict_definitions": [f"verdict_{index}_{j}" for j in range(len(PREMISES))],
            },
            "source_fingerprint": fingerprint,
        }
    return output


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path, help="attempts JSONL")
    parser.add_argument("--output", required=True, type=Path, help="verdicts JSONL")
    parser.add_argument("--evidence-dir", required=True, type=Path)
    parser.add_argument("--env-script", type=Path, help="pinned environment/env.sh")
    parser.add_argument("--batch-size", type=int, default=DEFAULT_BATCH_SIZE)
    parser.add_argument("--batch-workers", type=int, default=DEFAULT_BATCH_WORKERS,
                        help="concurrent independent Coq batches (1-4; default 4)")
    args = parser.parse_args()
    if args.batch_size < 1 or args.batch_size > DEFAULT_BATCH_SIZE:
        parser.error(f"batch-size must be between 1 and {DEFAULT_BATCH_SIZE}")
    if args.batch_workers < 1 or args.batch_workers > DEFAULT_BATCH_WORKERS:
        parser.error(f"batch-workers must be between 1 and {DEFAULT_BATCH_WORKERS}")
    root = Path(__file__).resolve().parents[2]
    env_script = (args.env_script or root / "environment/env.sh").resolve()
    if args.input.resolve() == args.output.resolve():
        raise ValidationError("input and output files must differ")
    if args.output.exists():
        raise ValidationError(f"refusing to overwrite prior verdict output: {args.output}")
    version_status, coq_version, version_stderr = capture_group(
        ["bash", str(env_script), "coqc", "--version"], None, 30,
    )
    if version_status:
        raise ValidationError(f"could not check pinned Coq version: {version_stderr.strip()}")
    if "version 8.20.0" not in coq_version or "OCaml 4.14.2" not in coq_version:
        raise ValidationError(f"unexpected Coq/OCaml version: {coq_version.strip()}")
    rows = []
    unique: dict[str, str] = {}
    for number, line in enumerate(args.input.read_text().splitlines(), 1):
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ValidationError(f"invalid JSON on input line {number}") from exc
        if not isinstance(row, dict) or "input_coq" not in row:
            raise ValidationError(f"input line {number} needs input_coq")
        expression = row["input_coq"]
        if expression is not None:
            check_constructor_term(expression)
            digest = sha256(expression.encode())
            if digest in unique and unique[digest] != expression:
                raise ValidationError("SHA-256 collision between input terms")
            unique[digest] = expression
        else:
            digest = None
        rows.append((row, digest))
    evidence_dir = args.evidence_dir.resolve()
    evidence_dir.mkdir(parents=True, exist_ok=True)
    build, fingerprint = prepare_build(root, evidence_dir, env_script,
                                       coq_version.strip(), args.batch_size,
                                       args.batch_workers)
    manifest = {
        "source_fingerprint": fingerprint,
        "spec_sha256": sha256((root / "specification/cedar/Spec.v").read_bytes()),
        "original_sha256": sha256((root / "properties/cedar_no_type_error/Original.v").read_bytes()),
        "validator_sha256": sha256((root / "scripts/cedar/Validator.v").read_bytes()),
        "driver_sha256": sha256(Path(__file__).read_bytes()),
        "env_script_sha256": sha256(env_script.read_bytes()),
        "proof_depth": PROOF_DEPTH,
        "tactic_timeout_seconds_each_direction": TACTIC_TIMEOUT_SECONDS,
        "batch_timeout_seconds": MAX_BATCH_SECONDS,
        "batch_size": args.batch_size,
        "batch_workers": args.batch_workers,
        "input_rows": len(rows),
        "unique_input_terms": len(unique),
        "env_script": str(env_script),
        "coq_version": coq_version.strip(),
    }
    manifest_path = evidence_dir / f"manifest-{uuid.uuid4().hex}.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    cache = evidence_dir / "cache" / fingerprint
    cache.mkdir(parents=True, exist_ok=True)
    resolved = {}
    pending = []
    for digest, expression in unique.items():
        cached = cache / f"{digest}.json"
        if cached.is_file():
            try:
                data = json.loads(cached.read_text())
            except json.JSONDecodeError as error:
                raise ValidationError(f"corrupted cache record: {cached}") from error
            if not isinstance(data, dict):
                raise ValidationError(f"corrupted cache record: {cached}")
            evidence = data.get("evidence") or {}
            premises = data.get("premises")
            if not isinstance(evidence, dict) or not isinstance(premises, dict):
                raise ValidationError(f"corrupted cache record: {cached}")
            if set(premises) != set(PREMISES) or any(
                value not in {"valid", "invalid", "unknown"} for value in premises.values()
            ):
                raise ValidationError(f"corrupted cache record: {cached}")
            expected_overall = (
                "invalid" if "invalid" in premises.values() else
                "valid" if all(value == "valid" for value in premises.values()) else
                "unknown"
            )
            if data.get("overall") != expected_overall:
                raise ValidationError(f"corrupted cache record: {cached}")
            if data.get("input_sha256") != digest:
                raise ValidationError(f"corrupted cache record: {cached}")
            required = ("source", "coqc_log", "coqchk_log")
            has_evidence = all(evidence.get(key) and Path(evidence[key]).is_file()
                               for key in required)
            timeout_unknown = (
                data.get("reason") is not None and expected_overall == "unknown" and
                all(value == "unknown" for value in premises.values())
            )
            checked_object = (
                evidence.get("vo") and Path(evidence["vo"]).is_file() and
                Path(evidence["coqc_log"] + ".ok").is_file() and
                Path(evidence["coqchk_log"] + ".ok").is_file()
            ) if has_evidence else False
            has_object = timeout_unknown or checked_object
            if data.get("source_fingerprint") == fingerprint and has_evidence and has_object:
                resolved[digest] = data
                continue
            raise ValidationError(f"stale or corrupted cache record: {cached}")
        pending.append((digest, expression))
    # Reserve distinct batch numbers before any worker can start. Workers only
    # write their own Coq source and logs; cache and JSONL writes stay here.
    numbered_batches = []
    sequence = 1
    for start in range(0, len(pending), args.batch_size):
        while True:
            batch_name = f"batch_{sequence:06d}"
            reservation = build / f"{batch_name}.reserve"
            if (build / f"{batch_name}.v").exists():
                sequence += 1
                continue
            try:
                reservation.touch(exist_ok=False)
            except FileExistsError:
                sequence += 1
                continue
            break
        numbered_batches.append((sequence, pending[start:start + args.batch_size]))
        sequence += 1
    with ThreadPoolExecutor(max_workers=args.batch_workers) as executor:
        futures = [executor.submit(validate_batch, items, build, env_script,
                                   number, fingerprint)
                   for number, items in numbered_batches]
        try:
            batch_verdicts = [future.result() for future in futures]
        except BaseException:
            for future in futures:
                future.cancel()
            raise
    for verdicts in batch_verdicts:
        for digest, data in verdicts.items():
            with (cache / f"{digest}.json").open("x") as stream:
                stream.write(json.dumps(data, sort_keys=True) + "\n")
        resolved.update(verdicts)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as stream:
        for row, digest in rows:
            result = {"id": row.get("id"), "input_sha256": digest}
            if digest is None:
                result.update({"premises": None, "overall": "no_generation", "evidence": None})
            else:
                result.update(resolved[digest])
            stream.write(json.dumps(result, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"validator: {error}", file=sys.stderr)
        raise SystemExit(2)
