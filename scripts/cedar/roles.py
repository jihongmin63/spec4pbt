#!/usr/bin/env python3
"""Fresh, filesystem-restricted Codex roles for the Cedar experiment.

Every call has a new workspace and private evidence directory.  The model is
never started unless an inherited Linux Landlock policy passes path probes.
The CLI's own bwrap sandbox is unavailable on the target host; the explicit
``--dangerously-bypass-approvals-and-sandbox`` flag applies only inside this
verified outer Landlock restriction.  A failed probe always stops the call.
"""

from __future__ import annotations

import ctypes
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import signal
import subprocess
import time
import uuid
from typing import Any, Mapping, Sequence


MODEL = "gpt-6-sol"
EFFORT = {"reformulator": "xhigh", "prover": "xhigh", "inspector": "high"}
OUTPUT = {"reformulator": "Candidate.v", "prover": "Equivalence.v", "inspector": None}
HERE = Path(__file__).resolve().parent
SCHEMA = {name: HERE / "schemas" / f"{name}.json" for name in EFFORT}
PROMPT = {name: HERE / "prompts" / f"{name}.txt" for name in EFFORT}

# Linux x86_64/aarch64 system call numbers.  Fail closed on other machines.
LANDLOCK_SYSCALLS = {"x86_64": (444, 445, 446), "aarch64": (444, 445, 446)}
READ_FILE = 1 << 2
READ_DIR = 1 << 3
EXECUTE = 1 << 0
WRITE_FILE = 1 << 1
WRITE_RIGHTS = sum(1 << bit for bit in range(4, 16)) | WRITE_FILE
READ_ACCESS = READ_FILE | READ_DIR | EXECUTE
ALL_ACCESS = READ_ACCESS | WRITE_RIGHTS
PR_SET_NO_NEW_PRIVS = 38


class RoleError(RuntimeError):
    """A role was stopped before a trustworthy result was available."""


class _PathBeneath(ctypes.Structure):
    _pack_ = 1
    _fields_ = [("allowed_access", ctypes.c_uint64), ("parent_fd", ctypes.c_int32)]


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def _real_existing(path: Path) -> Path:
    result = path.resolve(strict=True)
    if not result.is_absolute():
        raise RoleError(f"Non-absolute sandbox path: {path}")
    return result


def _landlock_abi() -> int:
    import platform

    numbers = LANDLOCK_SYSCALLS.get(platform.machine())
    if numbers is None:
        raise RoleError(f"Unsupported Landlock architecture: {platform.machine()}")
    libc = ctypes.CDLL(None, use_errno=True)
    abi = libc.syscall(numbers[0], 0, 0, 1)
    if abi < 5:
        raise RoleError(f"Landlock ABI >= 5 required; got {abi}, errno={ctypes.get_errno()}")
    return abi


def _restrict(read_paths: Sequence[Path], write_path: Path) -> None:
    """Apply a read allowlist and one writable tree to the current process."""
    import platform

    create, add, restrict = LANDLOCK_SYSCALLS[platform.machine()]
    libc = ctypes.CDLL(None, use_errno=True)
    handled = ctypes.c_uint64(ALL_ACCESS)
    ruleset = libc.syscall(create, ctypes.byref(handled), ctypes.sizeof(handled), 0)
    if ruleset < 0:
        raise OSError(ctypes.get_errno(), "landlock_create_ruleset")
    try:
        for path, access in [*( (p, READ_ACCESS) for p in read_paths), (write_path, ALL_ACCESS)]:
            path = _real_existing(path)
            if path.is_file():
                access &= READ_FILE | EXECUTE | WRITE_FILE | (1 << 14) | (1 << 15)
            fd = os.open(path, os.O_PATH | os.O_CLOEXEC)
            try:
                rule = _PathBeneath(access, fd)
                if libc.syscall(add, ruleset, 1, ctypes.byref(rule), 0) < 0:
                    raise OSError(ctypes.get_errno(), f"landlock_add_rule({path})")
            finally:
                os.close(fd)
        if libc.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) < 0:
            raise OSError(ctypes.get_errno(), "prctl(NO_NEW_PRIVS)")
        if libc.syscall(restrict, ruleset, 0) < 0:
            raise OSError(ctypes.get_errno(), "landlock_restrict_self")
    finally:
        os.close(ruleset)


def runtime_read_paths(switch: Path | None = None) -> list[Path]:
    """Resolve only operating-system runtime paths and the pinned switch."""
    paths = [Path(p) for p in ("/usr", "/lib", "/lib64", "/bin", "/sbin", "/etc",
                                "/dev") if Path(p).exists()]
    codex = shutil.which("codex")
    if codex is not None:
        executable = Path(codex).resolve(strict=True)
        paths.append(executable)
        # This CLI delegates tool execution to a separate installed binary.
        # Allow the exact runtime files, never the enclosing extension/user tree.
        for name in ("codex-code-mode-host", "rg", "codex-package.json"):
            dependency = executable.with_name(name)
            if dependency.is_file():
                paths.append(dependency)
    if switch is not None:
        prefix = _real_existing(switch)
        if prefix.name != "_opam-testing-theorems":
            raise RoleError("Expected the pinned _opam-testing-theorems switch")
        installed = prefix / "_opam"
        if not installed.is_dir():
            raise RoleError(f"Missing installed switch: {installed}")
        paths.append(installed)
    return list(dict.fromkeys(_real_existing(p) for p in paths))


def parse_usage(events: Sequence[Mapping[str, Any]], *, call_complete: bool = True) -> dict[str, Any]:
    """Sum actual completed-turn usage only; optional fields never add to totals."""
    turns = [event.get("usage") for event in events if event.get("type") == "turn.completed"]
    starts = sum(event.get("type") == "turn.started" for event in events)
    unfinished = (not call_complete or starts > len(turns) or any(
        event.get("type") in ("turn.failed", "turn.cancelled", "turn.aborted", "thread.failed")
        for event in events))
    if unfinished or not turns or any(not isinstance(item, Mapping) for item in turns):
        return {"status": "unavailable", "input_tokens": None, "output_tokens": None,
                "cached_input_tokens": None, "reasoning_output_tokens": None}
    primary = ("input_tokens", "output_tokens")
    optional = ("cached_input_tokens", "reasoning_output_tokens")
    if any(not isinstance(item.get(field), int) or item[field] < 0
           for item in turns for field in primary):
        return {"status": "unavailable", "input_tokens": None, "output_tokens": None,
                "cached_input_tokens": None, "reasoning_output_tokens": None}
    usage: dict[str, Any] = {"status": "available"}
    for field in primary:
        usage[field] = sum(item[field] for item in turns)
    for field in optional:
        usage[field] = (sum(item[field] for item in turns)
                        if all(isinstance(item.get(field), int) and item[field] >= 0
                               for item in turns) else None)
    if (usage["cached_input_tokens"] is not None
            and usage["cached_input_tokens"] > usage["input_tokens"]):
        usage["cached_input_tokens"] = None
    if (usage["reasoning_output_tokens"] is not None
            and usage["reasoning_output_tokens"] > usage["output_tokens"]):
        usage["reasoning_output_tokens"] = None
    return usage


def not_run_cost() -> dict[str, Any]:
    return {"status": "not_run", "wall_seconds": None,
            "usage": {"status": "not_run", "input_tokens": None, "output_tokens": None,
                      "cached_input_tokens": None, "reasoning_output_tokens": None}}


def _parse_events(path: Path) -> list[dict[str, Any]]:
    events = []
    if not path.exists():
        return events
    for line in path.read_text(errors="replace").splitlines():
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict):
            events.append(item)
    return events


def _copy_bundle(workspace: Path, inputs: Mapping[str, Path]) -> dict[str, str]:
    """Accept explicit relative destinations and regular source files only."""
    hashes = {}
    for relative, source in inputs.items():
        rel = Path(relative)
        if rel.is_absolute() or ".." in rel.parts or relative in ("", "."):
            raise RoleError(f"Unsafe bundle destination: {relative}")
        if set(rel.parts) & {"scratch", ".codex", ".opam", "private-evidence", "_opam-testing-theorems"}:
            raise RoleError(f"Reserved bundle destination: {relative}")
        source = Path(source)
        if source.is_symlink() or not source.is_file():
            raise RoleError(f"Bundle input must be a regular file: {source}")
        target = workspace / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        hashes[relative] = _sha(target)
    return hashes


def _source_inventory(workspace: Path) -> dict[str, str]:
    """Inventory every non-temporary workspace path, including rogue symlinks."""
    result = {}
    for path in workspace.rglob("*"):
        relative = path.relative_to(workspace)
        if relative.parts[0] in ("scratch", ".codex", ".opam", "_opam-testing-theorems") or (path.is_dir() and not path.is_symlink()):
            continue
        result[relative.as_posix()] = (f"symlink:{os.readlink(path)}" if path.is_symlink()
                                       else _sha(path) if path.is_file() else "special")
    return result


def _setup_coq_runtime(workspace: Path, source_root: Path, switch: Path) -> dict[str, str]:
    """Reuse the fixed env.sh with a private Opam root and pinned install link."""
    installed = _real_existing(switch)
    if installed.name != "_opam-testing-theorems" or not (installed / "_opam/bin/coqc").is_file():
        raise RoleError("Pinned Testing Theorems switch unavailable")
    wrapper = source_root / "environment/env.sh"
    if not wrapper.is_file() or wrapper.is_symlink():
        raise RoleError("Fixed environment/env.sh unavailable")
    target = workspace / "environment/env.sh"
    target.parent.mkdir(exist_ok=True)
    if target.exists() and _sha(target) != _sha(wrapper):
        raise RoleError("Bundled env.sh differs from fixed source")
    if not target.exists():
        shutil.copyfile(wrapper, target)
    switch_dir = workspace / "_opam-testing-theorems"
    if switch_dir.exists() or switch_dir.is_symlink():
        raise RoleError("Role bundle may not provide an installation directory")
    switch_dir.mkdir()
    local_prefix = switch_dir / "_opam"
    local_prefix.mkdir()
    for name in ("bin", "doc", "lib", "man", "sbin", "share"):
        (local_prefix / name).symlink_to(installed / "_opam" / name, target_is_directory=True)
    private_opam = workspace / ".opam"
    private_opam.mkdir()
    (private_opam / "config").write_text(
        'opam-version: "2.0"\nopam-root-version: "2.2"\n'
        f'installed-switches: [{json.dumps(str(switch_dir))}]\n'
        f'switch: {json.dumps(str(switch_dir))}\n')
    local_metadata = local_prefix / ".opam-switch"
    local_metadata.mkdir()
    installed_metadata = installed / "_opam/.opam-switch"
    for name in ("environment", "switch-state", "switch-config"):
        shutil.copyfile(installed_metadata / name, local_metadata / name)
    configuration = local_metadata / "switch-config"
    original = configuration.read_text()
    # The caller may itself run in an isolated HOME. Read the installed
    # metadata field instead of assuming that it equals the caller's HOME.
    roots = re.findall(r'^opam-root: "(?:[^"\\]|\\.)*"$', original, re.MULTILINE)
    if len(roots) != 1:
        raise RoleError("Pinned Opam switch root metadata changed unexpectedly")
    new_root = f'opam-root: {json.dumps(str(private_opam))}'
    configuration.write_text(original.replace(roots[0], new_root, 1))
    return {"env_sh_sha256": _sha(target), "opam_config_sha256": _sha(private_opam / "config"),
            "installed_switch": str(installed)}


def prepare_role(role: str, run_dir: Path, inputs: Mapping[str, Path],
                 context: Mapping[str, Any] | None = None) -> dict[str, Any]:
    """Create a new role invocation with a minimal input bundle.

    ``context`` is role-scoped structured data, never a transcript or event log.
    The caller decides which predecessor/helper files are necessary.
    """
    if role not in EFFORT:
        raise RoleError(f"Unknown role: {role}")
    names = set(inputs)
    if not any(Path(name).name == "Spec.v" for name in names):
        raise RoleError("Role input bundle is missing fixed Spec.v")
    if not any(Path(name).name == "Original.v" for name in names):
        raise RoleError("Role input bundle is missing fixed Original.v")
    if role == "prover" and "Candidate.v" not in names:
        raise RoleError("Prover input bundle requires frozen Candidate.v")
    if role == "reformulator" and "Candidate.v" in names:
        raise RoleError("Reformulator must start without a Candidate.v output")
    if any("private-evidence" in Path(name).parts or Path(name).suffix in (".jsonl", ".log")
           for name in names):
        raise RoleError("Private events/logs are not role inputs")
    if context is not None and any(token in json.dumps(context).lower()
                                   for token in ("transcript", "raw_event", "private-evidence")):
        raise RoleError("Context contains private event or transcript material")
    if context is not None and len(json.dumps(context)) > 100_000:
        raise RoleError("Role context exceeds the structured-feedback limit")
    run_dir = Path(run_dir).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    call = run_dir / "roles" / f"{role}-{uuid.uuid4().hex}"
    workspace = call / "workspace"
    evidence = call / "private-evidence"
    workspace.mkdir(parents=True)
    evidence.mkdir()
    (workspace / "scratch").mkdir()
    before = _copy_bundle(workspace, inputs)
    if context is not None:
        _json(workspace / "context.json", dict(context))
    prompt = PROMPT[role].read_text()
    (evidence / "prompt.txt").write_text(prompt)
    manifest = {"role": role, "model": MODEL, "effort": EFFORT[role],
                "call_dir": str(call), "workspace": str(workspace),
                "evidence": str(evidence), "input_sha256": before,
                "context_sha256": _sha(workspace / "context.json") if context is not None else None,
                "schema_sha256": _sha(SCHEMA[role]), "prompt_sha256": _sha(PROMPT[role])}
    _json(call / "manifest.json", manifest)
    return manifest


def probe_restriction(manifest: Mapping[str, Any], forbidden_paths: Sequence[Path],
                      read_paths: Sequence[Path]) -> dict[str, Any]:
    """Exercise direct and /proc-root forbidden reads plus forbidden writes."""
    workspace = Path(manifest["workspace"])
    evidence = Path(manifest["evidence"])
    probe = evidence / "sandbox-probe.json"
    forbidden = [str(_real_existing(Path(p))) for p in forbidden_paths]
    if not forbidden:
        raise RoleError("At least one existing forbidden path is required")
    script = r'''import json, os, pathlib, sys
forbidden = json.loads(sys.argv[1]); results = []
for path in forbidden:
    for name, target in (("direct", path), ("proc-root", "/proc/%d/root%s" % (os.getppid(), path))):
        try:
            with open(target, "rb") as stream: stream.read(1)
            results.append({"kind": name, "path": path, "blocked": False})
        except OSError as exc:
            results.append({"kind": name, "path": path, "blocked": True, "errno": exc.errno})
    try:
        with open(path, "ab") as stream: stream.write(b"")
        results.append({"kind": "write", "path": path, "blocked": False})
    except OSError as exc:
        results.append({"kind": "write", "path": path, "blocked": True, "errno": exc.errno})
allowed = pathlib.Path(sys.argv[2])
try:
    allowed.write_text("ok")
    results.append({"kind": "allowed-write", "blocked": False})
except OSError as exc:
    results.append({"kind": "allowed-write", "blocked": True, "errno": exc.errno})
print(json.dumps(results))
'''
    argv = ["python3", "-c", script, json.dumps(forbidden), str(workspace / "scratch" / "probe-ok")]
    started = time.monotonic()
    try:
        result = subprocess.run(argv, cwd=workspace, capture_output=True, text=True,
                                timeout=20, preexec_fn=lambda: _restrict(read_paths, workspace))
        parsed = json.loads(result.stdout) if result.returncode == 0 else []
        passed = (result.returncode == 0 and len(parsed) == 3 * len(forbidden) + 1
                  and all(item["blocked"] for item in parsed[:-1])
                  and not parsed[-1]["blocked"])
        report = {"status": "passed" if passed else "failed", "argv": argv[:2] + ["<probe-script>"] + argv[3:],
                  "returncode": result.returncode, "stdout": result.stdout,
                  "stderr": result.stderr, "results": parsed,
                  "wall_seconds": time.monotonic() - started,
                  "read_paths": [str(p) for p in read_paths], "write_path": str(workspace)}
    except Exception as exc:
        report = {"status": "failed", "argv": argv[:2] + ["<probe-script>"] + argv[3:],
                  "error": repr(exc), "wall_seconds": time.monotonic() - started,
                  "read_paths": [str(p) for p in read_paths], "write_path": str(workspace)}
    _json(probe, report)
    if report["status"] != "passed":
        raise RoleError(f"Filesystem restriction probe failed: {probe}")
    return report


def _run_cli_group(command: Sequence[str], prompt: str, workspace: Path,
                   evidence: Path, env: Mapping[str, str], read_paths: Sequence[Path],
                   timeout_seconds: int) -> tuple[int, str]:
    """Terminate and reap the entire CLI/tool process group on timeout."""
    with (evidence / "events.jsonl").open("w") as events, (evidence / "stderr.log").open("w") as errors:
        process = subprocess.Popen(command, cwd=workspace, stdin=subprocess.PIPE,
                                   stdout=events, stderr=errors, text=True, env=dict(env),
                                   start_new_session=True,
                                   preexec_fn=lambda: _restrict(read_paths, workspace))
        try:
            process.communicate(prompt, timeout=timeout_seconds)
            return process.returncode, "completed" if process.returncode == 0 else "failed"
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate()
            return process.returncode, "timeout"
        except BaseException:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate()
            raise


def run_role(role: str, source_root: Path, run_dir: Path, inputs: Mapping[str, Path],
             context: Mapping[str, Any] | None = None, *,
             forbidden_paths: Sequence[Path], switch: Path | None = None,
             timeout_seconds: int = 1800, probe_only: bool = False) -> dict[str, Any]:
    """Run one fresh role after verified filesystem probes.

    The caller must provide the fixed source snapshot's AGENTS.md among
    forbidden paths; additional sibling sources/evidence should be included.
    ``probe_only`` never calls the model and is useful during tool review.
    """
    source_root = _real_existing(Path(source_root))
    selected_run = Path(run_dir).resolve()
    for source in inputs.values():
        candidate = _real_existing(Path(source))
        if not (candidate.is_relative_to(source_root) or candidate.is_relative_to(selected_run)):
            raise RoleError(f"Input outside fixed snapshot and selected run: {source}")
        if "private-evidence" in candidate.parts or ".role-smoke" in candidate.parts:
            raise RoleError(f"Private evidence cannot be a role input: {source}")
    manifest = prepare_role(role, run_dir, inputs, context)
    workspace = Path(manifest["workspace"])
    evidence = Path(manifest["evidence"])
    if switch is not None:
        manifest["coq_runtime"] = _setup_coq_runtime(workspace, source_root, Path(switch))
        _json(workspace.parent / "manifest.json", manifest)
    auth = Path.home() / ".codex" / "auth.json"
    reads = runtime_read_paths(switch) + [workspace]
    # Never include source_root or the experiment parent in the read allowlist.
    if source_root in reads or any(source_root == p or p in source_root.parents
                                   for p in reads if str(p).startswith("/workspace")):
        raise RoleError("Runtime allowlist exposes source snapshot")
    forbidden = [source_root / "AGENTS.md", *forbidden_paths]
    probe = probe_restriction(manifest, forbidden, reads)
    if probe_only:
        return {"status": "probe_passed", "manifest": manifest, "probe": probe}

    command = ["codex", "--no-daemon", "exec", "--ephemeral", "--json", "--ignore-user-config",
               "-m", MODEL, "-c", f'model_reasoning_effort="{EFFORT[role]}"',
               "-C", str(workspace), "--output-schema", str(SCHEMA[role]),
               "--dangerously-bypass-approvals-and-sandbox", "-o",
               str(evidence / "last-message.json"), "-"]
    # The output schema and last-message target must be visible to the child.
    # Copy schema into workspace; events go to inherited stdout owned by the
    # harness and therefore remain in private evidence outside model access.
    shutil.copyfile(SCHEMA[role], workspace / "result-schema.json")
    command[command.index(str(SCHEMA[role]))] = str(workspace / "result-schema.json")
    command[command.index(str(evidence / "last-message.json"))] = str(workspace / "scratch" / "last-message.json")
    env = _cli_env(workspace, auth, switch)
    before = _source_inventory(workspace)
    started = time.monotonic()
    try:
        returncode, execution_status = _run_cli_group(
            command, PROMPT[role].read_text() + "\nRead context.json and the supplied source files.\n",
            workspace, evidence, env, reads, timeout_seconds)
    finally:
        _clear_private_auth(workspace)
    wall = time.monotonic() - started
    after = _source_inventory(workspace)
    changed = sorted(key for key in before.keys() | after.keys() if before.get(key) != after.get(key))
    events = _parse_events(evidence / "events.jsonl")
    cost = {"status": "measured", "wall_seconds": wall,
            "usage": parse_usage(events, call_complete=execution_status == "completed")}
    last = workspace / "scratch" / "last-message.json"
    if last.is_file():
        shutil.copyfile(last, evidence / "last-message.json")
        try:
            answer = json.loads(last.read_text())
        except json.JSONDecodeError:
            answer = None
    else:
        answer = None
    outcome = answer.get("status") if isinstance(answer, dict) else None
    if role == "reformulator":
        accepted_change = (outcome == "candidate" and changed == ["Candidate.v"]
                           or outcome == "no_candidate" and not changed)
    elif role == "prover":
        accepted_change = (outcome == "proved" and changed == ["Equivalence.v"]
                           or outcome == "failed" and not changed)
    else:
        accepted_change = outcome in ("passed", "failed") and not changed
    status = "accepted" if execution_status == "completed" and accepted_change else "rejected"
    if role == "reformulator" and outcome == "no_candidate" and status == "accepted":
        status = "no_candidate"
    report = {"status": status, "execution_status": execution_status,
              "returncode": returncode, "cost": cost, "changed_source_files": changed,
              "answer": answer, "manifest": manifest,
              "evidence": {"events": str(evidence / "events.jsonl"),
                           "stderr": str(evidence / "stderr.log"),
                           "last_message": str(evidence / "last-message.json")},
              "command": command, "sandbox": {"kind": "Landlock", "probe": str(evidence / "sandbox-probe.json")}}
    _json(evidence / "result.json", report)
    return report


def _cli_env(workspace: Path, auth: Path, switch: Path | None) -> dict[str, str]:
    env = {key: value for key, value in os.environ.items()
           if key in ("PATH", "LANG", "LC_ALL", "SSL_CERT_FILE", "SSL_CERT_DIR",
                      "HTTPS_PROXY", "HTTP_PROXY", "NO_PROXY")}
    env["HOME"] = str(workspace)
    env["TMPDIR"] = str(workspace / "scratch")
    if (workspace / ".opam/config").is_file():
        env["OPAMROOT"] = str(workspace / ".opam")
    codex_home = workspace / ".codex"
    codex_home.mkdir(exist_ok=True)
    if not auth.is_file():
        raise RoleError("Codex authentication file unavailable")
    private_auth = codex_home / "auth.json"
    shutil.copyfile(auth, private_auth)
    private_auth.chmod(0o600)
    env["CODEX_HOME"] = str(codex_home)
    if switch is not None:
        env["PATH"] = str(_real_existing(Path(switch)) / "_opam" / "bin") + os.pathsep + env.get("PATH", "/usr/bin:/bin")
    return env


def _clear_private_auth(workspace: Path) -> None:
    (workspace / ".codex" / "auth.json").unlink(missing_ok=True)


def smoke_cli(source_root: Path, run_dir: Path, *, timeout_seconds: int = 180) -> dict[str, Any]:
    """One non-experimental CLI smoke call that must execute a real command.

    The exact model and high effort are fixed. A failed restriction probe
    prevents invocation. A reply alone cannot pass: its command must create
    the expected scratch marker. Raw events and stderr stay private.
    """
    source_root = _real_existing(Path(source_root))
    call = Path(run_dir).resolve() / "harness-smoke" / uuid.uuid4().hex
    workspace = call / "workspace"
    evidence = call / "private-evidence"
    (workspace / "scratch").mkdir(parents=True)
    evidence.mkdir()
    manifest = {"role": "harness_smoke", "model": MODEL, "effort": "high",
                "workspace": str(workspace), "evidence": str(evidence)}
    _json(call / "manifest.json", manifest)
    auth = Path.home() / ".codex" / "auth.json"
    reads = runtime_read_paths() + [workspace]
    probe_restriction(manifest, [source_root / "AGENTS.md"], reads)
    schema = {"type": "object", "additionalProperties": False,
              "required": ["ok"], "properties": {"ok": {"type": "boolean", "const": True}}}
    _json(workspace / "smoke-schema.json", schema)
    marker = workspace / "scratch" / "cli-command-probe"
    prompt = """Use your command execution tool to run this command in the current
workspace: python3 -c "from pathlib import Path; Path('scratch/cli-command-probe').write_text('ok')"
After that command succeeds, return {"ok":true}. Do not read other files."""
    (evidence / "prompt.txt").write_text(prompt + "\n")
    command = ["codex", "--no-daemon", "exec", "--ephemeral", "--json", "--ignore-user-config",
               "-m", MODEL, "-c", 'model_reasoning_effort="high"', "-C", str(workspace),
               "--output-schema", str(workspace / "smoke-schema.json"),
               "--dangerously-bypass-approvals-and-sandbox", "-o",
               str(workspace / "scratch" / "last-message.json"), "-"]
    started = time.monotonic()
    try:
        returncode, execution_status = _run_cli_group(
            command, prompt, workspace, evidence, _cli_env(workspace, auth, None),
            reads, timeout_seconds)
    finally:
        _clear_private_auth(workspace)
    last = workspace / "scratch" / "last-message.json"
    if last.is_file():
        shutil.copyfile(last, evidence / "last-message.json")
        try:
            answer = json.loads(last.read_text())
        except json.JSONDecodeError:
            answer = None
    else:
        answer = None
    command_executed = marker.is_file() and marker.read_text() == "ok"
    report = {"status": "passed" if execution_status == "completed" and answer == {"ok": True}
              and command_executed else "failed",
              "command_executed": command_executed,
              "execution_status": execution_status, "returncode": returncode,
              "wall_seconds": time.monotonic() - started,
              "usage": parse_usage(_parse_events(evidence / "events.jsonl"),
                                   call_complete=execution_status == "completed"),
              "answer": answer, "command": command,
              "sandbox": {"kind": "Landlock", "probe": str(evidence / "sandbox-probe.json")},
              "evidence": {"events": str(evidence / "events.jsonl"),
                           "stderr": str(evidence / "stderr.log"),
                           "last_message": str(evidence / "last-message.json")}}
    _json(evidence / "result.json", report)
    return report
