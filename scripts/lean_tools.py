"""Small subprocess and identifier boundary for the native Lean tools."""

from pathlib import Path
import math
import json
import sys
import re
import subprocess
import tempfile

from scripts.toolchain import SCRATCH_DIRECTORY


IDENTIFIER = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*\Z")


def require_name(value: str) -> str:
    """Accept dotted ordinary Lean names without accepting Lean source commands."""
    if IDENTIFIER.fullmatch(value) is None:
        raise ValueError(f"Expected a dotted Lean identifier, received {value!r}")
    return value


def require_timeout(timeout_seconds: float) -> float:
    """Require a finite, positive subprocess deadline in seconds."""
    if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
        raise ValueError(f"--timeout-seconds must be finite and positive, received {timeout_seconds!r}")
    return timeout_seconds


def timeout_output(output: str | bytes | None) -> str:
    """Preserve the partial output carried by subprocess.TimeoutExpired."""
    if output is None:
        return ""
    if isinstance(output, bytes):
        return repr(output)
    return output


def run_checked(command: list[str], project: Path, timeout_seconds: float) -> str:
    """Run a local tool and preserve complete diagnostics on failure."""
    try:
        result = subprocess.run(
            command, cwd=project, capture_output=True, text=True, check=False,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as error:
        raise TimeoutError(
            f"Command timed out: {command!r}\nWorking directory: {project}\n"
            f"Timeout seconds: {timeout_seconds}\n"
            f"stdout:\n{timeout_output(error.stdout)}\nstderr:\n{timeout_output(error.stderr)}"
        ) from error
    if result.returncode != 0:
        raise ChildProcessError(
            f"Command failed: {command!r}\nWorking directory: {project}\n"
            f"Exit status: {result.returncode}\nstdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result.stdout


def elaborate(project: Path, source: str, timeout_seconds: float) -> str:
    """Elaborate a temporary command module using the project's native Lake environment."""
    scratch = project / SCRATCH_DIRECTORY
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="spec4pbt-", dir=scratch) as directory:
        path = Path(directory) / "Check.lean"
        path.write_text(source, encoding="utf-8")
        return run_checked(["lake", "env", "lean", str(path)], project, timeout_seconds)


def rebuild_modules(project: Path, modules: list[str], timeout_seconds: float) -> None:
    """Ask Lake to refresh each named module and its source dependency closure."""
    run_checked(["lake", "build", *modules], project, timeout_seconds)


def fingerprint_dependencies(project: Path, roots: list[Path], timeout: float,
                             *, dependency_graph: dict | None = None) -> dict[str, str]:
    """Resolve the same complete Lean closure with one Lake environment startup."""
    project = Path(project).resolve()
    timeout = require_timeout(timeout)
    worker = Path(__file__).resolve().with_name('_lean_dependencies.py')
    result = json.loads(run_checked(
        ['lake', 'env', sys.executable, str(worker), str(project), str(timeout),
         *[str(Path(root).resolve()) for root in roots]], project, timeout))
    if dependency_graph is not None:
        dependency_graph.update(result['graph'])
    return result['fingerprints']
