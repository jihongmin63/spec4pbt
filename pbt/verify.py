"""Check an exact Lean declaration type and reject every transitive axiom."""

import argparse
from pathlib import Path
import sys

from pbt.lean_tools import elaborate, rebuild_modules, require_name, require_timeout


def verify_proof(project: Path, module: str, proof: str, expected_type: str, timeout_seconds: float) -> None:
    """Rebuild the declaration's source closure, then check its type and axioms."""
    timeout_seconds = require_timeout(timeout_seconds)
    module = require_name(module)
    proof = require_name(proof)
    if not expected_type.strip():
        raise ValueError("--expected-type must contain a complete Lean type")
    rebuild_modules(project, ["pbt.GoalTools", module], timeout_seconds)
    source = (
        f"import pbt.GoalTools\nimport {module}\n"
        f"#spec4pbt_verify {proof} in_module {module} : (\n{expected_type}\n)\n"
    )
    print(elaborate(project, source, timeout_seconds), end="")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", required=True)
    parser.add_argument("--proof", required=True)
    parser.add_argument("--expected-type", required=True)
    parser.add_argument("--timeout-seconds", required=True, type=float)
    arguments = parser.parse_args()
    verify_proof(Path.cwd(), arguments.module, arguments.proof, arguments.expected_type, arguments.timeout_seconds)


if __name__ == "__main__":
    try:
        main()
    except (ChildProcessError, TimeoutError, ValueError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
