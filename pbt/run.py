"""Run the even-Nat example against an explicitly supplied Python executable."""

import argparse
import json
import os
from pathlib import Path
import subprocess
from typing import NamedTuple, cast

from pbt.unparse import render_program


Sample = NamedTuple("Sample", [("index", int), ("size", int), ("seed", int), ("input", int)])
RunOptions = NamedTuple(
    "RunOptions", [("implementation", Path), ("output", Path), ("count", int), ("size", int), ("seed", int)]
)


class SampleFormatError(ValueError):
    """The Lean executable returned malformed or inconsistent sample data."""


class ExternalProcessError(RuntimeError):
    """An external executable could not complete successfully."""


class ObservationError(ValueError):
    """An external program did not produce the required numeric result."""


def natural_number(value: str) -> int:
    if not value.isdecimal():
        raise argparse.ArgumentTypeError(f"expected a natural number; received {value!r}")
    return int(value)


def parse_options(arguments: list[str]) -> RunOptions:
    parser: argparse.ArgumentParser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--implementation", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--count", type=natural_number, required=True)
    parser.add_argument("--size", type=natural_number, required=True)
    parser.add_argument("--seed", type=natural_number, required=True)
    parsed: argparse.Namespace = parser.parse_args(arguments)
    return RunOptions(parsed.implementation, parsed.output, parsed.count, parsed.size, parsed.seed)


def execute(command: tuple[str, ...], directory: Path) -> subprocess.CompletedProcess[str]:
    """The process boundary captures complete output and fails on timeout or nonzero exit."""
    try:
        result: subprocess.CompletedProcess[str] = subprocess.run(
            command, cwd=directory, capture_output=True, text=True, check=False, timeout=60
        )
    except subprocess.TimeoutExpired as error:
        raise ExternalProcessError(
            f"command timed out after 60 seconds: command={command!r}, cwd={str(directory)!r}, "
            f"stdout={error.stdout!r}, stderr={error.stderr!r}"
        ) from error
    except OSError as error:
        raise ExternalProcessError(
            f"cannot execute command={command!r}, cwd={str(directory)!r}: {error}"
        ) from error
    if result.returncode != 0:
        raise ExternalProcessError(
            f"command failed: command={command!r}, cwd={str(directory)!r}, "
            f"status={result.returncode}, stdout={result.stdout!r}, stderr={result.stderr!r}"
        )
    return result


def parse_sample(line: str) -> Sample:
    try:
        decoded: object = json.loads(line)
    except json.JSONDecodeError as error:
        raise SampleFormatError(f"sample is invalid JSON: line={line!r}; {error}") from error
    if not isinstance(decoded, dict):
        raise SampleFormatError(f"sample must be a JSON object; received {decoded!r}")
    fields: dict[str, object] = cast(dict[str, object], decoded)
    values: list[int] = []
    for field in ("index", "size", "seed", "input"):
        value: object = fields.get(field)
        if type(value) is not int or value < 0:
            raise SampleFormatError(
                f"sample field {field!r} must be a natural number; received {value!r}; line={line!r}"
            )
        values.append(value)
    sample: Sample = Sample(*values)
    if sample.input % 2 != 0 or sample.input > 2 * sample.size:
        raise SampleFormatError(f"sample violates the even-input specification or size bound: {sample!r}")
    return sample


def read_samples(root: Path, count: int, size: int, seed: int) -> tuple[Sample, ...]:
    executable: Path = root / ".lake/build/bin/example-samples"
    result: subprocess.CompletedProcess[str] = execute(
        (str(executable), str(count), str(size), str(seed)), root
    )
    samples: tuple[Sample, ...] = tuple(parse_sample(line) for line in result.stdout.splitlines())
    if len(samples) != count:
        raise SampleFormatError(f"expected {count} samples; received {len(samples)}; stdout={result.stdout!r}")
    for index, sample in enumerate(samples):
        if (sample.index, sample.size, sample.seed) != (index, size, seed + index):
            raise SampleFormatError(
                f"sample metadata mismatch: expected index={index}, size={size}, seed={seed + index}; "
                f"received {sample!r}"
            )
    return samples


def check_observation(expected: int, result: subprocess.CompletedProcess[str]) -> int:
    try:
        observed: int = int(result.stdout.strip())
    except ValueError as error:
        raise ObservationError(
            f"program must print one integer: command={result.args!r}, status={result.returncode}, "
            f"stdout={result.stdout!r}, stderr={result.stderr!r}"
        ) from error
    if observed != expected:
        raise ObservationError(
            f"property failed: expected={expected}, observed={observed}, command={result.args!r}, "
            f"status={result.returncode}, stdout={result.stdout!r}, stderr={result.stderr!r}"
        )
    return observed


def run_example(root: Path, options: RunOptions) -> tuple[Sample, ...]:
    """Write fresh replay folders and stop immediately when an external observation fails."""
    implementation: Path = options.implementation.resolve(strict=True)
    if not implementation.is_file() or not os.access(implementation, os.X_OK):
        raise ValueError(f"implementation must be an executable file: {implementation}")
    output: Path = options.output.resolve()
    cases_root: Path = (root / "test_cases").resolve(strict=True)
    if not output.is_relative_to(cases_root) or output == cases_root:
        raise ValueError(f"output must be a new directory below {cases_root}; received {output}")
    if options.count == 0:
        raise ValueError("count must be positive so the run observes at least one program")
    samples: tuple[Sample, ...] = read_samples(root, options.count, options.size, options.seed)
    programs: tuple[str, ...] = tuple(render_program(sample.input) for sample in samples)
    for sample, program in zip(samples, programs, strict=True):
        compile(program, str(output / f"case-{sample.index:06d}" / "program.py"), "exec")
    output.mkdir(parents=True, exist_ok=False)
    for sample, program in zip(samples, programs, strict=True):
        case: Path = output / f"case-{sample.index:06d}"
        case.mkdir()
        source: Path = case / "program.py"
        source.write_text(program, encoding="utf-8")
        metadata: dict[str, int] = {
            "index": sample.index, "size": sample.size, "seed": sample.seed, "input": sample.input
        }
        (case / "sample.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
        result: subprocess.CompletedProcess[str] = execute((str(implementation), str(source)), case)
        observed: int = check_observation(sample.input, result)
        (case / "observation.json").write_text(
            json.dumps({"observed": observed, "stdout": result.stdout, "stderr": result.stderr}, indent=2) + "\n",
            encoding="utf-8",
        )
    return samples


def main(arguments: list[str]) -> None:
    options: RunOptions = parse_options(arguments)
    root: Path = Path(__file__).resolve().parents[1]
    samples: tuple[Sample, ...] = run_example(root, options)
    print(f"Passed {len(samples)} external programs; replay files: {options.output.resolve()}")


if __name__ == "__main__":
    import sys

    main(sys.argv[1:])
