"""Compare actual hs-to-rocq output with the unchanged native Haskell generator.

Run after bootstrap.sh and translate.sh with GENERATOR_HASKELL_ROCQ=/path/to/coqc
python3 -m unittest scripts.tests.test_generator_haskell_translation -v.
Rocq VM evaluation checks finite examples, not soundness or completeness proofs.
"""

from __future__ import annotations

import ast
import json
import os
from pathlib import Path
import re
import subprocess
from typing import cast
import unittest

from scripts.tests.generator_contract import inspect_record
from scripts.toolchain import PROJECT


ROCQ: str | None = os.environ.get("GENERATOR_HASKELL_ROCQ")
EXPERIMENT: Path = PROJECT / "experiments/generator-haskell"
BUILD: Path = PROJECT / "build/generator-haskell"
TRANSLATED: Path = BUILD / "translated"
BASE: Path = BUILD / "hs-to-rocq-5e6a7bddfa02b818a9e8490ed107b11bd52a84e4/examples/rocq9.0/base"
GHC: Path = BUILD / "ghc-9.10.3-x86_64-unknown-linux/bin/ghc"


def flatten(expression: object) -> tuple[int, ...]:
    """Encode the already independently validated JSON AST without losing fields."""
    if not isinstance(expression, list) or not expression:
        raise ValueError(f"Expected a nonempty AST array: {expression!r}")
    values = cast(list[object], expression)
    tag = values[0]
    if tag in ("int", "var"):
        return (1 if tag == "int" else 3, cast(int, values[1]))
    if tag == "bool":
        return (2, int(cast(bool, values[1])))
    if tag in ("neg", "not"):
        return (4 if tag == "neg" else 5, *flatten(values[1]))
    if tag in ("add", "eq"):
        return (6 if tag == "add" else 7, *flatten(values[1]), *flatten(values[2]))
    if tag == "if":
        return (8, *flatten(values[1]), *flatten(values[2]), *flatten(values[3]))
    if tag == "let":
        return (9, 0 if values[1] == "int" else 1,
                *flatten(values[2]), *flatten(values[3]))
    raise ValueError(f"Unknown AST constructor: {tag!r}")


def native_pairs(expression: str) -> tuple[tuple[int, int], ...]:
    """Evaluate private original functions in their real GHC module context."""
    result = subprocess.run(
        [str(GHC), "-i" + str(EXPERIMENT / "original"),
         str(EXPERIMENT / "original/Generator.hs"), "-e", expression],
        cwd=PROJECT, check=True, capture_output=True, text=True, timeout=120,
    )
    values: object = ast.literal_eval(result.stdout)
    if not isinstance(values, list) or any(
        not isinstance(pair, tuple) or len(pair) != 2
        or any(type(value) is not int for value in pair) for pair in values
    ):
        raise ValueError(f"Expected native integer pairs, received {result.stdout!r}")
    return tuple(cast(list[tuple[int, int]], values))


@unittest.skipUnless(ROCQ is not None, "Set GENERATOR_HASKELL_ROCQ for real translation checks")
class GeneratorHaskellTranslationTests(unittest.TestCase):
    def test_native_asts_rng_and_digests_match_rocq_vm(self) -> None:
        if ROCQ is None:
            raise RuntimeError("GENERATOR_HASKELL_ROCQ must name coqc")
        if not (TRANSLATED / "Generator.vo").is_file():
            raise FileNotFoundError("Compile the actual translation with experiments/generator-haskell/translate.sh first")
        output: Path = BUILD / "checks"
        output.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            [str(GHC), "-O2", "-Wall", "-Werror", "-fforce-recomp",
             "-i" + str(EXPERIMENT / "original"), "-outputdir", str(output),
             str(EXPERIMENT / "original/Sample.hs"), "-o", str(output / "original-sample")],
            cwd=PROJECT, check=True, capture_output=True, text=True, timeout=180,
        )
        statements: list[str] = [
            "From Stdlib Require Import ZArith NArith List Bool.",
            "Require Import Generator Word64Bridge.",
            "Import ListNotations. Open Scope Z_scope.",
            "Fixpoint flatten (e : Generator.Expr) : list Z := match e with",
            "| Generator.EIntLiteral n => [1; n]",
            "| Generator.EBoolLiteral b => [2; if b then 1 else 0]",
            "| Generator.EVariable n => [3; n]",
            "| Generator.ENegate e => 4 :: flatten e",
            "| Generator.ENot e => 5 :: flatten e",
            "| Generator.EAdd a b => 6 :: (flatten a ++ flatten b)",
            "| Generator.EEqual a b => 7 :: (flatten a ++ flatten b)",
            "| Generator.EIf c a b => 8 :: (flatten c ++ flatten a ++ flatten b)",
            "| Generator.ELet t a b => 9 :: (match t with Generator.IntType => 0 | Generator.BoolType => 1 end) :: (flatten a ++ flatten b)",
            "end.",
        ]
        samples_checked: int = 0
        evaluations: int = 0
        for nodes in (1, 2, 3, 4, 16, 64, 256, 1024):
            for seed in (17, 2026):
                result = subprocess.run(
                    [str(output / "original-sample"), "4", str(nodes), str(seed)],
                    cwd=PROJECT, check=True, capture_output=True, text=True, timeout=30,
                )
                records: tuple[object, ...] = tuple(json.loads(line) for line in result.stdout.splitlines())
                self.assertEqual(len(records), 4)
                for index, record in enumerate(records):
                    inspected = inspect_record(record, index, nodes)
                    encoded = flatten(cast(dict[str, object], record)["expr"])
                    expected: str = "; ".join(str(value) for value in encoded)
                    call: str = f"Generator.generateSample {index}%Z {nodes}%Z {seed}%N"
                    statements.append(
                        f"Eval vm_compute in match {call} with Some e => "
                        f"if List.list_eq_dec Z.eq_dec (flatten e) [{expected}] then true else false | None => false end."
                    )
                    statements.append(
                        f"Eval vm_compute in match {call} with Some e => "
                        "let '(n, d) := Generator.inspectExpr e in "
                        f"andb (Z.eqb n {nodes}%Z) (N.eqb d {inspected.digest}%N) | None => false end."
                    )
                    samples_checked += 1
                    evaluations += 2
        seeds: tuple[int, ...] = (0, 1, 4294967295, 9223372036854775808, 18446744073709551615)
        seed_list: str = ",".join(str(seed) for seed in seeds)
        for seed, (value, next_state) in zip(seeds, native_pairs(f"map nextWord [{seed_list}]"), strict=True):
            statements.append(
                f"Eval vm_compute in let '(v, s) := Generator.nextWord {seed}%N in "
                f"andb (N.eqb v {value}%N) (N.eqb s {next_state}%N)."
            )
            evaluations += 1
        for bound in (1, 2, 4, 256, 1023):
            for seed, (value, next_state) in zip(seeds, native_pairs(f"map (choose {bound}) [{seed_list}]"), strict=True):
                statements.append(
                    f"Eval vm_compute in let '(v, s) := Generator.choose {bound}%Z {seed}%N in "
                    f"andb (Z.eqb v {value}%Z) (N.eqb s {next_state}%N)."
                )
                evaluations += 1
        for declaration in ("Generator.generateSample", "Generator.generate", "Generator.inspectExpr", "Generator.nextWord",
                            "Word64Bridge.add", "Word64Bridge.multiply"):
            statements.append(f"Print Assumptions {declaration}.")
        checks: Path = output / "Checks.v"
        checks.write_text("\n".join(statements) + "\n")
        log: Path = output / "rocq.log"
        with log.open("w") as stream:
            checked = subprocess.run(
                [ROCQ, "-time", "-Q", str(BASE), "", "-Q", str(TRANSLATED), "", str(checks)],
                cwd=PROJECT, check=False, stdout=stream, stderr=subprocess.STDOUT, text=True, timeout=300,
            )
        transcript: str = log.read_text()
        self.assertEqual(checked.returncode, 0, transcript)
        self.assertEqual(len(re.findall(r"= true\s+: bool", transcript)), evaluations, transcript)
        self.assertNotIn("Axioms:", transcript)
        self.assertEqual(transcript.count("Closed under the global context"), 6, transcript)
        (output / "result.json").write_text(json.dumps({
            "native_asts_and_digests_checked": samples_checked,
            "primitive_cases_checked": evaluations - 2 * samples_checked,
            "rocq_vm_checks_passed": evaluations,
            "closed_assumption_reports": 6,
        }, indent=2) + "\n")


if __name__ == "__main__":
    unittest.main()
