"""Native compatibility checks for the Haskell translation experiment.

Run with GENERATOR_HASKELL_GHC=/path/to/ghc python3 -m unittest
scripts.tests.test_generator_haskell -v. Builds stay below build/scratch.
The unchanged original and the adapted source must emit identical ASTs;
the shared checker independently validates typing, scope, size, and digest.
These finite execution checks are not correctness or translation proofs.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import NamedTuple, cast
import unittest

from scripts.tests import FIXTURES
from scripts.tests.generator_contract import fold_digest, inspect_record
from scripts.toolchain import PROJECT, SCRATCH_DIRECTORY


EXPERIMENT: Path = PROJECT / "experiments" / "generator-haskell"
GHC: str | None = os.environ.get("GENERATOR_HASKELL_GHC")
Reference = NamedTuple("Reference", [("nodes", int), ("seed", int), ("count", int),
                                    ("total_nodes", int), ("checksum", int)])


def references() -> tuple[Reference, ...]:
    document: object = json.loads((FIXTURES / "generator_reference.json").read_text())
    if not isinstance(document, dict) or not isinstance(document.get("cases"), list):
        raise ValueError("generator_reference.json requires a cases array")
    cases = cast(list[object], document["cases"])
    result: list[Reference] = []
    for case in cases:
        if not isinstance(case, dict) or any(type(case.get(field)) is not int
                                             for field in Reference._fields):
            raise ValueError(f"reference requires integer fields {Reference._fields}: {case!r}")
        fields = cast(dict[str, int], case)
        result.append(Reference(*(fields[field] for field in Reference._fields)))
    return tuple(result)


def samples(executable: Path, case: Reference) -> tuple[object, ...]:
    result = subprocess.run([str(executable), str(case.count), str(case.nodes), str(case.seed)],
                            cwd=PROJECT, capture_output=True, text=True, check=True, timeout=30)
    return tuple(json.loads(line) for line in result.stdout.splitlines())


@unittest.skipUnless(GHC is not None, "Set GENERATOR_HASKELL_GHC to run native Haskell checks")
class GeneratorHaskellTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if GHC is None:
            raise RuntimeError("GENERATOR_HASKELL_GHC must name the Haskell compiler")
        scratch: Path = PROJECT / SCRATCH_DIRECTORY
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="generator-haskell-", dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.directory = Path(cls.temporary.name)
        for variant in ("original", "src"):
            output: Path = cls.directory / variant
            output.mkdir()
            command: list[str] = [GHC, "-O2", "-Wall", "-Werror", "-fforce-recomp",
                                  "-i" + str(EXPERIMENT / variant),
                                  "-i" + str(EXPERIMENT / "original"),
                                  "-outputdir", str(output), "-o", str(output / "sample"),
                                  str(EXPERIMENT / variant / "Sample.hs")]
            compiled = subprocess.run(command, cwd=PROJECT, capture_output=True, text=True,
                                      check=False, timeout=120)
            if compiled.returncode != 0:
                raise RuntimeError(f"Haskell build failed with status {compiled.returncode}: "
                                   f"{command!r}\n{compiled.stdout}\n{compiled.stderr}")

    def test_seeded_asts_and_checksums_match_original_and_shared_reference(self) -> None:
        for case in references():
            with self.subTest(nodes=case.nodes, seed=case.seed):
                original: tuple[object, ...] = samples(self.directory / "original/sample", case)
                adapted: tuple[object, ...] = samples(self.directory / "src/sample", case)
                self.assertEqual(len(original), case.count)
                self.assertEqual(len(adapted), case.count)
                digests: list[int] = []
                total_nodes: int = 0
                for index, (old, new) in enumerate(zip(original, adapted, strict=True)):
                    checked = inspect_record(new, index, case.nodes)
                    inspect_record(old, index, case.nodes)
                    old_record = cast(dict[str, object], old)
                    new_record = cast(dict[str, object], new)
                    self.assertEqual(new_record["expr"], old_record["expr"])
                    self.assertEqual(new_record["nodes"], checked.nodes)
                    self.assertEqual(new_record["digest"], checked.digest)
                    total_nodes += checked.nodes
                    digests.append(checked.digest)
                self.assertEqual(total_nodes, case.total_nodes)
                self.assertEqual(fold_digest(tuple(digests)), case.checksum)

    def test_exhausted_fuel_and_nonpositive_sizes_return_nothing(self) -> None:
        if GHC is None:
            raise RuntimeError("GENERATOR_HASKELL_GHC must name the Haskell compiler")
        expression: str = ("print [fmap (inspectExpr . fst) (generate [] IntType [] 1 17), "
                           "fmap (inspectExpr . fst) (generate [()] IntType [] 2 17), "
                           "fmap inspectExpr (generateSample 0 0 17), "
                           "fmap inspectExpr (generateSample 0 (-1) 17)]")
        result = subprocess.run([GHC, "-i" + str(EXPERIMENT / "src"),
                                 "-outputdir", str(self.directory / "src"),
                                 str(EXPERIMENT / "src/Generator.hs"), "-e", expression],
                                cwd=PROJECT, capture_output=True, text=True,
                                check=True, timeout=30)
        self.assertEqual(result.stdout, "[Nothing,Nothing,Nothing,Nothing]\n")


if __name__ == "__main__":
    unittest.main()
