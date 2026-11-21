"""Real Coq regressions for the original-premise validator."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
VALIDATOR = ROOT / "scripts/cedar/validator.py"
PINNED_ENV = ROOT / "environment/env.sh"


def name(value):
    return f'(MkName "{value}" [])'


N1 = name("EntityType1")
N2 = name("EntityType2")
ENTRY = "(MkEntitySchemaEntry [] [])"
UID = f'(MkEntityUID {name("Action")} "a")'
ACT = f'(MkActionSchemaEntry [{N1}] [{N1}] [])'
ETS = f'[({N1}, {ENTRY}); ({N2}, {ENTRY})]'
ACTS = f'[({UID}, {ACT})]'
REQ = f'(MkRequest {N1} {UID} {N1} [])'
REQ2 = f'(MkRequest {N2} {UID} {N1} [])'


def input_term(*, ets=ETS, req=REQ, es="[]", ty="intType",
               expr="(lit (int 0%Z), somepaths [])"):
    schema = f'(MkSchema {ets} {ACTS})'
    env = f'(MkEnvironment {schema} {req})'
    return f'mkInput {ets} {ACTS} [{req}] {env} {es} {ty} {expr}'


class CedarValidatorTests(unittest.TestCase):
    def test_real_coq_verdicts_and_exact_input_cache(self):
        duplicate_ets = f'[({N1}, {ENTRY}); ({N1}, {ENTRY})]'
        bad3_extra = f'[(MkEnvironment (MkSchema {ETS} {ACTS}) {REQ2})]'
        terms = [
            input_term(),
            input_term(ets=duplicate_ets),
            input_term(req=REQ2),
            input_term(es=bad3_extra),
            input_term(ty=f'(entityType {name("Unknown")})'),
            input_term(expr='(lit (stringLit "s"), somepaths [])'),
            input_term(),
            None,
        ]
        scratch = ROOT / "properties/cedar_no_type_error/.runs"
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="validator-test-", dir=scratch) as directory:
            work = Path(directory)
            attempts = work / "attempts.jsonl"
            output = work / "verdicts.jsonl"
            attempts.write_text("".join(
                json.dumps({"id": number, "input_coq": term}) + "\n"
                for number, term in enumerate(terms)
            ))
            evidence_dir = work / "evidence"

            def invoke(destination, batch_size=10):
                return subprocess.run(
                    [sys.executable, str(VALIDATOR), "--input", str(attempts),
                     "--output", str(destination), "--evidence-dir", str(evidence_dir),
                     "--env-script", str(PINNED_ENV), "--batch-size", str(batch_size)],
                    text=True, capture_output=True, timeout=180,
                )

            result = invoke(output)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            rows = [json.loads(line) for line in output.read_text().splitlines()]
            self.assertEqual(len(rows), len(terms))
            for row in rows[:6]:
                self.assertEqual(set(row["premises"]), {
                    "WfSchema", "ActionSchemaToRequestTypes", "SchemaToEnvironments",
                    "WfCedarType", "HasType",
                })
                self.assertTrue(Path(row["evidence"]["source"]).is_file())
                self.assertTrue(Path(row["evidence"]["vo"]).is_file())
                self.assertTrue(Path(row["evidence"]["coqchk_log"]).is_file())
            self.assertEqual(rows[0]["overall"], "valid")
            self.assertTrue(all(v == "valid" for v in rows[0]["premises"].values()))
            for index, premise in enumerate((
                "WfSchema", "ActionSchemaToRequestTypes", "SchemaToEnvironments",
                "WfCedarType", "HasType",
            ), 1):
                self.assertEqual(rows[index]["premises"][premise], "invalid")
                self.assertEqual(rows[index]["overall"], "invalid")
            self.assertEqual(rows[0]["input_sha256"], rows[6]["input_sha256"])
            self.assertEqual(rows[0]["evidence"], rows[6]["evidence"])
            self.assertEqual(rows[7]["overall"], "no_generation")
            self.assertIsNone(rows[7]["premises"])
            self.assertEqual(len(list((evidence_dir / "cache").rglob("*.json"))), 6)

            # A rerun reuses exact-expression evidence without a new batch.
            cached_output = work / "cached.jsonl"
            before_batches = list(evidence_dir.rglob("batch_*.v"))
            cached_run = invoke(cached_output)
            self.assertEqual(cached_run.returncode, 0, cached_run.stderr)
            self.assertEqual(len(list(evidence_dir.rglob("batch_*.v"))), len(before_batches))
            self.assertEqual(cached_output.read_text(), output.read_text())

            # Existing output is protected before any Coq invocation.
            original_output = output.read_bytes()
            overwrite = invoke(output)
            self.assertEqual(overwrite.returncode, 2)
            self.assertIn("refusing to overwrite", overwrite.stderr)
            self.assertEqual(output.read_bytes(), original_output)

            # A different fixed batch bound gets a different tool fingerprint.
            changed_bound = invoke(work / "changed-bound.jsonl", batch_size=9)
            self.assertEqual(changed_bound.returncode, 0, changed_bound.stderr)
            self.assertEqual(len(list(evidence_dir.glob("build-*"))), 2)
            self.assertEqual(len(list((evidence_dir / "cache").rglob("*.json"))), 12)

            # Corrupt cache evidence is refused and preserved for inspection.
            cache_file = next(
                (evidence_dir / "cache" / rows[0]["source_fingerprint"]).glob("*.json")
            )
            cache_file.write_text("{broken JSON\n")
            corrupted = invoke(work / "corrupted.jsonl")
            self.assertEqual(corrupted.returncode, 2)
            self.assertIn("corrupted cache record", corrupted.stderr)
            self.assertEqual(cache_file.read_text(), "{broken JSON\n")

    def test_rejects_vernacular_and_tactic_injection(self):
        from importlib.util import module_from_spec, spec_from_file_location
        spec = spec_from_file_location("cedar_validator", VALIDATOR)
        module = module_from_spec(spec)
        spec.loader.exec_module(module)
        for term in (
            'mkInput [] [] [] x [] intType y. Axiom fake : False.',
            'mkInput [] [] [] x [] intType ltac:(admit)',
            'mkInput [] [] [] x [] intType (y (* hidden *))',
            'let x := mkInput [] [] [] x [] intType y in x',
        ):
            with self.subTest(term=term), self.assertRaises(module.ValidationError):
                module.check_constructor_term(term)


if __name__ == "__main__":
    unittest.main()
