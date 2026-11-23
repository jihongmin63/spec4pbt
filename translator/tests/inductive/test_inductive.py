"""End-to-end checks for direct relation emission from a real AL fixture."""
from pathlib import Path
import json
import os
import importlib.util
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / "translator/tests/inductive/simple.watsup"


def direct_source(source):
    return "".join(path.read_text() for path in sorted(
        (source / "Generated").glob("InductiveRelations_*.v")))


class DirectRelationTests(unittest.TestCase):

    def test_emits_distinct_relation_and_call_continuation(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        self.assertTrue(backend.is_relative_to(ROOT / "_opam-testing-theorems"))
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "fixture", "--input", str(SOURCE),
                   "--output", str(source), "--manifest", str(run / "manifest.json"),
                   "--inductive-relations"]
        result = subprocess.run(command, cwd=run, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        generated = direct_source(source)
        self.assertIn("g_fixture_rel_Identity_execute :", generated)
        self.assertIn("g_fixture_rel_Called_execute", generated)
        self.assertIn("g_fixture_rel_Called_after_call_1_at_1", generated)
        self.assertIn("g_fixture_rel_Called_after_call_1_at_1 : nat -> Outcome (nat)", generated)
        self.assertIn("g_fixture_rel_Called_continue_from_2", generated)
        self.assertIn("g_fixture_dec_error_execute", generated)
        self.assertIn("g_fixture_dec_sink_execute", generated)
        self.assertIn("g_fixture_dec_fallback_after_call_1_at_1", generated)
        self.assertIn("g_fixture_dec_wraperror_after_call_1_at_1", generated)
        self.assertIn("g_fixture_rel_Negated_after_call_1_at_1", generated)
        self.assertIn("g_fixture_dec_arbitrary_execute", generated)
        self.assertNotIn("Eval ", generated)
        call_rule = next(line for line in generated.splitlines()
                         if "g_fixture_rel_Called_execute" in line
                         and "g_fixture_rel_Identity_execute" in line)
        self.assertEqual(call_rule.count("g_fixture_rel_Identity_execute"), 1)
        self.assertEqual(call_rule.count("g_fixture_rel_Called_after_call_1_at_1"), 1)
        manifest = json.loads((run / "manifest.json").read_text())
        self.assertEqual(manifest["status"], "coq-generated")
        spec = importlib.util.spec_from_file_location("translate_driver", ROOT / "scripts/translate.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        compiled = {"commands": []}
        driver.compile_generated(source, "fixture", run, compiled)
        (run / "compile-report.json").write_text(json.dumps(compiled, indent=2) + "\n")
        for name in ["EvalFacts", "InductiveChecks"]:
            destination = source / f"{name}.v"
            shutil.copy2(SOURCE.parent / f"{name}.v", destination)
            command = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                       "-Q", str(run / "support"), "ALCoq",
                       "-Q", str(source), "FixtureSpec", str(destination)]
            result = subprocess.run(command, cwd=run, text=True, capture_output=True)
            (run / f"{name}.log").write_text(result.stdout + result.stderr)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        proof_log = (run / "InductiveChecks.log").read_text()
        self.assertEqual(proof_log.count("Closed under the global context"), 9)
        self.assertNotIn("Axioms:", proof_log)

    def test_fresh_state_is_carried_into_next_clause(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive-fresh.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "p4", "--input", str(SOURCE.parent / "fresh.watsup"),
                   "--output", str(source), "--manifest", str(run / "manifest.json"),
                   "--inductive-relations"]
        result = subprocess.run(command, cwd=run, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        generated = direct_source(source)
        self.assertIn("g_p4_rel_Paths_continue_from_2", generated)
        spec = importlib.util.spec_from_file_location("translate_driver_fresh", ROOT / "scripts/translate.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        compiled = {"commands": []}
        driver.compile_generated(source, "p4", run, compiled)
        (run / "compile-report.json").write_text(json.dumps(compiled, indent=2) + "\n")
        destination = source / "FreshChecks.v"
        shutil.copy2(SOURCE.parent / "FreshChecks.v", destination)
        command = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                   "-Q", str(run / "support"), "ALCoq",
                   "-Q", str(source), "P4Spec", str(destination)]
        result = subprocess.run(command, cwd=run, text=True, capture_output=True)
        (run / "FreshChecks.log").write_text(result.stdout + result.stderr)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((run / "FreshChecks.log").read_text().count(
            "Closed under the global context"), 3)


    def test_polymorphic_and_higher_order_calls_are_equivalent(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive-higher.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "fixture", "--input", str(SOURCE.parent / "higher_order.watsup"),
                   "--output", str(source), "--manifest", str(run / "manifest.json"),
                   "--inductive-relations"]
        result = subprocess.run(command, cwd=run, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        generated = direct_source(source)
        self.assertIn("Inductive R_apply", generated)
        self.assertIn("g_fixture_dec_poly_x5f_identity_execute", generated)
        self.assertNotIn("Eval ", generated)
        spec = importlib.util.spec_from_file_location("translate_driver_higher", ROOT / "scripts/translate.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        driver.compile_generated(source, "fixture", run, {"commands": []})
        for name in ["EvalFacts", "HigherOrderChecks"]:
            destination = source / f"{name}.v"
            shutil.copy2(SOURCE.parent / f"{name}.v", destination)
            proof = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                     "-Q", str(run / "support"), "ALCoq",
                     "-Q", str(source), "FixtureSpec", str(destination)]
            checked = subprocess.run(proof, cwd=run, text=True, capture_output=True)
            (run / f"{name}.log").write_text(checked.stdout + checked.stderr)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertEqual((run / "HigherOrderChecks.log").read_text().count(
            "Closed under the global context"), 2)



if __name__ == "__main__":
    unittest.main(argv=[__import__("sys").argv[0]])
