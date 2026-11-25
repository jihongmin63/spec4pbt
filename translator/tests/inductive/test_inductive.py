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
    def test_traverse_emits_recursive_relation(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive-traverse.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "fixture", "--input", str(SOURCE.parent / "traverse.watsup"),
                   "--output", str(run / "spec"), "--manifest", str(run / "manifest.json")]
        result = subprocess.run(command, cwd=run, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        generated = direct_source(run / "spec")
        self.assertIn("g_fixture_dec_each_traverse_1_at_1", generated)
        self.assertNotIn("Eval ", generated)
        spec = importlib.util.spec_from_file_location("translate_driver_traverse", ROOT / "scripts/translate.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        compiled = {"commands": []}
        driver.compile_generated(run / "spec", "fixture", run, compiled)
        (run / "compile-report.json").write_text(json.dumps(compiled, indent=2) + "\n")
        for name in ["TraverseChecks"]:
            destination = run / "spec" / f"{name}.v"
            shutil.copy2(SOURCE.parent / f"{name}.v", destination)
            proof = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                     "-Q", str(run / "support"), "ALCoq",
                     "-Q", str(run / "spec"), "FixtureSpec", str(destination)]
            checked = subprocess.run(proof, cwd=run, text=True, capture_output=True)
            (run / f"{name}.log").write_text(checked.stdout + checked.stderr)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertIn("Closed under the global context", (run / "TraverseChecks.log").read_text())

    def test_emits_distinct_relation_and_call_continuation(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        self.assertTrue(backend.is_relative_to(ROOT / "_opam-testing-theorems"))
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "fixture", "--input", str(SOURCE),
                   "--output", str(source), "--manifest", str(run / "manifest.json")]
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
        self.assertIn("InductiveRelations", (source / "Spec.v").read_text())
        self.assertNotIn("Eval ", (source / "Generated/Relations_0000.v").read_text())
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
        for name in ["InductiveChecks"]:
            destination = source / f"{name}.v"
            shutil.copy2(SOURCE.parent / f"{name}.v", destination)
            command = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                       "-Q", str(run / "support"), "ALCoq",
                       "-Q", str(source), "FixtureSpec", str(destination)]
            result = subprocess.run(command, cwd=run, text=True, capture_output=True)
            (run / f"{name}.log").write_text(result.stdout + result.stderr)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        proof_log = (run / "InductiveChecks.log").read_text()
        self.assertEqual(proof_log.count("Closed under the global context"), 11)
        self.assertNotIn("Axioms:", proof_log)

    def test_negation_and_mutual_calls_propagate_outcomes(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive-control.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "fixture", "--input", str(SOURCE.parent / "control.watsup"),
                   "--output", str(source), "--manifest", str(run / "manifest.json")]
        result = subprocess.run(command, cwd=run, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        generated = direct_source(source)
        self.assertIn("with g_fixture_dec_right_execute", generated)
        self.assertIn("g_fixture_rel_Refuted_after_call_1_at_1", generated)
        self.assertIn("g_fixture_rel_Shielded_continue_from_2", generated)
        self.assertNotIn("Eval ", generated)
        spec = importlib.util.spec_from_file_location("translate_driver_control", ROOT / "scripts/translate.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        driver.compile_generated(source, "fixture", run, {"commands": []})
        destination = source / "ControlChecks.v"
        shutil.copy2(SOURCE.parent / destination.name, destination)
        proof = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                 "-Q", str(run / "support"), "ALCoq",
                 "-Q", str(source), "FixtureSpec", str(destination)]
        checked = subprocess.run(proof, cwd=run, text=True, capture_output=True)
        (run / "ControlChecks.log").write_text(checked.stdout + checked.stderr)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertEqual(checked.stdout.count("Closed under the global context"), 6)
        self.assertNotIn("Axioms:", checked.stdout)

    def test_fresh_state_is_carried_into_next_clause(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive-fresh.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "p4", "--input", str(SOURCE.parent / "fresh.watsup"),
                   "--output", str(source), "--manifest", str(run / "manifest.json")]
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
        generation = source / "FreshGeneration.v"
        shutil.copy2(SOURCE.parent / generation.name, generation)
        proof = command[:-1] + [str(generation)]
        derived = subprocess.run(proof, cwd=run, text=True, capture_output=True, timeout=120)
        (run / "FreshGeneration.log").write_text(derived.stdout + derived.stderr)
        self.assertEqual(derived.returncode, 0, derived.stdout + derived.stderr)
        self.assertIn("Closed under the global context", derived.stdout)
        self.assertNotIn("Axioms:", derived.stdout)
        self.assertTrue((run / "fresh_generator.ml").is_file())

    def test_builtin_unmatch_and_error_are_direct(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive-builtin.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "p4", "--input", str(SOURCE.parent / "builtin.watsup"),
                   "--output", str(source), "--manifest", str(run / "manifest.json")]
        result = subprocess.run(command, cwd=run, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        generated = direct_source(source)
        self.assertIn("g_p4_dec_max_x5f_nat_execute", generated)
        self.assertIn("g_p4_dec_text_x5f_to_x5f_int_execute", generated)
        self.assertNotIn("Eval ", generated)
        spec = importlib.util.spec_from_file_location("translate_driver_builtin", ROOT / "scripts/translate.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        driver.compile_generated(source, "p4", run, {"commands": []})
        destination = source / "BuiltinChecks.v"
        shutil.copy2(SOURCE.parent / "BuiltinChecks.v", destination)
        proof = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                 "-Q", str(run / "support"), "ALCoq",
                 "-Q", str(source), "P4Spec", str(destination)]
        checked = subprocess.run(proof, cwd=run, text=True, capture_output=True)
        (run / "BuiltinChecks.log").write_text(checked.stdout + checked.stderr)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertEqual((run / "BuiltinChecks.log").read_text().count(
            "Closed under the global context"), 4)

    def test_polymorphic_and_higher_order_calls_are_direct(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive-higher.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "fixture", "--input", str(SOURCE.parent / "higher_order.watsup"),
                   "--output", str(source), "--manifest", str(run / "manifest.json")]
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
        for name in ["HigherOrderChecks"]:
            destination = source / f"{name}.v"
            shutil.copy2(SOURCE.parent / f"{name}.v", destination)
            proof = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                     "-Q", str(run / "support"), "ALCoq",
                     "-Q", str(source), "FixtureSpec", str(destination)]
            checked = subprocess.run(proof, cwd=run, text=True, capture_output=True)
            (run / f"{name}.log").write_text(checked.stdout + checked.stderr)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertEqual((run / "HigherOrderChecks.log").read_text().count(
            "Closed under the global context"), 7)

    def test_computation_closures_preserve_the_direct_relation(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive-computed.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "fixture", "--property-pre", "Pre", "--input",
                   str(ROOT / "scripts/tests/fixtures/property/rocq/computed.watsup"),
                   "--output", str(source), "--manifest", str(run / "manifest.json")]
        result = subprocess.run(command, cwd=run, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        spec = importlib.util.spec_from_file_location("translate_driver_computed", ROOT / "scripts/translate.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        driver.compile_generated(source, "fixture", run, {"commands": []})
        destination = source / "ComputedChecks.v"
        shutil.copy2(SOURCE.parent / destination.name, destination)
        proof = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                 "-Q", str(run / "support"), "ALCoq",
                 "-Q", str(source), "FixtureSpec", str(destination)]
        checked = subprocess.run(proof, cwd=run, text=True, capture_output=True)
        (run / "ComputedChecks.log").write_text(checked.stdout + checked.stderr)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertIn("Closed under the global context", checked.stdout)
        self.assertNotIn("Axioms:", checked.stdout)

    def test_traverse_first_failure_preserves_fresh_state(self):
        state = ROOT / "_opam-testing-theorems/checks"
        state.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix="inductive-traverse-failure.", dir=state))
        backend = Path(os.environ["INDUCTIVE_BACKEND"])
        source = run / "spec"
        command = ["bash", str(ROOT / "environment/env.sh"), "frontend", str(backend),
                   "--profile", "p4", "--input", str(SOURCE.parent / "traverse_failure.watsup"),
                   "--output", str(source), "--manifest", str(run / "manifest.json")]
        result = subprocess.run(command, cwd=run, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        spec = importlib.util.spec_from_file_location("translate_driver_failure", ROOT / "scripts/translate.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        driver.compile_generated(source, "p4", run, {"commands": []})
        destination = source / "TraverseFailureChecks.v"
        shutil.copy2(SOURCE.parent / "TraverseFailureChecks.v", destination)
        proof = ["bash", str(ROOT / "environment/env.sh"), "coqc", "-q",
                 "-Q", str(run / "support"), "ALCoq",
                 "-Q", str(source), "P4Spec", str(destination)]
        checked = subprocess.run(proof, cwd=run, text=True, capture_output=True)
        (run / "TraverseFailureChecks.log").write_text(checked.stdout + checked.stderr)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertEqual((run / "TraverseFailureChecks.log").read_text().count(
            "Closed under the global context"), 6)


if __name__ == "__main__":
    unittest.main(argv=[__import__("sys").argv[0]])
