"""Strict proof and generator verification through the real Lean kernel."""

import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

from pbt.lean_tools import (
    elaborate, rebuild_modules, require_name, require_timeout, run_checked,
)


from tests import ROOT as REPOSITORY, SCRATCH


def make_project(project: Path) -> None:
    (project / "Fixtures").mkdir()
    (project / "Spec4Pbt").mkdir()
    shutil.copyfile(REPOSITORY / "lean-toolchain", project / "lean-toolchain")
    for name in ["GoalTools.lean", "CorrectGen.lean"]:
        shutil.copyfile(REPOSITORY / "Spec4Pbt" / name, project / "Spec4Pbt" / name)
    (project / ".lake").mkdir()
    (project / ".lake" / "packages").symlink_to(REPOSITORY / ".lake" / "packages", target_is_directory=True)
    manifest = json.loads((REPOSITORY / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest["name"] = "goal_tools_test"
    (project / "lake-manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    (project / "lakefile.toml").write_text(
        'name = "goal_tools_test"\nversion = "0.1.0"\n'
        '[[lean_lib]]\nname = "Fixtures"\n'
        '[[lean_lib]]\nname = "Spec4Pbt"\n'
        '[[require]]\nname = "palamedes"\n'
        'git = "https://github.com/hgoldstein95/palamedes-lean"\n'
        'rev = "c2012b84fc4ad8ee03e3528838175b959fcc9cf8"\n',
        encoding="utf-8",
    )


class ToolBoundaryTests(unittest.TestCase):
    def test_process_deadline_preserves_command_and_partial_output(self) -> None:
        command = [sys.executable, "-c", "import time; print('ready', flush=True); time.sleep(5)"]
        with self.assertRaises(TimeoutError) as raised:
            run_checked(command, REPOSITORY, 2.0)
        diagnostic = str(raised.exception)
        self.assertIn("timed out", diagnostic)
        self.assertIn("ready", diagnostic)
        self.assertIn(str(command), diagnostic)
        self.assertIn(str(REPOSITORY), diagnostic)

    def test_invalid_deadlines_are_rejected(self) -> None:
        for timeout in [float("nan"), float("inf"), float("-inf"), 0, -1]:
            with self.subTest(timeout=timeout):
                with self.assertRaisesRegex(ValueError, "finite and positive"):
                    require_timeout(timeout)
        self.assertEqual(require_timeout(0.5), 0.5)

    def test_identifier_boundary_rejects_embedded_lean_commands(self) -> None:
        for name in ["Fixture.valid\n#eval 1", "Fixture.valid; #eval 1", "", ".proof", "9proof"]:
            with self.subTest(name=name):
                with self.assertRaisesRegex(ValueError, "dotted Lean identifier"):
                    require_name(name)
        self.assertEqual(require_name("Fixture.πProof'"), "Fixture.πProof'")


class GoalToolsIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        SCRATCH.mkdir(parents=True, exist_ok=True)
        cls.temp = tempfile.TemporaryDirectory(prefix="goal-tools-test-", dir=SCRATCH)
        cls.project = Path(cls.temp.name)
        make_project(cls.project)
        rebuild_modules(cls.project, ["Spec4Pbt.GoalTools", "Spec4Pbt.CorrectGen"], 90)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temp.cleanup()

    def verify(self, source: str, proof: str = "Fixture.proof", expected: str = "True",
               module: str = "Fixtures.Proofs") -> str:
        (self.project / "Fixtures" / "Proofs.lean").write_text(source, encoding="utf-8")
        rebuild_modules(self.project, [module], 90)
        return elaborate(self.project,
                         f"import Spec4Pbt.GoalTools\nimport {module}\n"
                         f"#spec4pbt_verify {proof} in_module {module} : ({expected})\n", 90)

    def test_generator_rules_construct_and_extract_a_witness(self) -> None:
        checked = self.verify(
            "import Spec4Pbt.CorrectGen\n"
            "def Fixture.six : CorrectGen (fun n : Nat => n = 6) :=\n"
            "  Gen.CorrectGen.s_pure 6\n"
            "def Fixture.sample : Gen Nat := Fixture.six.val\n"
            "example : Gen.support Fixture.sample 6 := by\n"
            "  change Gen.support Fixture.six.val 6\n"
            "  rw [Fixture.six.property]\n",
            "Fixture.six", "CorrectGen (fun n : Nat => n = 6)",
        )
        self.assertIn("no forbidden transitive axioms", checked)

    def test_pick_rule_constructs_disjunction_and_reaches_both_branches(self) -> None:
        checked = self.verify(
            "import Spec4Pbt.CorrectGen\n"
            "def Fixture.oneOrTwo : CorrectGen (fun n : Nat => n = 1 ∨ n = 2) :=\n"
            "  Gen.CorrectGen.s_pick\n"
            "    (Gen.CorrectGen.s_pure (1 : Nat))\n"
            "    (Gen.CorrectGen.s_pure (2 : Nat))\n"
            "example : Gen.support Fixture.oneOrTwo.val 1 := by\n"
            "  rw [Fixture.oneOrTwo.property]\n"
            "  exact Or.inl rfl\n"
            "example : Gen.support Fixture.oneOrTwo.val 2 := by\n"
            "  rw [Fixture.oneOrTwo.property]\n"
            "  exact Or.inr rfl\n",
            "Fixture.oneOrTwo", "CorrectGen (fun n : Nat => n = 1 ∨ n = 2)",
        )
        self.assertIn("no forbidden transitive axioms", checked)

    def test_bind_rule_constructs_dependent_generator(self) -> None:
        checked = self.verify(
            "import Spec4Pbt.CorrectGen\n"
            "def Fixture.oneOrTwo : CorrectGen (fun n : Nat => n = 1 ∨ n = 2) :=\n"
            "  Gen.CorrectGen.s_pick\n"
            "    (Gen.CorrectGen.s_pure (1 : Nat))\n"
            "    (Gen.CorrectGen.s_pure (2 : Nat))\n"
            "def Fixture.twoOrFour : CorrectGen\n"
            "    (fun n : Nat => ∃ k, (k = 1 ∨ k = 2) ∧ n = 2 * k) :=\n"
            "  Gen.CorrectGen.s_bind Fixture.oneOrTwo\n"
            "    (fun k => Gen.CorrectGen.s_pure (2 * k))\n"
            "example : Gen.support Fixture.twoOrFour.val 2 := by\n"
            "  rw [Fixture.twoOrFour.property]\n"
            "  exact ⟨1, Or.inl rfl, rfl⟩\n"
            "example : Gen.support Fixture.twoOrFour.val 4 := by\n"
            "  rw [Fixture.twoOrFour.property]\n"
            "  exact ⟨2, Or.inr rfl, rfl⟩\n",
            "Fixture.twoOrFour", "CorrectGen (fun n : Nat => ∃ k, (k = 1 ∨ k = 2) ∧ n = 2 * k)",
        )
        self.assertIn("no forbidden transitive axioms", checked)

    def test_converted_generator_proves_soundness_and_completeness(self) -> None:
        checked = self.verify(
            "import Spec4Pbt.CorrectGen\n"
            "def Fixture.Premise (n : Nat) : Prop := n = n\n"
            "def Fixture.certified : CorrectGen Fixture.Premise :=\n"
            "  Gen.CorrectGen.convert (by funext n; apply propext; simp [Fixture.Premise])\n"
            "    Gen.CorrectGen.s_arbNat\n"
            "def Fixture.generate : Gen Nat := Fixture.certified.val\n"
            "theorem Fixture.sound : ∀ n, Gen.support Fixture.generate n → Fixture.Premise n := by\n"
            "  intro n h\n"
            "  exact (Iff.of_eq (congrFun Fixture.certified.property n)).mp h\n"
            "theorem Fixture.complete : ∀ n, Fixture.Premise n → Gen.support Fixture.generate n := by\n"
            "  intro n h\n"
            "  exact (Iff.of_eq (congrFun Fixture.certified.property n)).mpr h\n",
            "Fixture.certified", "CorrectGen Fixture.Premise",
        )
        self.assertIn("no forbidden transitive axioms", checked)

    def test_unicode_and_apostrophe_names_are_verified(self) -> None:
        checked = self.verify("theorem Fixture.πProof' : ∀ n : Nat, n = n := fun _ => rfl\n",
                              "Fixture.πProof'", "∀ n : Nat, n = n")
        self.assertIn("Verified 'Fixture.πProof'", checked)

    def test_verifier_rejects_untrusted_transitive_axioms(self) -> None:
        bodies = [
            ("custom", "axiom Fixture.untrusted : True\ntheorem Fixture.proof : True := Fixture.untrusted\n", "Fixture.untrusted"),
            ("sorry", "theorem Fixture.proof : True := by sorry\n", "sorryAx"),
            ("choice", "theorem Fixture.proof : True := Classical.choice (show Nonempty True from ⟨True.intro⟩)\n", "Classical.choice"),
        ]
        for label, body, axiom in bodies:
            with self.subTest(case=label):
                with self.assertRaises(ChildProcessError) as raised:
                    self.verify(body)
                self.assertIn(axiom, str(raised.exception))

    def test_verifier_allows_only_approved_foundational_axioms(self) -> None:
        checked = self.verify("theorem Fixture.proof : True = True := propext Iff.rfl\n",
                              expected="True = True")
        self.assertIn("propext", checked)
        expected = "Quot.mk (fun (_ _ : Nat) => True) 0 = Quot.mk (fun (_ _ : Nat) => True) 0"
        checked = self.verify(f"theorem Fixture.proof : {expected} := Quot.sound True.intro\n",
                              expected=expected)
        self.assertIn("Quot.sound", checked)

    def test_verifier_rejects_sorry_in_generator_witness(self) -> None:
        with self.assertRaisesRegex(ChildProcessError, "sorryAx"):
            self.verify(
                "import Spec4Pbt.CorrectGen\n"
                "def Fixture.uncertified : CorrectGen (fun _ : Nat => True) := by\n"
                "  refine ⟨pure 0, ?_⟩\n"
                "  sorry\n",
                "Fixture.uncertified", "CorrectGen (fun _ : Nat => True)",
            )

    def test_verifier_rejects_additional_hypotheses_and_prop_definitions(self) -> None:
        for source in [
            "theorem Fixture.proof (_assumption : False) : True := False.elim _assumption\n",
            "def Fixture.proof : Prop := True\n",
        ]:
            with self.subTest(source=source):
                with self.assertRaisesRegex(ChildProcessError, "type mismatch"):
                    self.verify(source)

    def test_rebuilding_dependencies_prevents_stale_proof_acceptance(self) -> None:
        dependency = self.project / "Fixtures" / "Dependency.lean"
        dependency.write_text("theorem Fixture.dependency : True := True.intro\n", encoding="utf-8")
        source = "import Fixtures.Dependency\ntheorem Fixture.proof : True := Fixture.dependency\n"
        self.assertIn("Verified", self.verify(source))
        dependency.write_text("theorem Fixture.dependency : True := by sorry\n", encoding="utf-8")
        with self.assertRaisesRegex(ChildProcessError, "sorryAx"):
            self.verify(source)

    def test_verifier_rejects_unused_axiom_declared_in_own_module(self) -> None:
        with self.assertRaisesRegex(ChildProcessError, "Fixture.unused"):
            self.verify("axiom Fixture.unused : True\ntheorem Fixture.proof : True := True.intro\n")

    def test_verifier_rejects_a_reexported_proof_as_owned_by_the_importer(self) -> None:
        (self.project / "Fixtures" / "Alias.lean").write_text("import Fixtures.Proofs\n", encoding="utf-8")
        with self.assertRaisesRegex(ChildProcessError, "not requested module"):
            self.verify("theorem Fixture.proof : True := True.intro\n", module="Fixtures.Alias")

    def test_verifier_rejects_an_incomplete_expected_type(self) -> None:
        with self.assertRaisesRegex(ChildProcessError, "unresolved metavariables"):
            self.verify("theorem Fixture.proof : True := True.intro\n", expected="_")


if __name__ == "__main__":
    unittest.main()
