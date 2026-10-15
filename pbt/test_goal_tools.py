"""Exercise goal extraction and strict proof verification with the real Lean kernel."""

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from pbt.generate_goals import parse_expressions, render_goal
from pbt.lean_tools import elaborate, rebuild_modules, run_checked


REPOSITORY = Path(__file__).resolve().parents[1]


def run_cli(project: Path, script: str, arguments: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "pbt." + script.removesuffix(".py"), *arguments],
        cwd=project,
        text=True,
        capture_output=True,
        check=False,
        timeout=180,
    )


def make_project(project: Path) -> None:
    (project / "Fixtures").mkdir()
    (project / "pbt").mkdir()
    shutil.copyfile(REPOSITORY / "lean-toolchain", project / "lean-toolchain")
    for name in ["GoalTools.lean", "CorrectGen.lean", "lean_tools.py", "generate_goals.py", "verify.py"]:
        shutil.copyfile(REPOSITORY / "pbt" / name, project / "pbt" / name)
    (project / "lakefile.toml").write_text(
        'name = "goal_tools_test"\nversion = "0.1.0"\n'
        '[[lean_lib]]\nname = "Fixtures"\n'
        '[[lean_lib]]\nname = "pbt"\n',
        encoding="utf-8",
    )
    (project / "Fixtures" / "Spec.lean").write_text(
        "namespace Fixture\ndef Valid (n : Nat) : Prop := n = n\nend Fixture\n",
        encoding="utf-8",
    )
    (project / "Fixtures" / "Property.lean").write_text(
        "import Fixtures.Spec\n"
        "universe u v\n"
        "universe «Type»\n"
        "def Input := Nat\n"
        "def Target : Prop := False\n"
        "private def Fixture.privateValid (n : Nat) : Prop := n = n\n"
        "def Fixture.property : Prop := ∀ n : Nat, Fixture.Valid n → n + 0 = n\n"
        "theorem Fixture.propertyTheorem : ∀ n : Nat, Fixture.Valid n → n + 0 = n := "
        "by intro n _; rfl\n"
        "def Fixture.multipleInputs : Prop := ∀ n m : Nat, n = m → n = m\n"
        "def Fixture.dependent : Prop := ∀ p : Prop, p → p\n"
        "def Fixture.dependentProof : Prop := ∀ n : Nat, ∀ h : n = n, h = h\n"
        "def Fixture.noPremise : Prop := ∀ n : Nat, n + 0 = n\n"
        "def Fixture.multiplePremises : Prop := ∀ n : Nat, n = n → n = 0 → n = 0\n"
        "def Fixture.nestedForall : Prop := ∀ n : Nat, Fixture.Valid n → ∀ m : Nat, n + m = m + n\n"
        "def Fixture.implicitInput : Prop := ∀ {n : Nat}, n = n\n"
        "def Fixture.dependentInput : Prop := ∀ n : Nat, ∀ i : Fin (n + 1), i.val ≤ n\n"
        "def Fixture.higherOrder : Prop := ∀ f : Nat → Nat, ∀ n : Nat, f n = f n\n"
        "def Fixture.typeInput : Prop := ∀ α : Type, ∀ x : α, x = x\n"
        "def Fixture.polymorphic : Prop := ∀ {α : Sort u}, ∀ x : α, x = x\n"
        "def Fixture.multipleUniverses : Prop := ∀ (α : Type u) (β : Type v) (x : α) (y : β), x = x ∧ y = y\n"
        "def Fixture.keywordUniverse : Prop := ∀ (α : Type «Type») (x : α), x = x\n"
        "def Fixture.shadowedInput : Prop := ∀ n : Input, n = n → n = n\n"
        "def Fixture.shadowedTarget : Prop := ∀ n : Nat, n = n → Target\n"
        "def Fixture.privateHelper : Prop := ∀ n : Nat, Fixture.privateValid n → n = n\n"
        "def Fixture.instanceInput : Prop := ∀ {α : Type u} [Inhabited α], (default : α) = default\n"
        "def Fixture.universePremise : Prop := ∀ n : Nat, (∃ α : Type u, Nonempty α) → n = n\n"
        "def Fixture.universeTarget : Prop := ∀ n : Nat, n = n → ∃ α : Type u, Nonempty α\n"
        "def Fixture.universeClosedTarget : Prop := ∃ α : Type u, Nonempty α\n"
        "def Fixture.parameterized (n m : Nat) : Prop := n = m\n"
        "def Fixture.parameterizedImplicit {α : Sort u} (x : α) : Prop := x = x\n"
        "theorem Fixture.polymorphicTheorem {α : Sort u} (x : α) : x = x := rfl\n"
        "def Fixture.truth : Prop := True\n"
        "def Fixture.falsehood : Prop := False\n"
        "def Fixture.existential : Prop := ∃ n : Nat, n = 0\n"
        "def Fixture.conjunction : Prop := (∀ n : Nat, n = n) ∧ (∃ m : Nat, m = 0)\n"
        "def Fixture.disjunction : Prop := (∃ n : Nat, n = 0) ∨ False\n"
        "def Fixture.negation : Prop := ¬ (∃ n : Nat, n < n)\n"
        "def Fixture.iffProperty : Prop := (∃ n : Nat, n = 0) ↔ True\n"
        "def Fixture.letBound : Prop := let n := 2; ∀ m : Nat, n + m = m + n\n"
        "def Fixture.alias : Prop := Fixture.multipleInputs\n"
        "def Fixture.PropFamily : Type := Nat → Prop\n"
        "def Fixture.aliasedType : Fixture.PropFamily := fun n => n = n\n"
        "opaque Fixture.opaqueProposition : Prop := True\n"
        "inductive Fixture.inductiveProposition (n : Nat) : Prop where\n"
        "  | witness : Fixture.inductiveProposition n\n"
        "private opaque Fixture.hiddenOpaque : Prop := True\n"
        "def Fixture.privateOpaque : Prop := Fixture.hiddenOpaque\n"
        "def Fixture.privateOpaqueWithInput : Prop := "
        "∀ n : Nat, Fixture.hiddenOpaque → n = n\n"
        "theorem Fixture.theoremWithPrivate : "
        "Fixture.hiddenOpaque → Fixture.hiddenOpaque := fun h => h\n"
        "theorem Fixture.polymorphicPrivateTheorem {α : Sort u} "
        "(x : α) (h : Fixture.hiddenOpaque) : x = x := rfl\n"
        "private def Fixture.privateCount : Nat → Nat\n"
        "  | 0 => 0\n"
        "  | n + 1 => Fixture.privateCount n + 1\n"
        "def Fixture.privateRecursive : Prop := ∀ n, Fixture.privateCount n = n\n"
        "private inductive Fixture.Hidden : Type where\n"
        "  | mk : Fixture.Hidden\n"
        "def Fixture.privateDomain (x : Fixture.Hidden) : Prop := True\n"
        "private inductive Fixture.HiddenIndex (n : Nat) : Type where\n"
        "  | mk : Fixture.HiddenIndex n\n"
        "def Fixture.privateDependentDomain (n : Nat) "
        "(x : Fixture.HiddenIndex n) : Prop := n = n\n"
        "opaque Fixture.opaqueNat : Nat := 0\n"
        "inductive Fixture.dataType : Type where\n"
        "  | mk : Fixture.dataType\n"
        "def Fixture.notProp : Nat := 0\n"
        "def Fixture.notPropFunction (n : Nat) : Nat := n\n"
        "axiom Fixture.axiomProperty : Prop\n",
        encoding="utf-8",
    )


def generate(project: Path, declaration: str, output: str) -> subprocess.CompletedProcess[str]:
    return run_cli(project, "generate_goals.py", [
        "--spec-module", "Fixtures.Spec",
        "--property-module", "Fixtures.Property",
        "--declaration", declaration,
        "--namespace", "FixtureGoals",
        "--output", output, "--timeout-seconds", "60",
    ])


def verify(project: Path, proof: str, expected: str) -> subprocess.CompletedProcess[str]:
    return run_cli(project, "verify.py", [
        "--module", "Fixtures.Proofs", "--proof", proof, "--expected-type", expected,
        "--timeout-seconds", "60",
    ])


class ToolBoundaryTests(unittest.TestCase):
    def test_reflection_requires_expression_levels_and_equivalence_proof(self) -> None:
        levels = {field: [] for field in ["input", "premise", "target", "claim"]}
        record = {
            "input": "Unit", "premise": "fun _ => True", "target": "fun _ => False",
            "claim": "False", "levels": levels, "equivalence": "by simp",
        }
        parsed = parse_expressions("SPEC4PBT_GOAL " + json.dumps(record))
        self.assertEqual(parsed.claim, "False")
        self.assertEqual(parsed.levels, levels)
        self.assertEqual(parsed.equivalence, "by simp")
        for field, invalid in [
            ("levels", None), ("levels", "u"), ("levels", [1]), ("levels", {}),
            ("levels", {**levels, "input": None}),
            ("levels", {**levels, "target": "u"}),
            ("levels", {**levels, "claim": [1]}),
            ("equivalence", None), ("equivalence", ""), ("equivalence", 1),
        ]:
            with self.subTest(field=field, invalid=invalid):
                with self.assertRaises((TypeError, ValueError)):
                    parse_expressions("SPEC4PBT_GOAL " + json.dumps({**record, field: invalid}))

    def test_process_deadline_preserves_command_and_partial_output(self) -> None:
        command = [sys.executable, "-c", "import time; print('ready', flush=True); time.sleep(5)"]
        with self.assertRaises(TimeoutError) as raised:
            run_checked(command, REPOSITORY, 2.0)
        diagnostic = str(raised.exception)
        self.assertIn("timed out", diagnostic)
        self.assertIn("ready", diagnostic)
        self.assertIn(str(REPOSITORY), diagnostic)

    def test_invalid_deadlines_fail_before_starting_lean(self) -> None:
        commands = [
            ("generate_goals.py", ["--spec-module", "specifications.Example",
             "--property-module", "pbt.example.Property", "--declaration", "Example.property",
             "--namespace", "Rejected", "--output", "test_cases/invalid-goal.lean"]),
            ("verify.py", ["--module", "pbt.example.Generator", "--proof", "Example.correctGenerator",
             "--expected-type", "ExampleGoals.CorrectGen ExampleGoals.Premise"]),
        ]
        for script, arguments in commands:
            with self.subTest(script=script):
                result = run_cli(REPOSITORY, script, [*arguments, "--timeout-seconds", "nan"])
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("finite and positive", result.stderr)


class GoalToolsIntegrationTests(unittest.TestCase):
    def test_generator_rules_construct_and_extract_a_witness(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            (project / "Fixtures" / "Proofs.lean").write_text(
                "import pbt.CorrectGen\n"
                "def Fixture.six : Spec4Pbt.CorrectGen (fun n : Nat => n = 6) :=\n"
                "  Spec4Pbt.CorrectGen.convert\n"
                "    (Spec4Pbt.CorrectGen.map (fun n : Nat => 2 * n)\n"
                "      (Spec4Pbt.CorrectGen.pure (3 : Nat)))\n"
                "    (by\n"
                "      intro n\n"
                "      constructor\n"
                "      · rintro ⟨k, hk, hn⟩\n"
                "        subst k\n"
                "        exact hn.symm\n"
                "      · intro hn\n"
                "        subst n\n"
                "        exact ⟨3, rfl, rfl⟩)\n"
                "def Fixture.sample : Spec4Pbt.Generator Nat := Fixture.six.val\n"
                "example : Fixture.sample 0 0 = 6 := rfl\n",
                encoding="utf-8",
            )
            checked = verify(project, "Fixture.six", "Spec4Pbt.CorrectGen (fun n : Nat => n = 6)")
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_pick_rule_constructs_disjunction_and_reaches_both_branches(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            (project / "Fixtures" / "Proofs.lean").write_text(
                "import pbt.CorrectGen\n"
                "def Fixture.oneOrTwo : Spec4Pbt.CorrectGen (fun n : Nat => n = 1 ∨ n = 2) :=\n"
                "  Spec4Pbt.CorrectGen.pick\n"
                "    (Spec4Pbt.CorrectGen.pure (1 : Nat))\n"
                "    (Spec4Pbt.CorrectGen.pure (2 : Nat))\n"
                "example : Fixture.oneOrTwo.val 0 0 = 1 := rfl\n"
                "example : Fixture.oneOrTwo.val 0 1 = 2 := rfl\n",
                encoding="utf-8",
            )
            checked = verify(project, "Fixture.oneOrTwo", "Spec4Pbt.CorrectGen (fun n : Nat => n = 1 ∨ n = 2)")
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_bind_rule_constructs_dependent_generator(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            (project / "Fixtures" / "Proofs.lean").write_text(
                "import pbt.CorrectGen\n"
                "def Fixture.oneOrTwo : Spec4Pbt.CorrectGen (fun n : Nat => n = 1 ∨ n = 2) :=\n"
                "  Spec4Pbt.CorrectGen.pick\n"
                "    (Spec4Pbt.CorrectGen.pure (1 : Nat))\n"
                "    (Spec4Pbt.CorrectGen.pure (2 : Nat))\n"
                "def Fixture.twoOrFour : Spec4Pbt.CorrectGen\n"
                "    (fun n : Nat => ∃ k, (k = 1 ∨ k = 2) ∧ n = 2 * k) :=\n"
                "  Spec4Pbt.CorrectGen.bind Fixture.oneOrTwo\n"
                "    (fun k => Spec4Pbt.CorrectGen.pure (2 * k))\n"
                "example : Fixture.twoOrFour.val 0 0 = 2 := rfl\n"
                "example : Fixture.twoOrFour.val 0 1 = 4 := rfl\n",
                encoding="utf-8",
            )
            checked = verify(project, "Fixture.twoOrFour", "Spec4Pbt.CorrectGen "
                             "(fun n : Nat => ∃ k, (k = 1 ∨ k = 2) ∧ n = 2 * k)")
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_generated_goal_extracts_generator_from_verified_witness(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            generated = generate(project, "Fixture.property", "Fixtures/Goal.lean")
            self.assertEqual(generated.returncode, 0, generated.stdout + generated.stderr)
            (project / "Fixtures" / "Proofs.lean").write_text(
                "import Fixtures.Goal\n"
                "example : FixtureGoals.Generator = (Nat → Nat → FixtureGoals.Input) := rfl\n"
                "def Fixture.certified : FixtureGoals.CorrectGen FixtureGoals.Premise := by\n"
                "  refine ⟨fun _size seed => seed, ?_⟩\n"
                "  intro input\n"
                "  constructor\n"
                "  · intro _; rfl\n"
                "  · intro _; exact ⟨0, input, rfl⟩\n"
                "def Fixture.generate : FixtureGoals.Generator := Fixture.certified.val\n"
                "example : Fixture.generate 0 3 = (3 : Nat) := rfl\n"
                "example : FixtureGoals.Sound Fixture.generate := Fixture.certified.sound\n"
                "example : FixtureGoals.Complete Fixture.generate := Fixture.certified.complete\n",
                encoding="utf-8",
            )
            checked = verify(project, "Fixture.certified", "FixtureGoals.CorrectGen FixtureGoals.Premise")
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            original = (project / "Fixtures" / "Goal.lean").read_bytes()
            repeated = generate(project, "Fixture.property", "Fixtures/Goal.lean")
            self.assertNotEqual(repeated.returncode, 0)
            self.assertEqual((project / "Fixtures" / "Goal.lean").read_bytes(), original)

    def test_theorem_property_is_reflected_from_its_type(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            result = generate(project, "Fixture.propertyTheorem", "Fixtures/Goal.lean")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_arbitrary_proposition_shapes_preserve_the_original_claim_without_axioms(self) -> None:
        declarations = [
            "property", "propertyTheorem", "multipleInputs", "dependent", "dependentProof", "noPremise", "multiplePremises",
            "nestedForall", "implicitInput", "dependentInput", "higherOrder", "typeInput",
            "polymorphic", "multipleUniverses", "keywordUniverse", "shadowedInput", "shadowedTarget", "privateHelper", "instanceInput", "parameterized",
            "universePremise", "universeTarget", "universeClosedTarget",
            "parameterizedImplicit", "polymorphicTheorem", "truth", "falsehood", "existential",
            "conjunction", "disjunction", "negation", "iffProperty", "letBound", "alias", "aliasedType",
            "opaqueProposition", "inductiveProposition", "privateOpaque", "privateRecursive",
            "privateOpaqueWithInput", "theoremWithPrivate", "polymorphicPrivateTheorem",
            "privateDomain", "privateDependentDomain",
        ]
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            rebuild_modules(project, ["pbt.GoalTools", "pbt.CorrectGen", "Fixtures.Property"], 60)
            reflected = elaborate(project, "\n".join([
                "import pbt.GoalTools", "import Fixtures.Property",
                *(f"#spec4pbt_goal Fixture.{name}" for name in declarations), "",
            ]), 60)
            records = [line for line in reflected.splitlines() if line.startswith("SPEC4PBT_GOAL ")]
            self.assertEqual(len(records), len(declarations), reflected)
            modules = ["import pbt.GoalTools\nimport pbt.CorrectGen\nimport Fixtures.Spec\nimport Fixtures.Property\n"]
            verification_commands = []
            for name, record in zip(declarations, records, strict=True):
                with self.subTest(declaration=name):
                    expressions = parse_expressions(record)
                    if name in ["universePremise", "universeTarget", "universeClosedTarget"]:
                        self.assertEqual(expressions.levels["input"], [])
                        self.assertEqual(expressions.levels["claim"], ["u"])
                        self.assertEqual(expressions.levels["premise"], ["u"] if name == "universePremise" else [])
                        self.assertEqual(expressions.levels["target"], [] if name == "universePremise" else ["u"])
                    source = render_goal(
                        "Fixtures.Spec", "Fixtures.Property", f"Goals_{name}", expressions,
                    )
                    body = "\n".join(line for line in source.splitlines() if not line.startswith("import "))
                    modules.append("section\n" + body + "\nend\n")
                    universe_values = {
                        level: str(index + 1)
                        for index, level in enumerate(sorted({
                            level for levels in expressions.levels.values() for level in levels
                        }))
                    }
                    references = {}
                    for declaration, field in [("Property", "claim"), ("Input", "input"),
                                               ("Premise", "premise"), ("Target", "target")]:
                        arguments = ", ".join(universe_values[level] for level in expressions.levels[field])
                        references[declaration] = f"Goals_{name}.{declaration}" + (f".{{{arguments}}}" if arguments else "")
                    verification_commands.append(
                        f"#spec4pbt_verify Goals_{name}.property_iff in_module Fixtures.Shapes : "
                        f"{references['Property']} ↔ "
                        f"(∀ input : {references['Input']}, {references['Premise']} input → {references['Target']} input)"
                    )
            modules.append(
                "example : Goals_parameterized.Property = (∀ n m : Nat, Fixture.parameterized n m) := rfl\n"
                "example : Goals_falsehood.Property = False := rfl\n"
                "example : Goals_falsehood.Input = Unit := rfl\n"
                "example (input : Goals_falsehood.Input) : Goals_falsehood.Target input = False := rfl\n"
                "example (input : Goals_existential.Input) : "
                "Goals_existential.Target input = (∃ n : Nat, n = 0) := rfl\n"
                "example (input : Goals_conjunction.Input) : "
                "Goals_conjunction.Target input = ((∀ n : Nat, n = n) ∧ (∃ m : Nat, m = 0)) := rfl\n"
                "example : Goals_polymorphic.Property.{0} = (∀ {α : Prop}, ∀ x : α, x = x) := rfl\n"
                "example : Goals_polymorphic.Property.{2} = (∀ {α : Type 1}, ∀ x : α, x = x) := rfl\n"
                "example : Goals_parameterizedImplicit.Property.{2} = "
                "(∀ {α : Type 1}, ∀ x : α, Fixture.parameterizedImplicit x) := rfl\n"
                "example : Goals_multipleUniverses.Property.{1, 2} = "
                "(∀ (α : Type 1) (β : Type 2) (x : α) (y : β), x = x ∧ y = y) := rfl\n"
                "example : Goals_universePremise.Input = Nat := rfl\n"
                "example (n : Nat) : Goals_universePremise.Premise.{2} n = "
                "(∃ α : Type 2, Nonempty α) := rfl\n"
                "example : Goals_universeTarget.Input = Nat := rfl\n"
                "example (n : Nat) : Goals_universeTarget.Target.{2} n = "
                "(∃ α : Type 2, Nonempty α) := rfl\n"
                "example : Goals_universeClosedTarget.Input = Unit := rfl\n"
                "example (input : Goals_universeClosedTarget.Input) : "
                "Goals_universeClosedTarget.Target.{2} input = (∃ α : Type 2, Nonempty α) := rfl\n"
                "example : Goals_privateOpaque.Input = Unit := rfl\n"
                "example (input : Goals_privateOpaque.Input) : "
                "Goals_privateOpaque.Target input = Fixture.privateOpaque := rfl\n"
                "example : Goals_privateOpaqueWithInput.Input = Unit := rfl\n"
                "example (input : Goals_privateOpaqueWithInput.Input) : "
                "Goals_privateOpaqueWithInput.Target input = Fixture.privateOpaqueWithInput := rfl\n"
                "example : Goals_privateRecursive.Input = Unit := rfl\n"
                "example (input : Goals_privateRecursive.Input) : "
                "Goals_privateRecursive.Target input = Fixture.privateRecursive := rfl\n"
                "example : Goals_theoremWithPrivate.Input = Unit := rfl\n"
                "example (input : Goals_theoremWithPrivate.Input) : "
                "Goals_theoremWithPrivate.Target input = Goals_theoremWithPrivate.Property := rfl\n"
                "example : Goals_privateDomain.Input = Unit := rfl\n"
                "example (input : Goals_privateDomain.Input) : "
                "Goals_privateDomain.Target input = (∀ x, Fixture.privateDomain x) := rfl\n"
                "example : Goals_privateDependentDomain.Input = Unit := rfl\n"
                "example (input : Goals_privateDependentDomain.Input) : "
                "Goals_privateDependentDomain.Target input = "
                "(∀ n x, Fixture.privateDependentDomain n x) := rfl\n"
            )
            (project / "Fixtures" / "Shapes.lean").write_text("\n".join(modules), encoding="utf-8")
            rebuild_modules(project, ["Fixtures.Shapes"], 60)
            checked = elaborate(project, "\n".join([
                "import pbt.GoalTools", "import Fixtures.Shapes",
                *verification_commands, "",
            ]), 60)
            self.assertEqual(checked.count("zero transitive axioms"), len(declarations), checked)

    def test_parameterized_property_works_through_the_cli(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            generated = generate(project, "Fixture.parameterized", "Fixtures/Goal.lean")
            self.assertEqual(generated.returncode, 0, generated.stdout + generated.stderr)
            (project / "Fixtures" / "Proofs.lean").write_text(
                "import Fixtures.Goal\n"
                "example : FixtureGoals.Property = (∀ n m : Nat, n = m) := rfl\n"
                "theorem Fixture.proof : FixtureGoals.Property ↔ "
                "(∀ input : FixtureGoals.Input, FixtureGoals.Premise input → FixtureGoals.Target input) := "
                "FixtureGoals.property_iff\n",
                encoding="utf-8",
            )
            checked = verify(project, "Fixture.proof", "FixtureGoals.Property ↔ "
                             "(∀ input : FixtureGoals.Input, FixtureGoals.Premise input → FixtureGoals.Target input)")
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_unicode_and_apostrophe_names_work_through_both_clis(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            with (project / "Fixtures" / "Property.lean").open("a", encoding="utf-8") as source:
                source.write("def Fixture.αβ' : Prop := ∀ n : Nat, n = n\n")
            generated = run_cli(project, "generate_goals.py", [
                "--spec-module", "Fixtures.Spec", "--property-module", "Fixtures.Property",
                "--declaration", "Fixture.αβ'", "--namespace", "ΓGoals'",
                "--output", "Fixtures/Goal.lean", "--timeout-seconds", "60",
            ])
            self.assertEqual(generated.returncode, 0, generated.stdout + generated.stderr)
            (project / "Fixtures" / "Proofs.lean").write_text(
                "import Fixtures.Goal\n"
                "theorem Fixture.πProof' : ΓGoals'.Property ↔ "
                "(∀ input : ΓGoals'.Input, ΓGoals'.Premise input → ΓGoals'.Target input) := "
                "ΓGoals'.property_iff\n",
                encoding="utf-8",
            )
            checked = verify(project, "Fixture.πProof'", "ΓGoals'.Property ↔ "
                             "(∀ input : ΓGoals'.Input, ΓGoals'.Premise input → ΓGoals'.Target input)")
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_embedded_source_is_rejected_by_generate_cli(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            for declaration in ["Fixture.valid\n#eval 1", "Fixture.valid; #eval 1"]:
                with self.subTest(declaration=declaration):
                    result = generate(project, declaration, "Fixtures/Goal.lean")
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("Expected a dotted Lean identifier", result.stderr)
                    self.assertFalse((project / "Fixtures" / "Goal.lean").exists())

    def test_non_proposition_and_axiom_declarations_fail_without_creating_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            for declaration in ["Fixture.notProp", "Fixture.notPropFunction", "Fixture.opaqueNat",
                                "Fixture.dataType", "Fixture.axiomProperty"]:
                with self.subTest(declaration=declaration):
                    result = generate(project, declaration, "Fixtures/Goal.lean")
                    self.assertNotEqual(result.returncode, 0)
                    self.assertFalse((project / "Fixtures" / "Goal.lean").exists())

    def test_verifier_rejects_all_transitive_axioms(self) -> None:
        bodies = [
            ("custom", "axiom Fixture.untrusted : True\ntheorem Fixture.proof : True := Fixture.untrusted\n", "Fixture.untrusted", "True"),
            ("sorry", "theorem Fixture.proof : True := by sorry\n", "sorryAx", "True"),
            ("propext", "theorem Fixture.proof : True = True := propext Iff.rfl\n", "propext", "True = True"),
            ("choice", "theorem Fixture.proof : True := Classical.choice (show Nonempty True from ⟨True.intro⟩)\n", "Classical.choice", "True"),
            ("quot", "theorem Fixture.proof : Quot.mk (fun (_ _ : Nat) => True) 0 = Quot.mk (fun (_ _ : Nat) => True) 0 := Quot.sound True.intro\n", "Quot.sound", "Quot.mk (fun (_ _ : Nat) => True) 0 = Quot.mk (fun (_ _ : Nat) => True) 0"),
        ]
        for label, body, axiom, expected in bodies:
            with self.subTest(case=label), tempfile.TemporaryDirectory() as directory:
                project = Path(directory)
                make_project(project)
                (project / "Fixtures" / "Proofs.lean").write_text(body, encoding="utf-8")
                result = verify(project, "Fixture.proof", expected)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(axiom, result.stdout + result.stderr)

    def test_verifier_rejects_sorry_in_generator_witness(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            (project / "Fixtures" / "Proofs.lean").write_text(
                "import pbt.CorrectGen\n"
                "def Fixture.uncertified : Spec4Pbt.CorrectGen (fun _ : Nat => True) := by\n"
                "  refine ⟨fun _ _ => 0, ?_⟩\n"
                "  intro _\n"
                "  sorry\n",
                encoding="utf-8",
            )
            checked = verify(project, "Fixture.uncertified",
                             "Spec4Pbt.CorrectGen (fun _ : Nat => True)")
            self.assertNotEqual(checked.returncode, 0)
            self.assertIn("sorryAx", checked.stdout + checked.stderr)

    def test_verifier_rejects_additional_hypotheses_and_prop_definitions(self) -> None:
        declarations = [
            "theorem Fixture.proof (_assumption : False) : True := False.elim _assumption\n",
            "def Fixture.proof : Prop := True\n",
        ]
        for declaration in declarations:
            with self.subTest(declaration=declaration), tempfile.TemporaryDirectory() as directory:
                project = Path(directory)
                make_project(project)
                (project / "Fixtures" / "Proofs.lean").write_text(declaration, encoding="utf-8")
                result = verify(project, "Fixture.proof", "True")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("type mismatch", result.stdout + result.stderr)

    def test_verifier_rebuilds_changed_dependencies(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            source = project / "Fixtures" / "Proofs.lean"
            source.write_text("theorem Fixture.proof : True := True.intro\n", encoding="utf-8")
            accepted = verify(project, "Fixture.proof", "True")
            self.assertEqual(accepted.returncode, 0, accepted.stdout + accepted.stderr)
            source.write_text("theorem Fixture.proof : True := by sorry\n", encoding="utf-8")
            rejected = verify(project, "Fixture.proof", "True")
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn("sorryAx", rejected.stdout + rejected.stderr)

    def test_verifier_rejects_unused_axiom_declared_in_own_module(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            make_project(project)
            (project / "Fixtures" / "Proofs.lean").write_text(
                "axiom Fixture.unused : True\ntheorem Fixture.proof : True := True.intro\n",
                encoding="utf-8",
            )
            result = verify(project, "Fixture.proof", "True")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Fixture.unused", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
