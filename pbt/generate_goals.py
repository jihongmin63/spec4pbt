"""Preserve a Lean proposition and derive its proof-carrying generator contract."""

import argparse
import json
from pathlib import Path
import sys
from typing import NamedTuple

from pbt.lean_tools import elaborate, rebuild_modules, require_name, require_timeout


class GoalExpressions(NamedTuple):
    input: str
    premise: str
    target: str
    claim: str
    equivalence: str
    levels: dict[str, list[str]]


def parse_expressions(output: str) -> GoalExpressions:
    """Validate the native reflection response without interpreting Lean source text."""
    prefix = "SPEC4PBT_GOAL "
    records = [line.removeprefix(prefix) for line in output.splitlines() if line.startswith(prefix)]
    if len(records) != 1:
        raise ValueError(f"Lean reflection must return one goal record; received stdout:\n{output}")
    value: object = json.loads(records[0])
    if not isinstance(value, dict):
        raise TypeError(f"Lean reflection returned a non-object JSON value: {value!r}")
    fields: list[str] = []
    for field in ["input", "premise", "target", "claim", "equivalence"]:
        expression: object = value.get(field)
        if not isinstance(expression, str) or not expression:
            raise TypeError(f"Lean reflection field {field!r} must be a nonempty expression string: {expression!r}")
        fields.append(expression)
    levels = value.get("levels")
    if not isinstance(levels, dict):
        raise TypeError("Lean reflection levels must be an object of universe parameter lists")
    for field in ["input", "premise", "target", "claim"]:
        parameters = levels.get(field)
        if (not isinstance(parameters, list)
                or any(not isinstance(parameter, str) or not parameter for parameter in parameters)):
            raise TypeError(f"Lean reflection levels[{field!r}] must be a list of universe names")
        if len(set(parameters)) != len(parameters):
            raise ValueError(f"Duplicate universe parameters in levels[{field!r}]")
    return GoalExpressions(*fields, levels)


def render_goal(spec_module: str, property_module: str, namespace: str, expressions: GoalExpressions) -> str:
    """Render a universe-aware contract with a kernel-checked, constructive equivalence."""
    imports = list(dict.fromkeys(["pbt.CorrectGen", spec_module, property_module]))

    def at_levels(name: str, field: str) -> str:
        parameters = expressions.levels[field]
        return name + (".{" + ", ".join(parameters) + "}" if parameters else "")

    property_name = at_levels("Property", "claim")
    input_name = at_levels("Input", "input")
    premise_name = at_levels("Premise", "premise")
    target_name = at_levels("Target", "target")
    candidate = at_levels("Candidate", "premise")
    generator = at_levels("Generator", "input")
    support = at_levels("Support", "input")
    correct_gen = at_levels("CorrectGen", "input")
    sound = at_levels("Sound", "premise")
    complete = at_levels("Complete", "premise")
    goal = at_levels("Goal", "premise")
    equivalence = at_levels("property_iff", "claim")
    return "\n".join([*(f"import {module}" for module in imports), "", f"namespace {namespace}", "",
        f"def {property_name} : Prop := {expressions.claim}", "",
        f"def {input_name} := {expressions.input}", "",
        f"def {premise_name} : {input_name} → Prop := {expressions.premise}", "",
        f"def {target_name} : {input_name} → Prop := {expressions.target}", "",
        f"def {candidate} := {{input : {input_name} // {premise_name} input}}", "",
        f"def {generator} := Spec4Pbt.Generator {input_name}", "",
        f"def {support} (gen : {generator}) (input : {input_name}) : Prop :=",
        "  Spec4Pbt.Support gen input", "",
        f"def {correct_gen} (P : {input_name} → Prop) := Spec4Pbt.CorrectGen P", "",
        f"def {sound} (gen : {generator}) : Prop :=",
        f"  ∀ size seed, {premise_name} (gen size seed)", "",
        f"def {complete} (gen : {generator}) : Prop :=",
        f"  ∀ input, {premise_name} input → ∃ size seed, gen size seed = input", "",
        f"def {goal} (gen : {generator}) : Prop := {sound} gen ∧ {complete} gen", "",
        f"theorem {equivalence} : {property_name} ↔",
        f"    (∀ input : {input_name}, {premise_name} input → {target_name} input) :=",
        f"  {expressions.equivalence}", "",
        f"end {namespace}", ""])


def generate_goals(project: Path, spec_module: str, property_module: str, declaration: str, namespace: str, output: Path, timeout_seconds: float) -> None:
    """Build source dependencies, reflect, and compile before exclusively creating output."""
    timeout_seconds = require_timeout(timeout_seconds)
    names = [require_name(name) for name in [spec_module, property_module, declaration, namespace]]
    spec_module, property_module, declaration, namespace = names
    if output.exists():
        raise FileExistsError(f"Refusing to overwrite existing goal file: {output}")
    rebuild_modules(project, list(dict.fromkeys(["pbt.GoalTools", "pbt.CorrectGen", spec_module, property_module])), timeout_seconds)
    reflected = elaborate(project, f"import pbt.GoalTools\nimport {spec_module}\nimport {property_module}\n#spec4pbt_goal {declaration}\n", timeout_seconds)
    source = render_goal(spec_module, property_module, namespace, parse_expressions(reflected))
    elaborate(project, source, timeout_seconds)
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x", encoding="utf-8") as destination:
        destination.write(source)
    print(f"Generated and compiled generator contract: {output}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--spec-module", required=True)
    parser.add_argument("--property-module", required=True)
    parser.add_argument("--declaration", required=True)
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout-seconds", required=True, type=float)
    arguments = parser.parse_args()
    generate_goals(Path.cwd(), arguments.spec_module, arguments.property_module, arguments.declaration, arguments.namespace, arguments.output, arguments.timeout_seconds)


if __name__ == "__main__":
    try:
        main()
    except (ChildProcessError, TimeoutError, ValueError, TypeError, FileExistsError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
