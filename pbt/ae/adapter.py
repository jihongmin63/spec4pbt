"""An independent arithmetic implementation, using Lean's derived JSON schema."""

import json
import sys


def evaluate(expression):
    if not isinstance(expression, dict) or len(expression) != 1:
        raise ValueError("expected one expression constructor")
    constructor, argument = next(iter(expression.items()))
    if constructor == "c0" and type(argument) is int:
        return argument
    if constructor not in ("c1", "c2") or not isinstance(argument, list) or len(argument) != 2:
        raise ValueError("invalid arithmetic expression")
    left, right = map(evaluate, argument)
    return left + right if constructor == "c1" else left - right


def main():
    request = json.load(sys.stdin)
    value = evaluate(request["input"])
    if sys.argv[1:] == ["--wrong"]:
        value += 1
    elif sys.argv[1:]:
        raise ValueError("unexpected arguments")
    print(json.dumps({"observation": value}))


if __name__ == "__main__":
    main()
