"""Project VALUE from the actual implementation result; TRACE is unobserved."""

import json
import sys


def implementation(value, mode):
    if type(value) is not int:
        raise ValueError("input must be an integer")
    return {"VALUE": value if mode == "wrong" else value + 1,
            "TRACE": -999 if mode == "hidden-change" else value}


def main():
    mode = sys.argv[1] if len(sys.argv) == 2 else "correct"
    if mode not in ("correct", "hidden-change", "wrong") or len(sys.argv) > 2:
        raise ValueError("expected correct, hidden-change, or wrong")
    request = json.load(sys.stdin)
    actual = implementation(request["input"], mode)
    # Keep the full result in stderr diagnostics for this demonstration.
    print(json.dumps(actual), file=sys.stderr)
    print(json.dumps({"observation": actual["VALUE"]}))


if __name__ == "__main__":
    main()
