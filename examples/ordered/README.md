# Ordered relation properties

- `spec.watsup`, `properties.watsup`: reference relations and property clauses.
- `observations.toml`: external relation outputs visible to the AL checker.
- `implementations/`: separate correct, zero-output and rejecting bindings.
- `adapter.py`, `target.py`: adapter protocol and the small native target.
- `templates/`: Lean property/reference-run proofs and exact-support generators.
- `run.py`: instantiate a named example, certify it and execute its adapter.

From the repository root:

```sh
python3 -m examples.ordered.run \
  --property progress --bundle examples/ordered/GeneratedProgress \
  --output test_cases/property-progress --count 4 --size 5 --seed 0
```

Choose a fresh bundle and output path on each invocation. Other properties are
`positive`, `internal_positive`, `chain` and `independent`. `--mode zero` and
`--mode reject` select intentionally incorrect implementations. The property
determines whether the changed behavior is observable and fails the case.

See the [property guide](../../docs/property-clauses.md) for custom bundles,
manual collection, trace rechecking and rerunning another implementation.
