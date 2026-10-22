# Ordered regression fixtures

These small specifications, properties, proof/generator templates, and target
adapters exercise the certified workflow. They are internal regression data;
actual property work belongs in `properties/` and `implementations/`.

Run from the repository root with fresh output paths:

```sh
python3 -m tests.ordered.run --property progress \
  --bundle out/scratch/OrderedProgress \
  --output out/results/ordered_progress/run-001 --count 4 --size 5 --seed 0
```

`--mode reject` exercises relation failure; `--property positive --mode zero`
exercises an observation value violation. This does not prove a full-P4 property.
