# P4 instantiation progress

`progress.watsup` states that a program accepted by `Program_ok` can be
instantiated by `Program_inst`. `observations.toml` selects instantiation as an
external relation with status-only observation.

From the repository root:

```sh
python3 -m pbt.property plan \
  --spec p4-spectec/spec --property examples/p4_progress/progress.watsup \
  --name instantiation_progress --config examples/p4_progress/observations.toml
```

This example provides the frontend/planning inputs. Certified execution needs
the chosen implementation adapter, native/external-type codecs, property and
reference-run proofs, and a certified generator. The [property guide](../../docs/property-clauses.md#type-soundness-successful-instantiation-after-typing)
explains the generated Lean contract and current execution boundary.
