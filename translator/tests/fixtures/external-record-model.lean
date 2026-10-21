local instance concrete : SpecTecExternTypes where
  json := Nat
  archState := Nat
  objectState := Nat
  decEqJson := inferInstance
  decEqArchState := inferInstance
  decEqObjectState := inferInstance

instance : Lean.ToJson SpecTec.payload where
  toJson value := Lean.toJson (α := Nat × Nat) (value.STATE, value.VALUE)

instance : Lean.FromJson SpecTec.payload where
  fromJson? json := do
    let (state, value) ← Lean.fromJson? (α := Nat × Nat) json
    pure { STATE := state, VALUE := value }
