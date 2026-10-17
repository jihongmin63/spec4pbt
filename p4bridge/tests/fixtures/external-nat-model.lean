local instance concrete : SpecTecExternTypes where
  json := Nat
  archState := Nat
  objectState := Nat
  decEqJson := inferInstance
  decEqArchState := inferInstance
  decEqObjectState := inferInstance

instance : Lean.ToJson SpecTec.archState := inferInstanceAs (Lean.ToJson Nat)
instance : Lean.FromJson SpecTec.archState := inferInstanceAs (Lean.FromJson Nat)
