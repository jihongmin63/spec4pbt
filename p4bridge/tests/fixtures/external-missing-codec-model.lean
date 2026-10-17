structure State where
  value : Nat
  deriving DecidableEq

local instance concrete : SpecTecExternTypes where
  json := Nat
  archState := State
  objectState := Nat
  decEqJson := inferInstance
  decEqArchState := inferInstance
  decEqObjectState := inferInstance
