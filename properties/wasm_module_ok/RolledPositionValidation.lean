import properties.wasm_module_ok.RectypePositionValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RolledPositionValidation

open properties.wasm_module_not_ok.Rejection

theorem rolledDefs_get?
    (rect : SpecTec.rectype) (base count i : Nat)
    (hi : i < count) :
    (rolledDefs rect base count)[i]? =
      some (.DefT rect (base + i)) := by
  induction count generalizing base i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => simp [rolledDefs]
      | succ j =>
          have hj : j < count := by omega
          change (rolledDefs rect (base + 1) count)[j]? =
            some (.DefT rect (base + (j + 1)))
          rw [ih (base + 1) j hj]
          have heq : base + 1 + j = base + (j + 1) := by omega
          rw [heq]

theorem rollDeftypes_get?
    (x : Nat) (sts : List SpecTec.subtype) (i : Nat)
    (hi : i < sts.length) :
    (rollDeftypes x (.RecT sts))[i]? =
      some (.DefT (.RecT (rollSubtypes sts x (sts.length + x))) i) := by
  simpa [rollDeftypes, rollRectypeAt, rollRectype, rollSubtypes]
    using rolledDefs_get?
      (.RecT (rollSubtypes sts x (sts.length + x))) 0
      (rollSubtypes sts x (sts.length + x)).length i
      (by simpa [rollSubtypes] using hi)

end properties.wasm_module_ok.RolledPositionValidation
