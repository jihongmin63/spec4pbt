import properties.wasm_module_not_ok.MatchStrtypeMixed
import properties.wasm_module_not_ok.MatchStrtypeTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def matchStrtypeTrue (d : List SpecTec.deftype)
    (a b : SpecTec.strtype) (start finalSupply : Nat) : Prop :=
  match a, b with
  | .DefStructT x, .DefStructT y =>
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_structtype» d x y⟩)
        start (.success (.of true)) finalSupply
  | .DefArrayT x, .DefArrayT y =>
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_arraytype» d x y⟩)
        start (.success (.of true)) finalSupply
  | .DefFuncT x, .DefFuncT y =>
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_functype» d x y⟩)
        start (.success (.of true)) finalSupply
  | _, _ => False

theorem match_strtype_true_iff_trace (d : List SpecTec.deftype)
    (a b : SpecTec.strtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d a b⟩)
      start (.success (.of true)) finalSupply ↔
    matchStrtypeTrue d a b start finalSupply := by
  cases a with
  | DefStructT x =>
      cases b with
      | DefStructT y =>
          exact match_strtype_struct_true_iff d x y start finalSupply
      | DefArrayT y =>
          constructor
          · intro h
            have hdet := match_strtype_mixed_deterministic d
              (.DefStructT x) (.DefArrayT y) start finalSupply
              (.success (.of true)) (by simp [strtypeKind]) h
            cases hdet.1
          · intro hfalse
            cases hfalse
      | DefFuncT y =>
          constructor
          · intro h
            have hdet := match_strtype_mixed_deterministic d
              (.DefStructT x) (.DefFuncT y) start finalSupply
              (.success (.of true)) (by simp [strtypeKind]) h
            cases hdet.1
          · intro hfalse
            cases hfalse
  | DefArrayT x =>
      cases b with
      | DefStructT y =>
          constructor
          · intro h
            have hdet := match_strtype_mixed_deterministic d
              (.DefArrayT x) (.DefStructT y) start finalSupply
              (.success (.of true)) (by simp [strtypeKind]) h
            cases hdet.1
          · intro hfalse
            cases hfalse
      | DefArrayT y =>
          exact match_strtype_array_true_iff d x y start finalSupply
      | DefFuncT y =>
          constructor
          · intro h
            have hdet := match_strtype_mixed_deterministic d
              (.DefArrayT x) (.DefFuncT y) start finalSupply
              (.success (.of true)) (by simp [strtypeKind]) h
            cases hdet.1
          · intro hfalse
            cases hfalse
  | DefFuncT x =>
      cases b with
      | DefStructT y =>
          constructor
          · intro h
            have hdet := match_strtype_mixed_deterministic d
              (.DefFuncT x) (.DefStructT y) start finalSupply
              (.success (.of true)) (by simp [strtypeKind]) h
            cases hdet.1
          · intro hfalse
            cases hfalse
      | DefArrayT y =>
          constructor
          · intro h
            have hdet := match_strtype_mixed_deterministic d
              (.DefFuncT x) (.DefArrayT y) start finalSupply
              (.success (.of true)) (by simp [strtypeKind]) h
            cases hdet.1
          · intro hfalse
            cases hfalse
      | DefFuncT y =>
          exact match_strtype_func_true_iff d x y start finalSupply

end properties.wasm_module_not_ok.Rejection
