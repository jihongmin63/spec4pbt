import properties.wasm_module_ok.ReadyHeapMatchSimpleBase
import properties.wasm_module_ok.MatchSpecialBaseTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyHeapMatchBase

open properties.wasm_module_ok.ReadyHeapMatchSimpleBase

/-- The translated special-base clauses swap the operands once. A second
swap can only occur when both original operands are special bases. -/
def baseMatchFuel : Nat → SpecTec.heaptype → SpecTec.heaptype → Bool
  | 0, source, target => simpleBaseMatch source target
  | fuel + 1, source, target =>
      match source with
      | .NoneHT => baseMatchFuel fuel target .AnyHT
      | .NoFuncHT => baseMatchFuel fuel target .FuncHT
      | .NoExnHT => baseMatchFuel fuel target .ExnHT
      | .NoExternHT => baseMatchFuel fuel target .ExternHT
      | .BotHT => true
      | _ => simpleBaseMatch source target

def baseMatch (source target : SpecTec.heaptype) : Bool :=
  baseMatchFuel 2 source target

private theorem fixed_target_eval
    (dts : List SpecTec.deftype) (source target : SpecTec.heaptype)
    (n : Nat)
    (hsource : source ∈ HeaptypeValidation.baseHeaptypes)
    (htarget : target ∈ MatchSpecialBaseTotal.fixedBaseTargets) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        dts source target⟩)
      n (.success (.of (baseMatchFuel 1 source target))) n := by
  have hsimple := MatchSpecialBaseTotal.fixed_target_simple target htarget
  simp [HeaptypeValidation.baseHeaptypes] at hsource
  rcases hsource with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact simpleBaseMatch_eval dts .AnyHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchHeaptypeBasic.match_heaptype_none_total_of_any
      dts target (simpleBaseMatch target .AnyHT) n
      (simpleBaseMatch_eval dts target .AnyHT n hsimple)
  · exact simpleBaseMatch_eval dts .EqHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact simpleBaseMatch_eval dts .I31HT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact simpleBaseMatch_eval dts .StructHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact simpleBaseMatch_eval dts .ArrayHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact simpleBaseMatch_eval dts .FuncHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchHeaptypeBasic.match_heaptype_nofunc_total_of_func
      dts target (simpleBaseMatch target .FuncHT) n
      (simpleBaseMatch_eval dts target .FuncHT n hsimple)
  · exact simpleBaseMatch_eval dts .ExnHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchHeaptypeBasic.match_heaptype_noexn_total_of_exn
      dts target (simpleBaseMatch target .ExnHT) n
      (simpleBaseMatch_eval dts target .ExnHT n hsimple)
  · exact simpleBaseMatch_eval dts .ExternHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchHeaptypeBasic.match_heaptype_noextern_total_of_extern
      dts target (simpleBaseMatch target .ExternHT) n
      (simpleBaseMatch_eval dts target .ExternHT n hsimple)
  · exact MatchHeaptypeBasic.match_heaptype_bot_total dts target n

theorem baseMatch_eval
    (dts : List SpecTec.deftype) (source target : SpecTec.heaptype)
    (n : Nat)
    (hsource : source ∈ HeaptypeValidation.baseHeaptypes)
    (htarget : target ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        dts source target⟩)
      n (.success (.of (baseMatch source target))) n := by
  simp [HeaptypeValidation.baseHeaptypes] at hsource
  rcases hsource with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact simpleBaseMatch_eval dts .AnyHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchHeaptypeBasic.match_heaptype_none_total_of_any
      dts target (baseMatchFuel 1 target .AnyHT) n
      (fixed_target_eval dts target .AnyHT n htarget
        (by simp [MatchSpecialBaseTotal.fixedBaseTargets]))
  · exact simpleBaseMatch_eval dts .EqHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact simpleBaseMatch_eval dts .I31HT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact simpleBaseMatch_eval dts .StructHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact simpleBaseMatch_eval dts .ArrayHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact simpleBaseMatch_eval dts .FuncHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchHeaptypeBasic.match_heaptype_nofunc_total_of_func
      dts target (baseMatchFuel 1 target .FuncHT) n
      (fixed_target_eval dts target .FuncHT n htarget
        (by simp [MatchSpecialBaseTotal.fixedBaseTargets]))
  · exact simpleBaseMatch_eval dts .ExnHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchHeaptypeBasic.match_heaptype_noexn_total_of_exn
      dts target (baseMatchFuel 1 target .ExnHT) n
      (fixed_target_eval dts target .ExnHT n htarget
        (by simp [MatchSpecialBaseTotal.fixedBaseTargets]))
  · exact simpleBaseMatch_eval dts .ExternHT target n (by
      simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchHeaptypeBasic.match_heaptype_noextern_total_of_extern
      dts target (baseMatchFuel 1 target .ExternHT) n
      (fixed_target_eval dts target .ExternHT n htarget
        (by simp [MatchSpecialBaseTotal.fixedBaseTargets]))
  · exact MatchHeaptypeBasic.match_heaptype_bot_total dts target n

end properties.wasm_module_ok.ReadyHeapMatchBase
