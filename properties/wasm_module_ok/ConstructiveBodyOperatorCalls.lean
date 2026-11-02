import properties.wasm_module_ok.ConstructiveBodyOperatorTypes
import properties.wasm_module_ok.ConstructiveBodySimpleAtoms
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyOperatorCalls
open SpecTec properties.wasm_module_ok ConstructiveBodyOperatorTypes

theorem test (c : context) (stack : inferresulttype) (op : testop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.TEST op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (numericType op)] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.TEST op) 79 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:79» c stack (.TEST op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:79»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (numeric_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem compare (c : context) (stack : inferresulttype) (op : relop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.COMPARE op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (numericType op),.NumT (numericType op)] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.COMPARE op) 80 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:80» c stack (.COMPARE op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:80»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (numeric_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem binary (c : context) (stack : inferresulttype) (op : binop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BINOP op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (numericType op),.NumT (numericType op)] [.NumT (numericType op)] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.BINOP op) 82 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:82» c stack (.BINOP op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:82»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (numeric_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecTest (c : context) (stack : inferresulttype) (op : vtestop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.TEST» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.TEST» op) 85 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:85» c stack (.«VEC.TEST» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:85»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecUnary (c : context) (stack : inferresulttype) (op : vunop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.UNARY» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.UNARY» op) 86 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:86» c stack (.«VEC.UNARY» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:86»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecTernary (c : context) (stack : inferresulttype) (op : vternop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.TERNARY» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T,.VecT .V128T,.VecT .V128T] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.TERNARY» op) 88 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:88» c stack (.«VEC.TERNARY» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:88»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecCompare (c : context) (stack : inferresulttype) (op : vrelop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.COMPARE» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T,.VecT .V128T] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.COMPARE» op) 89 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:89» c stack (.«VEC.COMPARE» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:89»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecConvert (c : context) (stack : inferresulttype) (op : vcvtop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.CONVERT» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.CONVERT» op) 90 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:90» c stack (.«VEC.CONVERT» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:90»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecShift (c : context) (stack : inferresulttype) (op : vshiftop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.SHIFT» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T,.NumT .I32T] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.SHIFT» op) 91 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:91» c stack (.«VEC.SHIFT» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:91»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecBitmask (c : context) (stack : inferresulttype) (op : vbitmaskop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.BITMASK» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.BITMASK» op) 92 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:92» c stack (.«VEC.BITMASK» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:92»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecTestbits (c : context) (stack : inferresulttype) (op : vvtestop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.TESTBITS» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.TESTBITS» op) 93 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:93» c stack (.«VEC.TESTBITS» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:93»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecUnarybits (c : context) (stack : inferresulttype) (op : vvunop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.UNARYBITS» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.UNARYBITS» op) 94 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:94» c stack (.«VEC.UNARYBITS» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:94»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecBinarybits (c : context) (stack : inferresulttype) (op : vvbinop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.BINARYBITS» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T,.VecT .V128T] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.BINARYBITS» op) 95 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:95» c stack (.«VEC.BINARYBITS» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:95»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecTernarybits (c : context) (stack : inferresulttype) (op : vvternop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.TERNARYBITS» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T,.VecT .V128T,.VecT .V128T] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.TERNARYBITS» op) 96 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:96» c stack (.«VEC.TERNARYBITS» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:96»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem vecSplat (c : context) (stack : inferresulttype) (op : vsplatop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.SPLAT» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (vecLaneType op)] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.SPLAT» op) 97 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:97» c stack (.«VEC.SPLAT» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:97»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vec_lane_type_call op n)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem effect_unique (c : context) (stack : inferresulttype) (i : instr)
    (expected result : inferinstrtype) (n finish : Nat)
    (total : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩) n (.success (.of expected)) n)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩) n (.success (.of result)) finish) :
    result=expected ∧ finish=n := by
  obtain ⟨he,hn⟩ := SpecTecExecution.eval_deterministic (by intro request a b h; cases h) h total
  cases he
  exact ⟨rfl,hn⟩

#print axioms vecSplat
end properties.wasm_module_ok.ConstructiveBodyOperatorCalls
