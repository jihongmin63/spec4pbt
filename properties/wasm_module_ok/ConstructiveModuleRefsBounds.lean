import properties.wasm_module_ok.ConstructiveModuleEnvironment
import properties.wasm_module_ok.ConstructiveRefs
import properties.wasm_module_ok.ConstructiveFreeModule
import properties.wasm_module_ok.ConstConstructiveTrace
import properties.wasm_module_ok.ConstRefFuncEffect
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleRefsBounds
open SpecTec properties.wasm_module_ok SpecTecExecution

def allFunctions (c : context) : SpecTec.free :=
  {properties.wasm_module_not_ok.Rejection.emptyFree with FUNCS:=.«`{ % `}» (List.range c.FUNCS.length)}

theorem allFunctions_has (c : context) (x : Nat) (hx : x<c.FUNCS.length) :
    FreeUnionValidation.HasFunc (allFunctions c) x := by
  simpa [FreeUnionValidation.HasFunc,allFunctions] using hx

theorem local_frame (c out : context) (x : Nat) (h : LocalInitValidation.initLocalResult c x=some out) : out.FUNCS=c.FUNCS := by
  cases hx : c.LOCALS[x]? with
  | none => simp [LocalInitValidation.initLocalResult,hx] at h
  | some lt =>
    cases lt
    simp [LocalInitValidation.initLocalResult,hx] at h
    cases h;rfl

theorem locals_frame (c out : context) (xs : List Nat) (h : LocalInitValidation.initLocalsResult c xs=some out) : out.FUNCS=c.FUNCS := by
  induction xs generalizing c with
  | nil => cases h;rfl
  | cons x xs ih =>
    cases hx : LocalInitValidation.initLocalResult c x with
    | none => simp [LocalInitValidation.initLocalsResult,hx] at h
    | some next =>
      have ht : LocalInitValidation.initLocalsResult next xs=some out := by
        simpa [LocalInitValidation.initLocalsResult,hx] using h
      exact (ih next ht).trans (local_frame c next x hx)

theorem trace_bound {c out : context} {stack finalStack : inferresulttype} {xs : List instr} {n finish : Nat}
    (h : ConstConstructiveTrace.Trace c stack xs out finalStack n finish) (x : Nat)
    (hx : instr.«REF.FUNC» x∈xs) : x<c.FUNCS.length := by
  induction h with
  | nil => simp at hx
  | @cons c next finalContext stack popped pushed finalStack i rest effect n n1 n2 n3 n4 finish hi hl hp hq ht ih =>
    rcases List.mem_cons.mp hx with he|hm
    · subst i
      obtain ⟨dt,hget,_⟩ := (ConstRefFuncEffect.ref_func_instruction_iff c stack x effect n n1).1 hi
      exact (List.getElem?_eq_some_iff.mp hget).1
    · have hb := ih hm
      have hf := locals_frame c next effect.2
        ((LocalInitValidation.init_locals_success_iff_result c effect.2 next n1 n2).1 hl).1
      simpa [hf] using hb

theorem constant_bound (c : context) (t : valtype) (xs : List instr) (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨Unit,SpecTecCall.Const_ok c t xs⟩) n (.success (.of ())) finish)
    (x : Nat) (hx : instr.«REF.FUNC» x∈xs) : x<c.FUNCS.length := by
  obtain ⟨_,stack,indices,ell,middle,hseq,_⟩ := (ConstExactSyntaxBoundary.const_ok_trace_iff c t xs n finish).1 h
  obtain ⟨_,out,htr⟩ := (ConstConstructiveTrace.instrs_success_iff_trace xs c (.NoEllipses,[]) (stack,indices) n middle).1 hseq
  exact trace_bound htr x hx

/-- Every original successful initializer remains available in the maximal
bounded-reference prestage. Its own syntax later realizes final exact REFS. -/
theorem constant_all (c : context) (t : valtype) (xs : List instr) (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨Unit,SpecTecCall.Const_ok c t xs⟩) n (.success (.of ())) finish) :
    Eval specTecProgram (.call ⟨Unit,SpecTecCall.Const_ok {c with REFS:=allFunctions c} t xs⟩) n (.success (.of ())) finish :=
  ConstructiveRefs.const_ok_replace_refs c (allFunctions c) t xs n finish
    (fun x hx => allFunctions_has c x (constant_bound c t xs n finish h x hx)) h
#print axioms constant_all
end properties.wasm_module_ok.ConstructiveModuleRefsBounds
