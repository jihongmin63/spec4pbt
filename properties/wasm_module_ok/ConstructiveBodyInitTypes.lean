import properties.wasm_module_ok.ConstructiveBodySimpleAtoms
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyInitTypes
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment

/-- Original BR_TABLE stack positions: count down from the arity to one,
leaving position zero for the branch selector. -/
def operandTypes (stack : inferresulttype) : Nat → List valtype
  | 0 => []
  | count+1 => PeekDecision.peekResult (count+1) stack :: operandTypes stack count

theorem prefix_length (stack : inferresulttype) (count : Nat) : (operandTypes stack count).length=count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [operandTypes,ih]

theorem prefix_backed (c : context) (stack : inferresulttype) (h : StackBacked c stack) (count : Nat) :
    ∀t∈operandTypes stack count,CandidateValMatch.InTableVal c t := by
  induction count with
  | zero => simp [operandTypes]
  | succ count ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · exact ConstructiveBodySimpleAtoms.peek_backed c stack h (count+1)
    · exact ih t ht

theorem interval_call (stack : inferresulttype) (count : Nat) (i start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List valtype,SpecTecCall.«$init_valtypes» stack i (i+count)⟩)
      start (.success (.of (operandTypes stack count))) start := by
  induction count generalizing i with
  | zero =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$init_valtypes_clauses» stack i i) ()) start (.success (.of ([] : List valtype))) start
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«$init_valtypes:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (show ¬i<i from Nat.lt_irrefl i))
    apply SpecTecExecution.firstSuccess_cons_success
    exact SpecTecExecution.Eval.pure _
  | succ count ih =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$init_valtypes_clauses» stack i (i+(count+1))) ()) start (.success (.of _)) start
    apply SpecTecExecution.firstSuccess_cons_success
    unfold SpecTec.«$init_valtypes:clause:0»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (show i<i+(count+1) from by omega))
    have hd : (Int.ofNat (i+(count+1))-Int.ofNat i)=Int.ofNat (count+1) := by
      change (Int.ofNat i + Int.ofNat (count+1))-Int.ofNat i=Int.ofNat (count+1)
      omega
    rw [hd]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp only [decide_eq_true_eq]; exact Int.natCast_nonneg _))
    simp only [Int.toNat?]
    apply SpecTecExecution.Eval.bind_success (PeekDecision.peek_total (count+1) stack start)
    have recur := ih (i+1)
    have he : (i+1)+count=i+(count+1) := by omega
    rw [he] at recur
    apply SpecTecExecution.Eval.bind_success recur
    exact SpecTecExecution.Eval.pure _

theorem zero_call (stack : inferresulttype) (count start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List valtype,SpecTecCall.«$init_valtypes» stack 0 count⟩)
      start (.success (.of (operandTypes stack count))) start := by
  simpa only [Nat.zero_add] using interval_call stack count 0 start

theorem zero_exact (stack : inferresulttype) (count : Nat) (ts : List valtype) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List valtype,SpecTecCall.«$init_valtypes» stack 0 count⟩)
      start (.success (.of ts)) finish ↔ ts=operandTypes stack count ∧ finish=start := by
  constructor
  · intro h
    obtain ⟨he,hn⟩ := SpecTecExecution.eval_deterministic (by intro request a b h; cases h) h (zero_call stack count start)
    cases he; exact ⟨rfl,hn⟩
  · rintro ⟨rfl,hn⟩; subst finish; exact zero_call stack count start

#print axioms zero_exact
end properties.wasm_module_ok.ConstructiveBodyInitTypes
