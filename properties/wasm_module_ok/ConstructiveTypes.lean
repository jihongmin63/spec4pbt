import properties.wasm_module_ok.ConstructiveTypesState
import properties.wasm_module_ok.CandidateTypesTrace
import properties.wasm_module_ok.EmptyStageValidation

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypes
open SpecTec properties.wasm_module_ok
open ConstructiveTypesState

structure Result (before : context) where
  types : List SpecTec.type
  after : context
  state : State after
  correct : ∀ n : Nat, SpecTecExecution.Eval SpecTec.Body
    (.call ⟨context,SpecTec.Call.Types_ok before types⟩) n (.success (.of after)) n

def done (c : context) (state : State c) : Result c :=
  ⟨[],c,state,EmptyStageValidation.types_nil_total c⟩

def cons (c : context) (state : State c) (x : Choice c state)
    (tail : Result (output c state x)) : Result c :=
  ⟨.RecT x.val :: tail.types,tail.after,tail.state,fun n =>
    CandidateTypesTrace.types_ok_cons_of_calls c (output c state x) tail.after (.RecT x.val)
      tail.types n n n (CandidateTypesTrace.type_ok_of_rectype c (output c state x) x.val n n
        (execute c state x n)) (tail.correct n)⟩

/-- Structural iteration over any finite number of recursive groups. Every
continuation receives the state established by the actual preceding output. -/
def sized : Nat → (c : context) → State c → Gen (Result c)
  | 0,c,state => pure (done c state)
  | n+1,c,state => do
    let x ← choose c state
    let rest ← sized n (output c state x) (advance c state x)
    pure (cons c state x rest)

def generate (c : context) (state : State c) : Gen (Result c) := do
  let count ← Gen.arbNat
  sized count c state

def types (c : context) (state : State c) : Gen (List SpecTec.type) :=
  Result.types <$> generate c state

theorem sized_audit (count : Nat) (c : context) (state : State c) :
    ConstructiveGenAudit.Structural (sized count c state) := by
  induction count generalizing c with
  | zero => trivial
  | succ n ih => exact ⟨choose_audit c state,fun x => ⟨ih _ _,fun _ => trivial⟩⟩

theorem generate_audit (c : context) (state : State c) : ConstructiveGenAudit.Structural (generate c state) :=
  ⟨ConstructiveGenAudit.arbNat_audit,fun n => sized_audit n c state⟩

theorem generate_total (c : context) (state : State c) : Gen.total (generate c state) :=
  ConstructiveGenAudit.audit_total _ (generate_audit c state)

theorem sized_length (count : Nat) (c : context) (state : State c) (out : Result c)
    (h : Gen.support (sized count c state) out) : out.types.length = count := by
  induction count generalizing c with
  | zero => have he : out = done c state := h; subst out; rfl
  | succ n ih =>
    obtain ⟨x,_,tail,ht,rfl⟩ := h
    simpa [cons] using congrArg Nat.succ (ih _ _ tail ht)

theorem sized_complete (c result : context) (state : State c) (ts : List SpecTec.type)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Types_ok c ts⟩) start (.success (.of result)) finish) :
    ∃ out : Result c, Gen.support (sized ts.length c state) out ∧
      out.types = ts ∧ out.after = result := by
  induction ts generalizing c result start finish with
  | nil =>
    have he := ValidatedTypeChain.types_ok_nil_eq c result start finish h
    exact ⟨done c state,rfl,rfl,he.symm⟩
  | cons t ts ih =>
    cases t with
    | RecT sts =>
      obtain ⟨middle,next,hhead,htail⟩ := TypesPrefixValidation.types_ok_cons_trace c result (.RecT sts) ts start finish h
      have hrect := TypesPrefixValidation.type_ok_rectype_trace c next sts start middle hhead
      let x : Choice c state := ⟨sts,original_choice c next state sts start middle hrect⟩
      have hnext : next = output c state x :=
        ConstructiveFreshCompleteness.original_closed c next sts start middle hrect (bound c state x)
      rw [hnext] at htail
      obtain ⟨tail,hs,hsyn,hout⟩ := ih (output c state x) result (advance c state x) middle finish htail
      refine ⟨cons c state x tail,?_,?_,hout⟩
      · exact ⟨x,choose_covers c state x,tail,hs,rfl⟩
      · simp [cons,x,hsyn]

theorem generate_complete (c result : context) (state : State c) (ts : List SpecTec.type)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Types_ok c ts⟩) start (.success (.of result)) finish) :
    ∃ out : Result c, Gen.support (generate c state) out ∧ out.types = ts ∧ out.after = result := by
  obtain ⟨out,hg,hs,ho⟩ := sized_complete c result state ts start finish h
  exact ⟨out,⟨ts.length,by simp,hg⟩,hs,ho⟩

/-- Exact support for the ORIGINAL Types_ok relation, with arbitrary group
count, arbitrary group size, every raw alias and both fresh/copy classes. -/
theorem types_exact (c : context) (state : State c) (ts : List SpecTec.type) (n : Nat) :
    Gen.support (types c state) ts ↔ ∃ result : context,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨context,SpecTec.Call.Types_ok c ts⟩) n (.success (.of result)) n := by
  constructor
  · rintro ⟨out,_,rfl⟩
    exact ⟨out.after,out.correct n⟩
  · rintro ⟨result,h⟩
    obtain ⟨out,hg,hs,_⟩ := generate_complete c result state ts n n h
    exact ⟨out,hg,hs.symm⟩

def fromEmpty (c : context) (hc : c.TYPES = []) : Gen (Result c) := generate c (empty c hc)

end properties.wasm_module_ok.ConstructiveTypes
