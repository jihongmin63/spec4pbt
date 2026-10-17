/- Relational ordered execution with a shared fresh supply.
   SpecTecRunEval supplies the optional executable refinement. -/
set_option autoImplicit false

namespace SpecTecExecution

universe u v w

inductive Outcome (α : Type v) where
  | success (value : α)
  | unmatch
  | abort (message : String)
  deriving DecidableEq, Repr

inductive Value : Type 1 where
  | of {α : Type} (value : α)

inductive Plan (Call : Type u) : Type (max u 1) where
  | pure {α : Type} (value : α) : Plan Call
  | unmatch : Plan Call
  | abort (message : String) : Plan Call
  | freshId : Plan Call
  | call (request : Call) : Plan Call
  | primitive (request : Call) : Plan Call
  | guard (condition : Prop) : Plan Call
  | bind {α : Type} (plan : Plan Call) (next : α → Plan Call) : Plan Call
  | orElse (plan : Plan Call) (next : Unit → Plan Call) : Plan Call
  | notHold (plan : Plan Call) : Plan Call

structure Program (Call : Type u) where
  body : Call → Plan Call
  primitive : Call → Outcome Value → Prop

def freshName (supply : Nat) : String := "FRESH__" ++ toString supply

/- Individual outcomes retain their consumed supply. Failed alternatives do not
   commit that supply to the fallback. -/
inductive Eval {Call : Type u} (program : Program Call) :
    Plan Call → Nat → Outcome Value → Nat → Prop where
  | pure {α : Type} {n : Nat} (value : α) :
      Eval program (.pure value) n (.success (.of value)) n
  | unmatch {n : Nat} : Eval program .unmatch n .unmatch n
  | abort {n : Nat} (message : String) : Eval program (.abort message) n (.abort message) n
  | freshId {n : Nat} : Eval program .freshId n (.success (.of (freshName n))) (n + 1)
  | call {request : Call} {outcome : Outcome Value} {start final : Nat} :
      Eval program (program.body request) start outcome final →
      Eval program (.call request) start outcome final
  | primitive {request : Call} {outcome : Outcome Value} {n : Nat} :
      program.primitive request outcome → Eval program (.primitive request) n outcome n
  | guard_true {condition : Prop} {n : Nat} : condition →
      Eval program (.guard condition) n (.success (.of ())) n
  | guard_false {condition : Prop} {n : Nat} : ¬ condition →
      Eval program (.guard condition) n .unmatch n
  | bind_success {α : Type} {plan : Plan Call} {next : α → Plan Call}
      {value : α} {outcome : Outcome Value} {start middle final : Nat} :
      Eval program plan start (.success (.of value)) middle →
      Eval program (next value) middle outcome final →
      Eval program (.bind plan next) start outcome final
  | bind_unmatch {α : Type} {plan : Plan Call} {next : α → Plan Call} {start final : Nat} :
      Eval program plan start .unmatch final →
      Eval program (.bind plan next) start .unmatch final
  | bind_abort {α : Type} {plan : Plan Call} {next : α → Plan Call}
      {message : String} {start final : Nat} :
      Eval program plan start (.abort message) final →
      Eval program (.bind plan next) start (.abort message) final
  | orElse_success {plan : Plan Call} {next : Unit → Plan Call} {value : Value}
      {start final : Nat} :
      Eval program plan start (.success value) final →
      Eval program (.orElse plan next) start (.success value) final
  | orElse_unmatch {plan : Plan Call} {next : Unit → Plan Call} {outcome : Outcome Value}
      {start failedFinal final : Nat} :
      Eval program plan start .unmatch failedFinal →
      Eval program (next ()) start outcome final →
      Eval program (.orElse plan next) start outcome final
  | orElse_abort {plan : Plan Call} {next : Unit → Plan Call} {message : String}
      {start final : Nat} :
      Eval program plan start (.abort message) final →
      Eval program (.orElse plan next) start (.abort message) final
  | notHold_success {plan : Plan Call} {start final : Nat} :
      Eval program plan start .unmatch final →
      Eval program (.notHold plan) start (.success (.of ())) final
  | notHold_unmatch {plan : Plan Call} {value : Value} {start final : Nat} :
      Eval program plan start (.success value) final →
      Eval program (.notHold plan) start .unmatch final
  | notHold_abort {plan : Plan Call} {message : String} {start final : Nat} :
      Eval program plan start (.abort message) final →
      Eval program (.notHold plan) start (.abort message) final

abbrev Clause (Call : Type u) (I : Type w) := I → Plan Call

def require {Call : Type u} (condition : Prop) (message : String) : Plan Call :=
  .orElse (.guard condition) (fun () => .abort message)

def firstSuccess {Call : Type u} {I : Type w}
    (clauses : List (Clause Call I)) (input : I) : Plan Call :=
  match clauses with
  | [] => .unmatch
  | clause :: rest => .orElse (clause input) (fun () => firstSuccess rest input)

variable {Call : Type u} {I : Type w} {program : Program.{u} Call}

theorem firstSuccess_nil (input : I) (supply : Nat) :
    Eval program (firstSuccess ([] : List (Clause Call I)) input) supply .unmatch supply :=
  .unmatch

theorem firstSuccess_cons_success {clause : Clause Call I}
    {rest : List (Clause Call I)} {input : I} {value : Value} {start final : Nat}
    (h : Eval program (clause input) start (.success value) final) :
    Eval program (firstSuccess (clause :: rest) input) start (.success value) final :=
  .orElse_success h

theorem firstSuccess_cons_unmatch {clause : Clause Call I}
    {rest : List (Clause Call I)} {input : I} {outcome : Outcome Value}
    {start failedFinal final : Nat}
    (h : Eval program (clause input) start .unmatch failedFinal)
    (tail : Eval program (firstSuccess rest input) start outcome final) :
    Eval program (firstSuccess (clause :: rest) input) start outcome final :=
  .orElse_unmatch h tail

theorem firstSuccess_cons_abort {clause : Clause Call I}
    {rest : List (Clause Call I)} {input : I} {message : String} {start final : Nat}
    (h : Eval program (clause input) start (.abort message) final) :
    Eval program (firstSuccess (clause :: rest) input) start (.abort message) final :=
  .orElse_abort h

def PrimitiveDeterministic (program : Program.{u} Call) : Prop :=
  ∀ request x y, program.primitive request x → program.primitive request y → x = y

theorem eval_deterministic (det : PrimitiveDeterministic program)
    {plan : Plan Call} {start leftFinal rightFinal : Nat} {left right : Outcome Value}
    (a : Eval program plan start left leftFinal)
    (b : Eval program plan start right rightFinal) : left = right ∧ leftFinal = rightFinal := by
  induction a generalizing right rightFinal with
  | pure => cases b; exact ⟨rfl, rfl⟩
  | unmatch => cases b; exact ⟨rfl, rfl⟩
  | abort => cases b; exact ⟨rfl, rfl⟩
  | freshId => cases b; exact ⟨rfl, rfl⟩
  | call _ ih => cases b with | call h => exact ih h
  | primitive h => cases b with | primitive h' => exact ⟨det _ _ _ h h', rfl⟩
  | guard_true h => cases b with
    | guard_true => exact ⟨rfl, rfl⟩
    | guard_false h' => exact False.elim (h' h)
  | guard_false h => cases b with
    | guard_true h' => exact False.elim (h h')
    | guard_false => exact ⟨rfl, rfl⟩
  | bind_success _ _ first second => cases b with
    | bind_success h k =>
      obtain ⟨e, s⟩ := first h
      cases e; cases s; exact second k
    | bind_unmatch h => cases (first h).1
    | bind_abort h => cases (first h).1
  | bind_unmatch _ ih => cases b with
    | bind_success h _ => cases (ih h).1
    | bind_unmatch h => exact ih h
    | bind_abort h => cases (ih h).1
  | bind_abort _ ih => cases b with
    | bind_success h _ => cases (ih h).1
    | bind_unmatch h => cases (ih h).1
    | bind_abort h => exact ih h
  | orElse_success _ ih => cases b with
    | orElse_success h => exact ih h
    | orElse_unmatch h _ => cases (ih h).1
    | orElse_abort h => cases (ih h).1
  | orElse_unmatch _ _ first second => cases b with
    | orElse_success h => cases (first h).1
    | orElse_unmatch _ k => exact second k
    | orElse_abort h => cases (first h).1
  | orElse_abort _ ih => cases b with
    | orElse_success h => cases (ih h).1
    | orElse_unmatch h _ => cases (ih h).1
    | orElse_abort h => exact ih h
  | notHold_success _ ih => cases b with
    | notHold_success h => exact ⟨rfl, (ih h).2⟩
    | notHold_unmatch h => cases (ih h).1
    | notHold_abort h => cases (ih h).1
  | notHold_unmatch _ ih => cases b with
    | notHold_success h => cases (ih h).1
    | notHold_unmatch h => exact ⟨rfl, (ih h).2⟩
    | notHold_abort h => cases (ih h).1
  | notHold_abort _ ih => cases b with
    | notHold_success h => cases (ih h).1
    | notHold_unmatch h => cases (ih h).1
    | notHold_abort h => exact ih h

theorem supply_monotone {plan : Plan Call} {start final : Nat} {outcome : Outcome Value}
    (h : Eval program plan start outcome final) : start ≤ final := by
  induction h with
  | freshId => exact Nat.le_succ _
  | bind_success _ _ first second => exact Nat.le_trans first second
  | orElse_unmatch _ _ _ second => exact second
  | call _ ih | bind_unmatch _ ih | bind_abort _ ih | orElse_success _ ih
    | orElse_abort _ ih | notHold_success _ ih | notHold_unmatch _ ih
    | notHold_abort _ ih => exact ih
  | _ => exact Nat.le_refl _

theorem unmatch_excludes_success (det : PrimitiveDeterministic program)
    {plan : Plan Call} {start failedFinal successFinal : Nat}
    (failed : Eval program plan start .unmatch failedFinal) (value : Value) :
    ¬ Eval program plan start (.success value) successFinal := by
  intro success
  cases (eval_deterministic det failed success).1

/- Failed clauses are independent attempts from the same starting supply. -/
inductive AllUnmatch (program : Program.{u} Call) (input : I) :
    List (Clause Call I) → Nat → Nat → Prop where
  | nil {supply : Nat} : AllUnmatch program input [] supply supply
  | cons {clause : Clause Call I} {rest : List (Clause Call I)}
      {start failedFinal final : Nat} :
      Eval program (clause input) start .unmatch failedFinal →
      AllUnmatch program input rest start final →
      AllUnmatch program input (clause :: rest) start final

inductive Selected (program : Program.{u} Call) (input : I) :
    List (Clause Call I) → Nat → Nat → Value → Nat → Prop where
  | here {clause : Clause Call I} {rest : List (Clause Call I)} {value : Value}
      {start final : Nat} :
      Eval program (clause input) start (.success value) final →
      Selected program input (clause :: rest) start 0 value final
  | next {clause : Clause Call I} {rest : List (Clause Call I)} {index : Nat} {value : Value}
      {start failedFinal final : Nat} :
      Eval program (clause input) start .unmatch failedFinal →
      Selected program input rest start index value final →
      Selected program input (clause :: rest) start (index + 1) value final

theorem firstSuccess_success_iff (clauses : List (Clause Call I))
    (input : I) (start : Nat) (value : Value) (final : Nat) :
    Eval program (firstSuccess clauses input) start (.success value) final ↔
      ∃ index, Selected program input clauses start index value final := by
  induction clauses generalizing start with
  | nil => constructor <;> intro h
           · cases h
           · obtain ⟨_, h⟩ := h; cases h
  | cons clause rest ih =>
    constructor
    · intro h; cases h with
      | orElse_success h => exact ⟨0, .here h⟩
      | orElse_unmatch h k =>
        obtain ⟨i, selected⟩ := (ih _).mp k
        exact ⟨i + 1, .next h selected⟩
    · rintro ⟨i, h⟩; cases h with
      | here h => exact .orElse_success h
      | next h k => exact .orElse_unmatch h ((ih _).mpr ⟨_, k⟩)

@[simp] theorem eval_call_iff {request : Call} {outcome : Outcome Value} {start final : Nat} :
    Eval program (.call request) start outcome final ↔
      Eval program (program.body request) start outcome final := by
  constructor
  · intro h; cases h with | call h => exact h
  · exact Eval.call

theorem firstSuccess_unmatch_iff (clauses : List (Clause Call I)) (input : I)
    (start final : Nat) :
    Eval program (firstSuccess clauses input) start .unmatch final ↔
      AllUnmatch program input clauses start final := by
  induction clauses generalizing start with
  | nil =>
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; exact .unmatch
  | cons clause rest ih =>
    constructor
    · intro h; cases h with
      | orElse_unmatch first tail => exact .cons first ((ih _).mp tail)
    · intro h; cases h with
      | cons first tail => exact .orElse_unmatch first ((ih _).mpr tail)

theorem firstSuccess_append_of_unmatch {prior rest : List (Clause Call I)}
    {input : I} {outcome : Outcome Value} {start failedFinal final : Nat}
    (failed : Eval program (firstSuccess prior input) start .unmatch failedFinal)
    (tail : Eval program (firstSuccess rest input) start outcome final) :
    Eval program (firstSuccess (prior ++ rest) input) start outcome final := by
  induction prior generalizing start with
  | nil => cases failed; exact tail
  | cons clause prior ih =>
    cases failed with
    | orElse_unmatch first failed => exact .orElse_unmatch first (ih failed tail)

end SpecTecExecution

/- Byte operations preserve the backend's existing valid-UTF8 fragment. -/
def specTecTextSlice (text : String) (start length : Nat) : String :=
  (String.fromUTF8? (text.toUTF8.extract start (start + length))).getD ""

abbrev specTecTextSliceValid (text : String) (start length : Nat) : Prop :=
  start + length ≤ text.utf8ByteSize ∧
  (String.fromUTF8? (text.toUTF8.extract start (start + length))).isSome = true

def specTecTextUpdate (text : String) (index : Nat) (replacement : String) : String :=
  specTecTextSlice text 0 index ++ replacement ++
    specTecTextSlice text (index + 1) (text.utf8ByteSize - index - 1)

abbrev specTecTextUpdateValid (text : String) (index : Nat) (replacement : String) : Prop :=
  index < text.utf8ByteSize ∧ replacement.utf8ByteSize = 1 ∧
  specTecTextSliceValid text 0 index ∧ specTecTextSliceValid text index 1 ∧
  specTecTextSliceValid text (index + 1) (text.utf8ByteSize - index - 1)
