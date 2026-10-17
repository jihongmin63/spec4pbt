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

/- Typed, executable refinement of SpecTecExecution. Embedded after that library. -/
set_option autoImplicit false

namespace SpecTecExecution

universe u

def Outcome.pack {α : Type} : Outcome α → Outcome Value
  | .success value => .success (.of value)
  | .unmatch => .unmatch
  | .abort message => .abort message

/-- Keeping the output index makes bind executable without dynamic casts. -/
inductive ExecutablePlan (Call : Type → Type u) : Type → Type (max u 1) where
  | pure {α : Type} (value : α) : ExecutablePlan Call α
  | unmatch {α : Type} : ExecutablePlan Call α
  | abort {α : Type} (message : String) : ExecutablePlan Call α
  | freshId : ExecutablePlan Call String
  | call {α : Type} (request : Call α) : ExecutablePlan Call α
  | primitive {α : Type} (request : Call α) : ExecutablePlan Call α
  | guard (condition : Prop) [Decidable condition] : ExecutablePlan Call Unit
  | bind {α β : Type} (plan : ExecutablePlan Call α)
      (next : α → ExecutablePlan Call β) : ExecutablePlan Call β
  | orElse {α : Type} (plan : ExecutablePlan Call α)
      (next : Unit → ExecutablePlan Call α) : ExecutablePlan Call α
  | notHold {α : Type} (plan : ExecutablePlan Call α) : ExecutablePlan Call Unit

def ExecutablePlan.erase {Call : Type → Type u} {α : Type} :
    ExecutablePlan Call α → Plan (Sigma Call)
  | .pure value => .pure value
  | .unmatch => .unmatch
  | .abort message => .abort message
  | .freshId => .freshId
  | .call request => .call ⟨_, request⟩
  | .primitive request => .primitive ⟨_, request⟩
  | @ExecutablePlan.guard _ condition _ => .guard condition
  | .bind plan next => .bind plan.erase (fun value => (next value).erase)
  | .orElse plan next => .orElse plan.erase (fun arg => (next arg).erase)
  | .notHold plan => .notHold plan.erase

def ExecutablePlan.require {Call : Type → Type u} (condition : Prop)
    [Decidable condition] (message : String) : ExecutablePlan Call Unit :=
  .orElse (.guard condition) (fun () => .abort message)

abbrev ExecutablePlan.Clause (Call : Type → Type u) (I α : Type) :=
  I → ExecutablePlan Call α

def ExecutablePlan.firstSuccess {Call : Type → Type u} {I α : Type}
    (clauses : List (ExecutablePlan.Clause Call I α)) (input : I) : ExecutablePlan Call α :=
  match clauses with
  | [] => .unmatch
  | clause :: rest => .orElse (clause input) (fun () => firstSuccess rest input)

structure ExecutableProgram (Call : Type → Type u) where
  body : {α : Type} → Call α → ExecutablePlan Call α
  primitive : Sigma Call → Outcome Value → Prop

def ExecutableProgram.erase {Call : Type → Type u} (program : ExecutableProgram Call) :
    Program (Sigma Call) where
  body request := (program.body request.2).erase
  primitive := program.primitive

/-- A partial implementation may decline a request, but every answer is certified. -/
structure PrimitiveRunner {Call : Type → Type u} (program : ExecutableProgram Call) where
  run : {α : Type} → Call α → Option (Outcome α)
  sound : ∀ {α : Type} (request : Call α) (outcome : Outcome α),
    run request = some outcome → program.primitive ⟨α, request⟩ outcome.pack

def PrimitiveRunner.unavailable {Call : Type → Type u} (program : ExecutableProgram Call) :
    PrimitiveRunner program where
  run _ := none
  sound _ _ h := by cases h

/-- Only `done` describes a semantic outcome. Neither incomplete result is unmatch. -/
inductive RunResult (α : Type) where
  | done (outcome : Outcome α) (supply : Nat)
  | outOfFuel
  | unsupportedPrimitive
  deriving DecidableEq, Repr

/-- Fuel bounds derivation height. Each recursive child receives one less fuel. -/
def runEval {Call : Type → Type u} (program : ExecutableProgram Call)
    (primitives : PrimitiveRunner program) :
    Nat → {α : Type} → ExecutablePlan Call α → Nat → RunResult α
  | 0, _, _, _ => .outOfFuel
  | fuel + 1, _, plan, supply =>
    match plan with
    | .pure value => .done (.success value) supply
    | .unmatch => .done .unmatch supply
    | .abort message => .done (.abort message) supply
    | .freshId => .done (.success (freshName supply)) (supply + 1)
    | .call request => runEval program primitives fuel (program.body request) supply
    | .primitive request => match primitives.run request with
      | some outcome => .done outcome supply
      | none => .unsupportedPrimitive
    | @ExecutablePlan.guard _ condition dec =>
      letI := dec
      if condition then .done (.success ()) supply else .done .unmatch supply
    | .bind plan next => match runEval program primitives fuel plan supply with
      | .done (.success value) middle => runEval program primitives fuel (next value) middle
      | .done .unmatch final => .done .unmatch final
      | .done (.abort message) final => .done (.abort message) final
      | .outOfFuel => .outOfFuel
      | .unsupportedPrimitive => .unsupportedPrimitive
    | .orElse plan next => match runEval program primitives fuel plan supply with
      | .done .unmatch _ => runEval program primitives fuel (next ()) supply
      | .done (.success value) final => .done (.success value) final
      | .done (.abort message) final => .done (.abort message) final
      | .outOfFuel => .outOfFuel
      | .unsupportedPrimitive => .unsupportedPrimitive
    | .notHold plan => match runEval program primitives fuel plan supply with
      | .done .unmatch final => .done (.success ()) final
      | .done (.success _) final => .done .unmatch final
      | .done (.abort message) final => .done (.abort message) final
      | .outOfFuel => .outOfFuel
      | .unsupportedPrimitive => .unsupportedPrimitive

theorem runEval_sound {Call : Type → Type u} (program : ExecutableProgram Call)
    (primitives : PrimitiveRunner program) (fuel : Nat) {α : Type}
    (plan : ExecutablePlan Call α) (start : Nat) (outcome : Outcome α) (final : Nat)
    (h : runEval program primitives fuel plan start = .done outcome final) :
    Eval program.erase plan.erase start outcome.pack final := by
  induction fuel generalizing α plan start outcome final with
  | zero => cases h
  | succ fuel ih =>
    cases plan with
    | pure value => cases h; exact .pure value
    | unmatch => cases h; exact .unmatch
    | abort message => cases h; exact .abort message
    | freshId => cases h; exact .freshId
    | call request => exact .call (ih _ _ _ _ h)
    | primitive request =>
      simp only [runEval] at h
      cases hr : primitives.run request with
      | none => simp [hr] at h
      | some value =>
        have hp := primitives.sound request value hr
        simp only [hr] at h
        cases h
        exact .primitive hp
    | guard condition =>
      simp only [runEval] at h
      split at h
      · cases h; exact .guard_true ‹condition›
      · cases h; exact .guard_false ‹¬ condition›
    | bind plan next =>
      simp only [runEval] at h
      cases hr : runEval program primitives fuel plan start with
      | outOfFuel => simp [hr] at h
      | unsupportedPrimitive => simp [hr] at h
      | done first middle =>
        cases first with
        | success value =>
          simp only [hr] at h
          exact .bind_success (ih _ _ _ _ hr) (ih _ _ _ _ h)
        | unmatch =>
          simp only [hr] at h; cases h
          exact .bind_unmatch (ih _ _ _ _ hr)
        | abort message =>
          simp only [hr] at h; cases h
          exact .bind_abort (ih _ _ _ _ hr)
    | orElse plan next =>
      simp only [runEval] at h
      cases hr : runEval program primitives fuel plan start with
      | outOfFuel => simp [hr] at h
      | unsupportedPrimitive => simp [hr] at h
      | done first middle =>
        cases first with
        | success value =>
          simp only [hr] at h; cases h
          exact .orElse_success (ih _ _ _ _ hr)
        | unmatch =>
          simp only [hr] at h
          exact .orElse_unmatch (ih _ _ _ _ hr) (ih _ _ _ _ h)
        | abort message =>
          simp only [hr] at h; cases h
          exact .orElse_abort (ih _ _ _ _ hr)
    | notHold plan =>
      simp only [runEval] at h
      cases hr : runEval program primitives fuel plan start with
      | outOfFuel => simp [hr] at h
      | unsupportedPrimitive => simp [hr] at h
      | done first middle =>
        cases first with
        | success value =>
          simp only [hr] at h; cases h
          exact .notHold_unmatch (ih _ _ _ _ hr)
        | unmatch =>
          simp only [hr] at h; cases h
          exact .notHold_success (ih _ _ _ _ hr)
        | abort message =>
          simp only [hr] at h; cases h
          exact .notHold_abort (ih _ _ _ _ hr)

/-- A completed computation is unchanged by increasing its fuel. -/
theorem runEval_mono {Call : Type → Type u} (program : ExecutableProgram Call)
    (primitives : PrimitiveRunner program) {fuel more : Nat} (le : fuel ≤ more)
    {α : Type} (plan : ExecutablePlan Call α) (start : Nat)
    (outcome : Outcome α) (final : Nat)
    (h : runEval program primitives fuel plan start = .done outcome final) :
    runEval program primitives more plan start = .done outcome final := by
  induction fuel generalizing more α plan start outcome final with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => cases le
    | succ more =>
      have le' := Nat.le_of_succ_le_succ le
      cases plan with
      | pure value | unmatch | abort message | freshId | primitive request | guard condition =>
        exact h
      | call request => exact ih le' _ _ _ _ h
      | bind plan next =>
        simp only [runEval] at h ⊢
        cases hr : runEval program primitives fuel plan start with
        | outOfFuel => simp [hr] at h
        | unsupportedPrimitive => simp [hr] at h
        | done first middle =>
          rw [ih le' _ _ _ _ hr]
          cases first with
          | success value => exact ih le' _ _ _ _ (by simpa only [hr] using h)
          | unmatch | abort message => simpa only [hr] using h
      | orElse plan next =>
        simp only [runEval] at h ⊢
        cases hr : runEval program primitives fuel plan start with
        | outOfFuel => simp [hr] at h
        | unsupportedPrimitive => simp [hr] at h
        | done first middle =>
          rw [ih le' _ _ _ _ hr]
          cases first with
          | unmatch => exact ih le' _ _ _ _ (by simpa only [hr] using h)
          | success value | abort message => simpa only [hr] using h
      | notHold plan =>
        simp only [runEval] at h ⊢
        cases hr : runEval program primitives fuel plan start with
        | outOfFuel => simp [hr] at h
        | unsupportedPrimitive => simp [hr] at h
        | done first middle =>
          rw [ih le' _ _ _ _ hr]
          simpa only [hr] using h

end SpecTecExecution


set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

set_option autoImplicit false
set_option linter.unusedVariables false

class SpecTecPrint (α : Type) where
  print? : α → Option String

def specTecPrintFiltered (parts : List (Option String)) : Option String :=
  match parts.filterMap id with
  | [] => none
  | present => some (" ".intercalate present)

def specTecPrintSequence (parts : List (Option String)) : Option String :=
  some (" ".intercalate (parts.map (fun part => part.getD "")))

def specTecPrintFuse (left right : Option String) : Option String :=
  some (left.getD "" ++ right.getD "")

def specTecPrintFinish (fragment : Option String) : String :=
  fragment.getD ""

def specTecPrintDecimalByte (value : Nat) : String :=
  String.ofList
    [ Char.ofNat (48 + value / 100),
      Char.ofNat (48 + (value / 10) % 10),
      Char.ofNat (48 + value % 10) ]

def specTecPrintEscapeByte (byte : UInt8) : String :=
  let value := byte.toNat
  match value with
  | 34 => "\\\""
  | 92 => "\\\\"
  | 10 => "\\n"
  | 9 => "\\t"
  | 13 => "\\r"
  | 8 => "\\b"
  | value =>
      if 32 ≤ value ∧ value ≤ 126 then String.singleton (Char.ofNat value)
      else "\\" ++ specTecPrintDecimalByte value

def specTecPrintEscapeText (value : String) : String :=
  value.toUTF8.foldl (fun result byte => result ++ specTecPrintEscapeByte byte) ""

def specTecTextSetInsert (value : String) : List String → List String
  | [] => [value]
  | head :: tail =>
      if value < head then value :: head :: tail
      else if head < value then head :: specTecTextSetInsert value tail
      else head :: tail

def specTecTextSetNormalize (values : List String) : List String :=
  values.foldr specTecTextSetInsert []

def specTecTextSetUnion (left right : List String) : List String :=
  specTecTextSetNormalize (left ++ right)

def specTecTextSetDiff (left right : List String) : List String :=
  let normalizedRight := specTecTextSetNormalize right
  (specTecTextSetNormalize left).filter (fun value => !normalizedRight.contains value)

def specTecTextSetIntersect (left right : List String) : List String :=
  let normalizedRight := specTecTextSetNormalize right
  (specTecTextSetNormalize left).filter (fun value => normalizedRight.contains value)

instance : SpecTecPrint Bool :=
  ⟨fun value => some (if value then "true" else "false")⟩

instance : SpecTecPrint Nat := ⟨fun value => some (toString value)⟩

instance : SpecTecPrint Int := ⟨fun value => some (toString value)⟩

instance : SpecTecPrint String :=
  ⟨fun value => some (specTecPrintEscapeText value)⟩

def specTecPrintList {α : Type} [SpecTecPrint α]
    (value : List α) : Option String :=
  match value with
  | [] => some ""
  | head :: tail => do
      let printedHead ← SpecTecPrint.print? head
      let printedTail ← specTecPrintList tail
      return match tail with
        | [] => printedHead
        | _ => printedHead ++ " " ++ printedTail
termination_by structural value

instance {α : Type} [SpecTecPrint α] : SpecTecPrint (List α) :=
  ⟨specTecPrintList⟩

def specTecPrintOption {α : Type} [SpecTecPrint α]
    (value : Option α) : Option String :=
  match value with
  | none => some ""
  | some item => SpecTecPrint.print? item

instance {α : Type} [SpecTecPrint α] : SpecTecPrint (Option α) :=
  ⟨specTecPrintOption⟩

instance {α β : Type} [SpecTecPrint α] [SpecTecPrint β] :
    SpecTecPrint (α × β) :=
  ⟨fun value => do
    let left ← SpecTecPrint.print? value.1
    let right ← SpecTecPrint.print? value.2
    return "(" ++ left ++ ", " ++ right ++ ")"⟩

namespace SpecTec

-- SpecTecModule:decl:begin:0
structure result : Type where
  («VALUE» : _root_.Int)
  («TRACE» : _root_.Int)
deriving _root_.DecidableEq
-- SpecTecModule:decl:end:0

-- SpecTecModule:decl:begin:1
set_option inductive.autoPromoteIndices false in
inductive SpecTecCall : Type → Type 1 where
  | Eval (input0 : _root_.Int) : SpecTecCall result
-- SpecTecModule:decl:end:1

-- SpecTecModule:decl:begin:2
abbrev SpecTecRequest := Sigma SpecTecCall
-- SpecTecModule:decl:end:2

-- SpecTecModule:decl:begin:3
noncomputable def «Eval:clause:0» (input0 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n : _root_.Int := input0; (.pure ((({ VALUE := (n + (_root_.Int.ofNat (1 : _root_.Nat))), TRACE := n } : result) : result))))
-- SpecTecModule:decl:end:3

-- SpecTecModule:decl:begin:4
noncomputable def Eval_clauses (input0 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Eval:clause:0»  input0)]
-- SpecTecModule:decl:end:4

-- SpecTecModule:decl:begin:5
noncomputable def specTecBody (request : SpecTecRequest) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  match request with
  | ⟨_, @SpecTecCall.Eval input0⟩ =>  SpecTecExecution.firstSuccess (Eval_clauses input0) ()
-- SpecTecModule:decl:end:5

-- SpecTecModule:decl:begin:6
noncomputable def specTecProgram : SpecTecExecution.Program.{1} SpecTecRequest :=
  ⟨specTecBody, fun _ _ => False⟩
-- SpecTecModule:decl:end:6

-- SpecTecModule:decl:begin:7
noncomputable def Eval (arg0 : _root_.Int) (arg1 : result) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨result, SpecTecCall.Eval arg0⟩) 0 (.success (.of (arg1))) finalSupply

namespace Notation.Eval
scoped notation:50 x0:51 " ~> " x1:51 => _root_.SpecTec.Eval x0 x1
end Notation.Eval
-- SpecTecModule:decl:end:7

end SpecTec
