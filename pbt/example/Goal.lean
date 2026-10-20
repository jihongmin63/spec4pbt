import pbt.CorrectGen
import pbt.example.Property

namespace ExampleGoals

def Property : Prop := Example.property

abbrev Input := Nat

def Premise : Input → Prop := ExampleSpec.Valid

def Target : Input → Prop := fun n => n + 0 = n

abbrev Candidate := {input : Input // Premise input}

def Support (gen : Gen Input) (input : Input) : Prop :=
  Gen.support gen input

abbrev CorrectGen (P : Input → Prop) := _root_.CorrectGen P

def Sound (gen : Gen Input) : Prop :=
  ∀ input, Support gen input → Premise input

def Complete (gen : Gen Input) : Prop :=
  ∀ input, Premise input → Support gen input

def Goal (gen : Gen Input) : Prop := Sound gen ∧ Complete gen

theorem property_iff : Property ↔ (∀ input : Input, Premise input → Target input) :=
  Iff.rfl

end ExampleGoals
