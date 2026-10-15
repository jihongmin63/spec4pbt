import pbt.CorrectGen
import pbt.example.Property

namespace ExampleGoals

def Property : Prop := Example.property

abbrev Input := Nat

def Premise : Input → Prop := ExampleSpec.Valid

def Target : Input → Prop := fun n => n + 0 = n

abbrev Candidate := {input : Input // Premise input}

abbrev Generator := Spec4Pbt.Generator Input

def Support (gen : Generator) (input : Input) : Prop :=
  Spec4Pbt.Support gen input

abbrev CorrectGen (P : Input → Prop) := Spec4Pbt.CorrectGen P

def Sound (gen : Generator) : Prop :=
  ∀ size seed, Premise (gen size seed)

def Complete (gen : Generator) : Prop :=
  ∀ input, Premise input → ∃ size seed, gen size seed = input

def Goal (gen : Generator) : Prop := Sound gen ∧ Complete gen

theorem property_iff : Property ↔ (∀ input : Input, Premise input → Target input) :=
  Iff.rfl

end ExampleGoals
