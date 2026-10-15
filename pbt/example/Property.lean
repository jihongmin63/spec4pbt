import specifications.Example

namespace Example

/-- The external program adds zero to a specification-valid input. -/
def property : Prop := ∀ n : Nat, ExampleSpec.Valid n → n + 0 = n

end Example
