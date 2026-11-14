import GeneratorRust
import Init.Data.Char.Ordinal

set_option autoImplicit false

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def textChars : Text → List Char
  | .Empty => []
  | .Cons scalar tail => Char.ofNat scalar.val :: textChars tail

def textValue (value : Text) : String := String.ofList (textChars value)

def charScalar (value : Char) : U32 :=
  UScalar.ofNatCore value.toNat (by exact UInt32.toNat_lt value.val)

def charChoice (value : Char) : U64 :=
  UScalar.ofNatCore value.ordinal.val (by
    have bounded := value.ordinal.isLt
    simp only [Char.numCodePoints] at bounded
    change value.ordinal.val < 18446744073709551616
    omega)

def textLiteral : List Char → Text
  | [] => .Empty
  | head :: tail => .Cons (charScalar head) (textLiteral tail)

def TextValid : Text → Prop
  | .Empty => True
  | .Cons scalar tail => scalar.val.isValidChar ∧ TextValid tail

@[simp] theorem charScalar_val (value : Char) : (charScalar value).val = value.toNat := by
  simp [charScalar]

@[simp] theorem charChoice_val (value : Char) : (charChoice value).val = value.ordinal.val := by
  simp [charChoice]

/-- Witnesses use valid scalars, so their native and Lean decoders agree. -/
theorem text_literal_valid (values : List Char) : TextValid (textLiteral values) := by
  induction values with
  | nil => trivial
  | cons head tail ih =>
      change (charScalar head).val.isValidChar ∧ TextValid (textLiteral tail)
      rw [charScalar_val]
      exact ⟨head.valid, ih⟩

theorem text_chars_roundtrip (values : List Char) : textChars (textLiteral values) = values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [textChars, textLiteral, ih]

/-- Every original String is represented exactly, including NUL and non-BMP scalars. -/
theorem text_roundtrip (value : String) : textValue (textLiteral value.toList) = value := by
  simp [textValue, text_chars_roundtrip]

/-- The scalar transformation used by Rust is inverse to the canonical choice ordinal. -/
theorem char_choice_decode (value : Char) :
    (if value.ordinal.val < 55296 then value.ordinal.val else value.ordinal.val + 2048) =
      value.toNat := by
  have inverse := congrArg Char.toNat (Char.ofOrdinal_ordinal (c := value))
  split_ifs with low
  · simpa only [Char.ofOrdinal, dif_pos low, Char.toNat, UInt32.toNat_ofNatLT] using inverse
  · simpa only [Char.ofOrdinal, dif_neg low, Char.toNat, UInt32.toNat_ofNatLT,
      Char.numSurrogates] using inverse

end RustWasm
