/- Shared printing and text-set support from the donor Lean backend. -/
set_option autoImplicit false

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
