import SpecTecSupport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$sum_nat» (arg0 : (_root_.List _root_.Nat)) : _root_.Nat := arg0.foldl (· + ·) 0


def «$sum_int» (arg0 : (_root_.List _root_.Int)) : _root_.Int := arg0.foldl (· + ·) 0


def «$max_int» (arg0 : (_root_.List _root_.Int)) : _root_.Int := match arg0 with | [] => 0 | x :: xs => xs.foldl max x


def «$min_int» (arg0 : (_root_.List _root_.Int)) : _root_.Int := match arg0 with | [] => 0 | x :: xs => xs.foldl min x


def «$text_to_int:parse» (arg0 : _root_.String) : (_root_.Option _root_.Int) := let digit? (base : Nat) (c : Char) : Option Nat := let code := c.toNat; let value? := if '0'.toNat ≤ code ∧ code ≤ '9'.toNat then some (code - '0'.toNat) else if 'a'.toNat ≤ code ∧ code ≤ 'f'.toNat then some (code - 'a'.toNat + 10) else if 'A'.toNat ≤ code ∧ code ≤ 'F'.toNat then some (code - 'A'.toNat + 10) else none; value?.bind (fun value => if value < base then some value else none); let rec digits (base accumulator : Nat) (chars : List Char) : Option Nat := match chars with | [] => some accumulator | '_' :: tail => digits base accumulator tail | c :: tail => match digit? base c with | none => none | some digit => digits base (accumulator * base + digit) tail; let (negative, chars) := match arg0.toList with | '-' :: '+' :: tail => (true, tail) | '-' :: tail => (true, tail) | '+' :: tail => (false, tail) | chars => (false, chars); let (base, chars) := match chars with | '0' :: 'x' :: tail | '0' :: 'X' :: tail => (16, tail) | '0' :: 'o' :: tail | '0' :: 'O' :: tail => (8, tail) | '0' :: 'b' :: tail | '0' :: 'B' :: tail => (2, tail) | chars => (10, chars); match chars with | '_' :: _ => none | _ => (digits base 0 chars).map (fun value => if negative then -(Int.ofNat value) else Int.ofNat value)


def «$int_to_text» (arg0 : _root_.Int) : _root_.String := (if arg0 ≥ 0 then "+" else "-") ++ toString arg0.natAbs


def «$strip_all_whitespace» (arg0 : _root_.String) : _root_.String := String.ofList (arg0.toList.filter (· != ' '))


def «$rev_» {X : Type} (arg0 : (_root_.List X)) : (_root_.List X) := arg0.reverse


def «$concat_» {X : Type} (arg0 : (_root_.List (_root_.List X))) : (_root_.List X) := arg0.flatten


def «$sort_» {X : Type} (arg0 : (_root_.List (_root_.Nat × X))) : (_root_.List (_root_.Nat × X)) := arg0.mergeSort (fun left right => left.1 ≤ right.1)


inductive set (K : Type) : Type where
  | «`{ % `}» : (_root_.List K) → (set K)
deriving _root_.DecidableEq


def «$intersect_set» (arg0 : (set _root_.String)) (arg1 : (set _root_.String)) : (set _root_.String) := match arg0, arg1 with | .«`{ % `}» left, .«`{ % `}» right => .«`{ % `}» (_root_.specTecTextSetIntersect left right)


def «$union_set» (arg0 : (set _root_.String)) (arg1 : (set _root_.String)) : (set _root_.String) := match arg0, arg1 with | .«`{ % `}» left, .«`{ % `}» right => .«`{ % `}» (_root_.specTecTextSetUnion left right)


def «$unions_set» (arg0 : (_root_.List (set _root_.String))) : (set _root_.String) := .«`{ % `}» (arg0.foldr (fun current result => match current with | .«`{ % `}» elements => _root_.specTecTextSetUnion elements result) [])


def «$diff_set» (arg0 : (set _root_.String)) (arg1 : (set _root_.String)) : (set _root_.String) := match arg0, arg1 with | .«`{ % `}» left, .«`{ % `}» right => .«`{ % `}» (_root_.specTecTextSetDiff left right)


inductive pair (K V : Type) : Type where
  | «% ':' %» : K → V → (pair K V)
deriving _root_.DecidableEq


abbrev map (K V : Type) : Type := (set (pair K V))


inductive trailingCommaOpt : Type where
  | _EMPTY : trailingCommaOpt
  | «','» : trailingCommaOpt
deriving _root_.DecidableEq


mutual

def print_trailingCommaOpt (value : trailingCommaOpt) : _root_.Option _root_.String :=
  match value with
  | ._EMPTY => do
      return _root_.specTecPrintFinish (_root_.Option.none)
  | .«','» => do
      return _root_.specTecPrintFinish (_root_.Option.some ",")

end

instance : _root_.SpecTecPrint trailingCommaOpt := ⟨print_trailingCommaOpt⟩


inductive booleanLiteral : Type where
  | TRUE : booleanLiteral
  | FALSE : booleanLiteral
deriving _root_.DecidableEq


inductive integerLiteral : Type where
  | D : _root_.Int → integerLiteral
  | «% W %» : _root_.Nat → _root_.Int → integerLiteral
  | «% S %» : _root_.Nat → _root_.Int → integerLiteral
deriving _root_.DecidableEq


inductive stringLiteral : Type where
  | «'"' % '"'» : _root_.String → stringLiteral
deriving _root_.DecidableEq


inductive identifier : Type where
  | _ID : _root_.String → identifier
deriving _root_.DecidableEq


inductive typeIdentifier : Type where
  | _TID : _root_.String → typeIdentifier
deriving _root_.DecidableEq


mutual

def print_typeIdentifier (value : typeIdentifier) : _root_.Option _root_.String :=
  match value with
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])

end

instance : _root_.SpecTecPrint typeIdentifier := ⟨print_typeIdentifier⟩


inductive nonTypeName : Type where
  | _ID : _root_.String → nonTypeName
  | APPLY : nonTypeName
  | KEY : nonTypeName
  | ACTIONS : nonTypeName
  | STATE : nonTypeName
  | ENTRIES : nonTypeName
  | TYPE : nonTypeName
  | PRIORITY : nonTypeName
deriving _root_.DecidableEq


mutual

def print_nonTypeName (value : nonTypeName) : _root_.Option _root_.String :=
  match value with
  | ._ID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .APPLY => do
      return _root_.specTecPrintFinish (_root_.Option.some "apply")
  | .KEY => do
      return _root_.specTecPrintFinish (_root_.Option.some "key")
  | .ACTIONS => do
      return _root_.specTecPrintFinish (_root_.Option.some "actions")
  | .STATE => do
      return _root_.specTecPrintFinish (_root_.Option.some "state")
  | .ENTRIES => do
      return _root_.specTecPrintFinish (_root_.Option.some "entries")
  | .TYPE => do
      return _root_.specTecPrintFinish (_root_.Option.some "type")
  | .PRIORITY => do
      return _root_.specTecPrintFinish (_root_.Option.some "priority")

end

instance : _root_.SpecTecPrint nonTypeName := ⟨print_nonTypeName⟩


inductive prefixedNonTypeName : Type where
  | _ID : _root_.String → prefixedNonTypeName
  | APPLY : prefixedNonTypeName
  | KEY : prefixedNonTypeName
  | ACTIONS : prefixedNonTypeName
  | STATE : prefixedNonTypeName
  | ENTRIES : prefixedNonTypeName
  | TYPE : prefixedNonTypeName
  | PRIORITY : prefixedNonTypeName
  | «_ID '.' %» : nonTypeName → prefixedNonTypeName
deriving _root_.DecidableEq


abbrev typeName : Type := typeIdentifier


inductive prefixedTypeName : Type where
  | _TID : _root_.String → prefixedTypeName
  | «_TID '.' %» : typeName → prefixedTypeName
deriving _root_.DecidableEq


mutual

def print_prefixedTypeName (value : prefixedTypeName) : _root_.Option _root_.String :=
  match value with
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .«_TID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])

end

instance : _root_.SpecTecPrint prefixedTypeName := ⟨print_prefixedTypeName⟩


inductive tableCustomName : Type where
  | _ID : _root_.String → tableCustomName
  | _TID : _root_.String → tableCustomName
  | APPLY : tableCustomName
  | STATE : tableCustomName
  | TYPE : tableCustomName
  | PRIORITY : tableCustomName
deriving _root_.DecidableEq

end SpecTec
