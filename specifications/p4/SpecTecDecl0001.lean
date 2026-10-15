import SpecTecDecl0000

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

mutual

def print_tableCustomName (value : tableCustomName) : _root_.Option _root_.String :=
  match value with
  | ._ID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .APPLY => do
      return _root_.specTecPrintFinish (_root_.Option.some "apply")
  | .STATE => do
      return _root_.specTecPrintFinish (_root_.Option.some "state")
  | .TYPE => do
      return _root_.specTecPrintFinish (_root_.Option.some "type")
  | .PRIORITY => do
      return _root_.specTecPrintFinish (_root_.Option.some "priority")

end

instance : _root_.SpecTecPrint tableCustomName := ⟨print_tableCustomName⟩


inductive name : Type where
  | _ID : _root_.String → name
  | APPLY : name
  | KEY : name
  | ACTIONS : name
  | STATE : name
  | ENTRIES : name
  | TYPE : name
  | PRIORITY : name
  | _TID : _root_.String → name
  | LIST : name
deriving _root_.DecidableEq


mutual

def print_name (value : name) : _root_.Option _root_.String :=
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
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .LIST => do
      return _root_.specTecPrintFinish (_root_.Option.some "list")

end

instance : _root_.SpecTecPrint name := ⟨print_name⟩


inductive nameList : Type where
  | _ID : _root_.String → nameList
  | APPLY : nameList
  | KEY : nameList
  | ACTIONS : nameList
  | STATE : nameList
  | ENTRIES : nameList
  | TYPE : nameList
  | PRIORITY : nameList
  | _TID : _root_.String → nameList
  | LIST : nameList
  | «% ',' %» : nameList → name → nameList
deriving _root_.DecidableEq


def «$flatten_nameList:case_1:downcast:0» (arg0 : nameList) : (_root_.Option name) := match arg0 with | ._ID field0 => some (name._ID field0) | .APPLY => some (name.APPLY) | .KEY => some (name.KEY) | .ACTIONS => some (name.ACTIONS) | .STATE => some (name.STATE) | .ENTRIES => some (name.ENTRIES) | .TYPE => some (name.TYPE) | .PRIORITY => some (name.PRIORITY) | ._TID field0 => some (name._TID field0) | .LIST => some (name.LIST) | _ => none


abbrev member : Type := name


inductive direction : Type where
  | _EMPTY : direction
  | IN : direction
  | OUT : direction
  | INOUT : direction
deriving _root_.DecidableEq


abbrev typeParameter : Type := name


inductive typeParameterList : Type where
  | _ID : _root_.String → typeParameterList
  | APPLY : typeParameterList
  | KEY : typeParameterList
  | ACTIONS : typeParameterList
  | STATE : typeParameterList
  | ENTRIES : typeParameterList
  | TYPE : typeParameterList
  | PRIORITY : typeParameterList
  | _TID : _root_.String → typeParameterList
  | LIST : typeParameterList
  | «% ',' %» : typeParameterList → typeParameter → typeParameterList
deriving _root_.DecidableEq


def «$flatten_typeParameterList:case_1:downcast:0» (arg0 : typeParameterList) : (_root_.Option name) := match arg0 with | ._ID field0 => some (name._ID field0) | .APPLY => some (name.APPLY) | .KEY => some (name.KEY) | .ACTIONS => some (name.ACTIONS) | .STATE => some (name.STATE) | .ENTRIES => some (name.ENTRIES) | .TYPE => some (name.TYPE) | .PRIORITY => some (name.PRIORITY) | ._TID field0 => some (name._TID field0) | .LIST => some (name.LIST) | _ => none


inductive typeParameterListOpt : Type where
  | _EMPTY : typeParameterListOpt
  | «`< % `>» : typeParameterList → typeParameterListOpt
deriving _root_.DecidableEq


inductive literalExpression : Type where
  | TRUE : literalExpression
  | FALSE : literalExpression
  | D : _root_.Int → literalExpression
  | «% W %» : _root_.Nat → _root_.Int → literalExpression
  | «% S %» : _root_.Nat → _root_.Int → literalExpression
  | «'"' % '"'» : _root_.String → literalExpression
deriving _root_.DecidableEq


inductive referenceExpression : Type where
  | _ID : _root_.String → referenceExpression
  | APPLY : referenceExpression
  | KEY : referenceExpression
  | ACTIONS : referenceExpression
  | STATE : referenceExpression
  | ENTRIES : referenceExpression
  | TYPE : referenceExpression
  | PRIORITY : referenceExpression
  | «_ID '.' %» : nonTypeName → referenceExpression
  | THIS : referenceExpression
deriving _root_.DecidableEq


inductive defaultExpression : Type where
  | «'...'» : defaultExpression
deriving _root_.DecidableEq


inductive unop : Type where
  | «'!'» : unop
  | «'~'» : unop
  | «'-'» : unop
  | «'+'» : unop
deriving _root_.DecidableEq


mutual

def print_unop (value : unop) : _root_.Option _root_.String :=
  match value with
  | .«'!'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "!")
  | .«'~'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "~")
  | .«'-'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "-")
  | .«'+'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "+")

end

instance : _root_.SpecTecPrint unop := ⟨print_unop⟩


inductive binop : Type where
  | «'*'» : binop
  | «'/'» : binop
  | «'%'» : binop
  | «'+'» : binop
  | «'-'» : binop
  | «'|+|'» : binop
  | «'|-|'» : binop
  | «'<<'» : binop
  | «'>>'» : binop
  | «'<='» : binop
  | «'>='» : binop
  | «'<'» : binop
  | «'>'» : binop
  | «'!='» : binop
  | «'=='» : binop
  | «'&'» : binop
  | «'^'» : binop
  | «'|'» : binop
  | «'++'» : binop
  | «'&&'» : binop
  | «'||'» : binop
deriving _root_.DecidableEq


mutual

def print_binop (value : binop) : _root_.Option _root_.String :=
  match value with
  | .«'*'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "*")
  | .«'/'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "/")
  | .«'%'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "%")
  | .«'+'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "+")
  | .«'-'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "-")
  | .«'|+|'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "|+|")
  | .«'|-|'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "|-|")
  | .«'<<'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "<<")
  | .«'>>'» => do
      return _root_.specTecPrintFinish (_root_.Option.some ">>")
  | .«'<='» => do
      return _root_.specTecPrintFinish (_root_.Option.some "<=")
  | .«'>='» => do
      return _root_.specTecPrintFinish (_root_.Option.some ">=")
  | .«'<'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "<")
  | .«'>'» => do
      return _root_.specTecPrintFinish (_root_.Option.some ">")
  | .«'!='» => do
      return _root_.specTecPrintFinish (_root_.Option.some "!=")
  | .«'=='» => do
      return _root_.specTecPrintFinish (_root_.Option.some "==")
  | .«'&'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "&")
  | .«'^'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "^")
  | .«'|'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "|")
  | .«'++'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "++")
  | .«'&&'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "&&")
  | .«'||'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "||")

end

instance : _root_.SpecTecPrint binop := ⟨print_binop⟩


inductive invalidHeaderExpression : Type where
  | «'{#}'» : invalidHeaderExpression
deriving _root_.DecidableEq


inductive errorAccessExpression : Type where
  | «ERROR '.' %» : member → errorAccessExpression
deriving _root_.DecidableEq


inductive sliceop : Type where
  | «':'» : sliceop
  | «'+:'» : sliceop
deriving _root_.DecidableEq


mutual

def print_sliceop (value : sliceop) : _root_.Option _root_.String :=
  match value with
  | .«':'» => do
      return _root_.specTecPrintFinish (_root_.Option.some ":")
  | .«'+:'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "+:")

end

instance : _root_.SpecTecPrint sliceop := ⟨print_sliceop⟩


mutual

inductive type : Type where
  | BOOL : type
  | ERROR : type
  | MATCH_KIND : type
  | STRING : type
  | INT : type
  | «INT `< % `>» : _root_.Int → type
  | «INT `< `( % `) `>» : expression → type
  | BIT : type
  | «BIT `< % `>» : _root_.Int → type
  | «BIT `< `( % `) `>» : expression → type
  | «VARBIT `< % `>» : _root_.Int → type
  | «VARBIT `< `( % `) `>» : expression → type
  | _TID : _root_.String → type
  | «_TID '.' %» : typeName → type
  | «% `< % `>» : prefixedTypeName → typeArgumentList → type
  | «% `[ % `]» : type → expression → type
  | «LIST `< % `>» : typeArgument → type
  | «TUPLE `< % `>» : typeArgumentList → type
deriving _root_.DecidableEq

inductive namedExpression : Type where
  | «% '=' %» : name → expression → namedExpression
deriving _root_.DecidableEq

inductive namedExpressionList : Type where
  | «% '=' %» : name → expression → namedExpressionList
  | «% ',' %» : namedExpressionList → namedExpression → namedExpressionList
deriving _root_.DecidableEq

inductive expression : Type where
  | TRUE : expression
  | FALSE : expression
  | D : _root_.Int → expression
  | «% W %» : _root_.Nat → _root_.Int → expression
  | «% S %» : _root_.Nat → _root_.Int → expression
  | «'"' % '"'» : _root_.String → expression
  | _ID : _root_.String → expression
  | APPLY : expression
  | KEY : expression
  | ACTIONS : expression
  | STATE : expression
  | ENTRIES : expression
  | TYPE : expression
  | PRIORITY : expression
  | «_ID '.' %» : nonTypeName → expression
  | THIS : expression
  | «'...'» : expression
  | «% %» : unop → expression → expression
  | «% % %» : expression → binop → expression → expression
  | «% '?' % ':' %» : expression → expression → expression → expression
  | «`( % `) %» : type → expression → expression
  | «'{#}'» : expression
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → expression
  | «ERROR '.' %» : member → expression
  | «% '.' %» : memberAccessBase → member → expression
  | «% `[ % `]» : expression → expression → expression
  | «% `[ % % % `]» : expression → expression → sliceop → expression → expression
  | «% `( % `)» : callTarget → argumentList → expression
  | «% `< % `> `( % `)» : expression → realTypeArgumentList → argumentList → expression
  | «`( % `)» : expression → expression
deriving _root_.DecidableEq

inductive expressionList : Type where
  | _EMPTY : expressionList
  | TRUE : expressionList
  | FALSE : expressionList
  | D : _root_.Int → expressionList
  | «% W %» : _root_.Nat → _root_.Int → expressionList
  | «% S %» : _root_.Nat → _root_.Int → expressionList
  | «'"' % '"'» : _root_.String → expressionList
  | _ID : _root_.String → expressionList
  | APPLY : expressionList
  | KEY : expressionList
  | ACTIONS : expressionList
  | STATE : expressionList
  | ENTRIES : expressionList
  | TYPE : expressionList
  | PRIORITY : expressionList
  | «_ID '.' %» : nonTypeName → expressionList
  | THIS : expressionList
  | «'...'» : expressionList
  | «% %» : unop → expression → expressionList
  | «% % %» : expression → binop → expression → expressionList
  | «% '?' % ':' %» : expression → expression → expression → expressionList
  | «`( % `) %» : type → expression → expressionList
  | «'{#}'» : expressionList
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → expressionList
  | «ERROR '.' %» : member → expressionList
  | «% '.' %» : memberAccessBase → member → expressionList
  | «% `[ % `]» : expression → expression → expressionList
  | «% `[ % % % `]» : expression → expression → sliceop → expression → expressionList
  | «% `( % `)» : callTarget → argumentList → expressionList
  | «% `< % `> `( % `)» : expression → realTypeArgumentList → argumentList → expressionList
  | «`( % `)» : expression → expressionList
  | «% ',' %» : expressionList → expression → expressionList
deriving _root_.DecidableEq

inductive memberAccessBase : Type where
  | _TID : _root_.String → memberAccessBase
  | «_TID '.' %» : typeName → memberAccessBase
  | TRUE : memberAccessBase
  | FALSE : memberAccessBase
  | D : _root_.Int → memberAccessBase
  | «% W %» : _root_.Nat → _root_.Int → memberAccessBase
  | «% S %» : _root_.Nat → _root_.Int → memberAccessBase
  | «'"' % '"'» : _root_.String → memberAccessBase
  | _ID : _root_.String → memberAccessBase
  | APPLY : memberAccessBase
  | KEY : memberAccessBase
  | ACTIONS : memberAccessBase
  | STATE : memberAccessBase
  | ENTRIES : memberAccessBase
  | TYPE : memberAccessBase
  | PRIORITY : memberAccessBase
  | «_ID '.' %» : nonTypeName → memberAccessBase
  | THIS : memberAccessBase
  | «'...'» : memberAccessBase
  | «% %» : unop → expression → memberAccessBase
  | «% % %» : expression → binop → expression → memberAccessBase
  | «% '?' % ':' %» : expression → expression → expression → memberAccessBase
  | «`( % `) %» : type → expression → memberAccessBase
  | «'{#}'» : memberAccessBase
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → memberAccessBase
  | «ERROR '.' %» : member → memberAccessBase
  | «% '.' %» : memberAccessBase → member → memberAccessBase
  | «% `[ % `]» : expression → expression → memberAccessBase
  | «% `[ % % % `]» : expression → expression → sliceop → expression → memberAccessBase
  | «% `( % `)» : callTarget → argumentList → memberAccessBase
  | «% `< % `> `( % `)» : expression → realTypeArgumentList → argumentList → memberAccessBase
  | «`( % `)» : expression → memberAccessBase
deriving _root_.DecidableEq

inductive sequenceOrRecordElementExpression : Type where
  | _EMPTY : sequenceOrRecordElementExpression
  | TRUE : sequenceOrRecordElementExpression
  | FALSE : sequenceOrRecordElementExpression
  | D : _root_.Int → sequenceOrRecordElementExpression
  | «% W %» : _root_.Nat → _root_.Int → sequenceOrRecordElementExpression
  | «% S %» : _root_.Nat → _root_.Int → sequenceOrRecordElementExpression
  | «'"' % '"'» : _root_.String → sequenceOrRecordElementExpression
  | _ID : _root_.String → sequenceOrRecordElementExpression
  | APPLY : sequenceOrRecordElementExpression
  | KEY : sequenceOrRecordElementExpression
  | ACTIONS : sequenceOrRecordElementExpression
  | STATE : sequenceOrRecordElementExpression
  | ENTRIES : sequenceOrRecordElementExpression
  | TYPE : sequenceOrRecordElementExpression
  | PRIORITY : sequenceOrRecordElementExpression
  | «_ID '.' %» : nonTypeName → sequenceOrRecordElementExpression
  | THIS : sequenceOrRecordElementExpression
  | «'...'» : sequenceOrRecordElementExpression
  | «% %» : unop → expression → sequenceOrRecordElementExpression
  | «% % %» : expression → binop → expression → sequenceOrRecordElementExpression
  | «% '?' % ':' %» : expression → expression → expression → sequenceOrRecordElementExpression
  | «`( % `) %» : type → expression → sequenceOrRecordElementExpression
  | «'{#}'» : sequenceOrRecordElementExpression
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → sequenceOrRecordElementExpression
  | «ERROR '.' %» : member → sequenceOrRecordElementExpression
  | «% '.' %» : memberAccessBase → member → sequenceOrRecordElementExpression
  | «% `[ % `]» : expression → expression → sequenceOrRecordElementExpression
  | «% `[ % % % `]» : expression → expression → sliceop → expression → sequenceOrRecordElementExpression
  | «% `( % `)» : callTarget → argumentList → sequenceOrRecordElementExpression
  | «% `< % `> `( % `)» : expression → realTypeArgumentList → argumentList → sequenceOrRecordElementExpression
  | «`( % `)» : expression → sequenceOrRecordElementExpression
  | «% ',' %» : expressionList → expression → sequenceOrRecordElementExpression
  | «% '=' %» : name → expression → sequenceOrRecordElementExpression
  | «% '=' % ',' '...'» : name → expression → sequenceOrRecordElementExpression
  | «% '=' % ',' %» : name → expression → namedExpressionList → sequenceOrRecordElementExpression
  | «% '=' % ',' % ',' '...'» : name → expression → namedExpressionList → sequenceOrRecordElementExpression
deriving _root_.DecidableEq

inductive callTarget : Type where
  | TRUE : callTarget
  | FALSE : callTarget
  | D : _root_.Int → callTarget
  | «% W %» : _root_.Nat → _root_.Int → callTarget
  | «% S %» : _root_.Nat → _root_.Int → callTarget
  | «'"' % '"'» : _root_.String → callTarget
  | _ID : _root_.String → callTarget
  | APPLY : callTarget
  | KEY : callTarget
  | ACTIONS : callTarget
  | STATE : callTarget
  | ENTRIES : callTarget
  | TYPE : callTarget
  | PRIORITY : callTarget
  | «_ID '.' %» : nonTypeName → callTarget
  | THIS : callTarget
  | «'...'» : callTarget
  | «% %» : unop → expression → callTarget
  | «% % %» : expression → binop → expression → callTarget
  | «% '?' % ':' %» : expression → expression → expression → callTarget
  | «`( % `) %» : type → expression → callTarget
  | «'{#}'» : callTarget
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → callTarget
  | «ERROR '.' %» : member → callTarget
  | «% '.' %» : memberAccessBase → member → callTarget
  | «% `[ % `]» : expression → expression → callTarget
  | «% `[ % % % `]» : expression → expression → sliceop → expression → callTarget
  | «% `( % `)» : callTarget → argumentList → callTarget
  | «% `< % `> `( % `)» : expression → realTypeArgumentList → argumentList → callTarget
  | «`( % `)» : expression → callTarget
  | _TID : _root_.String → callTarget
  | «_TID '.' %» : typeName → callTarget
  | «% `< % `>» : prefixedTypeName → typeArgumentList → callTarget
deriving _root_.DecidableEq

inductive realTypeArgument : Type where
  | BOOL : realTypeArgument
  | ERROR : realTypeArgument
  | MATCH_KIND : realTypeArgument
  | STRING : realTypeArgument
  | INT : realTypeArgument
  | «INT `< % `>» : _root_.Int → realTypeArgument
  | «INT `< `( % `) `>» : expression → realTypeArgument
  | BIT : realTypeArgument
  | «BIT `< % `>» : _root_.Int → realTypeArgument
  | «BIT `< `( % `) `>» : expression → realTypeArgument
  | «VARBIT `< % `>» : _root_.Int → realTypeArgument
  | «VARBIT `< `( % `) `>» : expression → realTypeArgument
  | _TID : _root_.String → realTypeArgument
  | «_TID '.' %» : typeName → realTypeArgument
  | «% `< % `>» : prefixedTypeName → typeArgumentList → realTypeArgument
  | «% `[ % `]» : type → expression → realTypeArgument
  | «LIST `< % `>» : typeArgument → realTypeArgument
  | «TUPLE `< % `>» : typeArgumentList → realTypeArgument
  | VOID : realTypeArgument
  | «'_'» : realTypeArgument
deriving _root_.DecidableEq

inductive realTypeArgumentList : Type where
  | BOOL : realTypeArgumentList
  | ERROR : realTypeArgumentList
  | MATCH_KIND : realTypeArgumentList
  | STRING : realTypeArgumentList
  | INT : realTypeArgumentList
  | «INT `< % `>» : _root_.Int → realTypeArgumentList
  | «INT `< `( % `) `>» : expression → realTypeArgumentList
  | BIT : realTypeArgumentList
  | «BIT `< % `>» : _root_.Int → realTypeArgumentList
  | «BIT `< `( % `) `>» : expression → realTypeArgumentList
  | «VARBIT `< % `>» : _root_.Int → realTypeArgumentList
  | «VARBIT `< `( % `) `>» : expression → realTypeArgumentList
  | _TID : _root_.String → realTypeArgumentList
  | «_TID '.' %» : typeName → realTypeArgumentList
  | «% `< % `>» : prefixedTypeName → typeArgumentList → realTypeArgumentList
  | «% `[ % `]» : type → expression → realTypeArgumentList
  | «LIST `< % `>» : typeArgument → realTypeArgumentList
  | «TUPLE `< % `>» : typeArgumentList → realTypeArgumentList
  | VOID : realTypeArgumentList
  | «'_'» : realTypeArgumentList
  | «% ',' %» : realTypeArgumentList → realTypeArgument → realTypeArgumentList
deriving _root_.DecidableEq

inductive typeArgument : Type where
  | BOOL : typeArgument
  | ERROR : typeArgument
  | MATCH_KIND : typeArgument
  | STRING : typeArgument
  | INT : typeArgument
  | «INT `< % `>» : _root_.Int → typeArgument
  | «INT `< `( % `) `>» : expression → typeArgument
  | BIT : typeArgument
  | «BIT `< % `>» : _root_.Int → typeArgument
  | «BIT `< `( % `) `>» : expression → typeArgument
  | «VARBIT `< % `>» : _root_.Int → typeArgument
  | «VARBIT `< `( % `) `>» : expression → typeArgument
  | _TID : _root_.String → typeArgument
  | «_TID '.' %» : typeName → typeArgument
  | «% `< % `>» : prefixedTypeName → typeArgumentList → typeArgument
  | «% `[ % `]» : type → expression → typeArgument
  | «LIST `< % `>» : typeArgument → typeArgument
  | «TUPLE `< % `>» : typeArgumentList → typeArgument
  | VOID : typeArgument
  | «'_'» : typeArgument
  | _ID : _root_.String → typeArgument
  | APPLY : typeArgument
  | KEY : typeArgument
  | ACTIONS : typeArgument
  | STATE : typeArgument
  | ENTRIES : typeArgument
  | TYPE : typeArgument
  | PRIORITY : typeArgument
deriving _root_.DecidableEq

inductive typeArgumentList : Type where
  | _EMPTY : typeArgumentList
  | BOOL : typeArgumentList
  | ERROR : typeArgumentList
  | MATCH_KIND : typeArgumentList
  | STRING : typeArgumentList
  | INT : typeArgumentList
  | «INT `< % `>» : _root_.Int → typeArgumentList
  | «INT `< `( % `) `>» : expression → typeArgumentList
  | BIT : typeArgumentList
  | «BIT `< % `>» : _root_.Int → typeArgumentList
  | «BIT `< `( % `) `>» : expression → typeArgumentList
  | «VARBIT `< % `>» : _root_.Int → typeArgumentList
  | «VARBIT `< `( % `) `>» : expression → typeArgumentList
  | _TID : _root_.String → typeArgumentList
  | «_TID '.' %» : typeName → typeArgumentList
  | «% `< % `>» : prefixedTypeName → typeArgumentList → typeArgumentList
  | «% `[ % `]» : type → expression → typeArgumentList
  | «LIST `< % `>» : typeArgument → typeArgumentList
  | «TUPLE `< % `>» : typeArgumentList → typeArgumentList
  | VOID : typeArgumentList
  | «'_'» : typeArgumentList
  | _ID : _root_.String → typeArgumentList
  | APPLY : typeArgumentList
  | KEY : typeArgumentList
  | ACTIONS : typeArgumentList
  | STATE : typeArgumentList
  | ENTRIES : typeArgumentList
  | TYPE : typeArgumentList
  | PRIORITY : typeArgumentList
  | «% ',' %» : typeArgumentList → typeArgument → typeArgumentList
deriving _root_.DecidableEq

inductive argument : Type where
  | TRUE : argument
  | FALSE : argument
  | D : _root_.Int → argument
  | «% W %» : _root_.Nat → _root_.Int → argument
  | «% S %» : _root_.Nat → _root_.Int → argument
  | «'"' % '"'» : _root_.String → argument
  | _ID : _root_.String → argument
  | APPLY : argument
  | KEY : argument
  | ACTIONS : argument
  | STATE : argument
  | ENTRIES : argument
  | TYPE : argument
  | PRIORITY : argument
  | «_ID '.' %» : nonTypeName → argument
  | THIS : argument
  | «'...'» : argument
  | «% %» : unop → expression → argument
  | «% % %» : expression → binop → expression → argument
  | «% '?' % ':' %» : expression → expression → expression → argument
  | «`( % `) %» : type → expression → argument
  | «'{#}'» : argument
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → argument
  | «ERROR '.' %» : member → argument
  | «% '.' %» : memberAccessBase → member → argument
  | «% `[ % `]» : expression → expression → argument
  | «% `[ % % % `]» : expression → expression → sliceop → expression → argument
  | «% `( % `)» : callTarget → argumentList → argument
  | «% `< % `> `( % `)» : expression → realTypeArgumentList → argumentList → argument
  | «`( % `)» : expression → argument
  | «% '=' %» : name → expression → argument
  | «% '=' '_'» : name → argument
  | «'_'» : argument
deriving _root_.DecidableEq

inductive argumentListNonEmpty : Type where
  | TRUE : argumentListNonEmpty
  | FALSE : argumentListNonEmpty
  | D : _root_.Int → argumentListNonEmpty
  | «% W %» : _root_.Nat → _root_.Int → argumentListNonEmpty
  | «% S %» : _root_.Nat → _root_.Int → argumentListNonEmpty
  | «'"' % '"'» : _root_.String → argumentListNonEmpty
  | _ID : _root_.String → argumentListNonEmpty
  | APPLY : argumentListNonEmpty
  | KEY : argumentListNonEmpty
  | ACTIONS : argumentListNonEmpty
  | STATE : argumentListNonEmpty
  | ENTRIES : argumentListNonEmpty
  | TYPE : argumentListNonEmpty
  | PRIORITY : argumentListNonEmpty
  | «_ID '.' %» : nonTypeName → argumentListNonEmpty
  | THIS : argumentListNonEmpty
  | «'...'» : argumentListNonEmpty
  | «% %» : unop → expression → argumentListNonEmpty
  | «% % %» : expression → binop → expression → argumentListNonEmpty
  | «% '?' % ':' %» : expression → expression → expression → argumentListNonEmpty
  | «`( % `) %» : type → expression → argumentListNonEmpty
  | «'{#}'» : argumentListNonEmpty
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → argumentListNonEmpty
  | «ERROR '.' %» : member → argumentListNonEmpty
  | «% '.' %» : memberAccessBase → member → argumentListNonEmpty
  | «% `[ % `]» : expression → expression → argumentListNonEmpty
  | «% `[ % % % `]» : expression → expression → sliceop → expression → argumentListNonEmpty
  | «% `( % `)» : callTarget → argumentList → argumentListNonEmpty
  | «% `< % `> `( % `)» : expression → realTypeArgumentList → argumentList → argumentListNonEmpty
  | «`( % `)» : expression → argumentListNonEmpty
  | «% '=' %» : name → expression → argumentListNonEmpty
  | «% '=' '_'» : name → argumentListNonEmpty
  | «'_'» : argumentListNonEmpty
  | «% ',' %» : argumentListNonEmpty → argument → argumentListNonEmpty
deriving _root_.DecidableEq

inductive argumentList : Type where
  | _EMPTY : argumentList
  | TRUE : argumentList
  | FALSE : argumentList
  | D : _root_.Int → argumentList
  | «% W %» : _root_.Nat → _root_.Int → argumentList
  | «% S %» : _root_.Nat → _root_.Int → argumentList
  | «'"' % '"'» : _root_.String → argumentList
  | _ID : _root_.String → argumentList
  | APPLY : argumentList
  | KEY : argumentList
  | ACTIONS : argumentList
  | STATE : argumentList
  | ENTRIES : argumentList
  | TYPE : argumentList
  | PRIORITY : argumentList
  | «_ID '.' %» : nonTypeName → argumentList
  | THIS : argumentList
  | «'...'» : argumentList
  | «% %» : unop → expression → argumentList
  | «% % %» : expression → binop → expression → argumentList
  | «% '?' % ':' %» : expression → expression → expression → argumentList
  | «`( % `) %» : type → expression → argumentList
  | «'{#}'» : argumentList
  | «`{ % % `}» : sequenceOrRecordElementExpression → trailingCommaOpt → argumentList
  | «ERROR '.' %» : member → argumentList
  | «% '.' %» : memberAccessBase → member → argumentList
  | «% `[ % `]» : expression → expression → argumentList
  | «% `[ % % % `]» : expression → expression → sliceop → expression → argumentList
  | «% `( % `)» : callTarget → argumentList → argumentList
  | «% `< % `> `( % `)» : expression → realTypeArgumentList → argumentList → argumentList
  | «`( % `)» : expression → argumentList
  | «% '=' %» : name → expression → argumentList
  | «% '=' '_'» : name → argumentList
  | «'_'» : argumentList
  | «% ',' %» : argumentListNonEmpty → argument → argumentList
deriving _root_.DecidableEq

end


mutual

def print_type (value : type) : _root_.Option _root_.String :=
  match value with
  | .BOOL => do
      return _root_.specTecPrintFinish (_root_.Option.some "bool")
  | .ERROR => do
      return _root_.specTecPrintFinish (_root_.Option.some "error")
  | .MATCH_KIND => do
      return _root_.specTecPrintFinish (_root_.Option.some "match_kind")
  | .STRING => do
      return _root_.specTecPrintFinish (_root_.Option.some "string")
  | .INT => do
      return _root_.specTecPrintFinish (_root_.Option.some "int")
  | .«INT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«INT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .BIT => do
      return _root_.specTecPrintFinish (_root_.Option.some "bit")
  | .«BIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«BIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .«VARBIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«VARBIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .«_TID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .«% `< % `>» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_typeArgumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"]])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«LIST `< % `>» x0 => do
      let s0 ← print_typeArgument x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "list", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«TUPLE `< % `>» x0 => do
      let s0 ← print_typeArgumentList x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "tuple", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
termination_by structural value

def print_expression (value : expression) : _root_.Option _root_.String :=
  match value with
  | .TRUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "true")
  | .FALSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "false")
  | .D x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.Option.some s0)
  | .«% W %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "w")) (_root_.Option.some s1))
  | .«% S %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "s")) (_root_.Option.some s1))
  | .«'"' % '"'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some "\"") (_root_.Option.some s0)) (_root_.Option.some "\""))
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
  | .«_ID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .THIS => do
      return _root_.specTecPrintFinish (_root_.Option.some "this")
  | .«'...'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "...")
  | .«% %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1])
  | .«% % %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1, _root_.Option.some s2])
  | .«% '?' % ':' %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "?", _root_.Option.some s1, _root_.Option.some ":", _root_.Option.some s2])
  | .«`( % `) %» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some s1])
  | .«'{#}'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "{#}")
  | .«`{ % % `}» x0 x1 => do
      let s0 ← print_sequenceOrRecordElementExpression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "{", _root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1], _root_.Option.some "}"])
  | .«ERROR '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "error", _root_.Option.some ".", _root_.Option.some s0])
  | .«% '.' %» x0 x1 => do
      let s0 ← print_memberAccessBase x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ".", _root_.Option.some s1])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«% `[ % % % `]» x0 x1 x2 x3 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← _root_.SpecTecPrint.print? x2
      let s3 ← print_expression x3
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.specTecPrintFiltered [_root_.Option.some s1, _root_.Option.some s2, _root_.Option.some s3], _root_.Option.some "]"]])
  | .«% `( % `)» x0 x1 => do
      let s0 ← print_callTarget x0
      let s1 ← print_argumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s1, _root_.Option.some ")"]])
  | .«% `< % `> `( % `)» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_realTypeArgumentList x1
      let s2 ← print_argumentList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"], _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s2, _root_.Option.some ")"]])
  | .«`( % `)» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"])
termination_by structural value

def print_sequenceOrRecordElementExpression (value : sequenceOrRecordElementExpression) : _root_.Option _root_.String :=
  match value with
  | ._EMPTY => do
      return _root_.specTecPrintFinish (_root_.Option.none)
  | .TRUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "true")
  | .FALSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "false")
  | .D x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.Option.some s0)
  | .«% W %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "w")) (_root_.Option.some s1))
  | .«% S %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "s")) (_root_.Option.some s1))
  | .«'"' % '"'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some "\"") (_root_.Option.some s0)) (_root_.Option.some "\""))
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
  | .«_ID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .THIS => do
      return _root_.specTecPrintFinish (_root_.Option.some "this")
  | .«'...'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "...")
  | .«% %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1])
  | .«% % %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1, _root_.Option.some s2])
  | .«% '?' % ':' %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "?", _root_.Option.some s1, _root_.Option.some ":", _root_.Option.some s2])
  | .«`( % `) %» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some s1])
  | .«'{#}'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "{#}")
  | .«`{ % % `}» x0 x1 => do
      let s0 ← print_sequenceOrRecordElementExpression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "{", _root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1], _root_.Option.some "}"])
  | .«ERROR '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "error", _root_.Option.some ".", _root_.Option.some s0])
  | .«% '.' %» x0 x1 => do
      let s0 ← print_memberAccessBase x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ".", _root_.Option.some s1])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«% `[ % % % `]» x0 x1 x2 x3 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← _root_.SpecTecPrint.print? x2
      let s3 ← print_expression x3
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.specTecPrintFiltered [_root_.Option.some s1, _root_.Option.some s2, _root_.Option.some s3], _root_.Option.some "]"]])
  | .«% `( % `)» x0 x1 => do
      let s0 ← print_callTarget x0
      let s1 ← print_argumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s1, _root_.Option.some ")"]])
  | .«% `< % `> `( % `)» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_realTypeArgumentList x1
      let s2 ← print_argumentList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"], _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s2, _root_.Option.some ")"]])
  | .«`( % `)» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"])
  | .«% ',' %» x0 x1 => do
      let s0 ← print_expressionList x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ",", _root_.Option.some s1])
  | .«% '=' %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some s1])
  | .«% '=' % ',' '...'» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some s1, _root_.Option.some ",", _root_.Option.some "..."])
  | .«% '=' % ',' %» x0 x1 x2 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      let s2 ← print_namedExpressionList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some s1, _root_.Option.some ",", _root_.Option.some s2])
  | .«% '=' % ',' % ',' '...'» x0 x1 x2 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      let s2 ← print_namedExpressionList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some s1, _root_.Option.some ",", _root_.Option.some s2, _root_.Option.some ",", _root_.Option.some "..."])
termination_by structural value

def print_memberAccessBase (value : memberAccessBase) : _root_.Option _root_.String :=
  match value with
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .«_TID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .TRUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "true")
  | .FALSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "false")
  | .D x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.Option.some s0)
  | .«% W %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "w")) (_root_.Option.some s1))
  | .«% S %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "s")) (_root_.Option.some s1))
  | .«'"' % '"'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some "\"") (_root_.Option.some s0)) (_root_.Option.some "\""))
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
  | .«_ID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .THIS => do
      return _root_.specTecPrintFinish (_root_.Option.some "this")
  | .«'...'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "...")
  | .«% %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1])
  | .«% % %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1, _root_.Option.some s2])
  | .«% '?' % ':' %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "?", _root_.Option.some s1, _root_.Option.some ":", _root_.Option.some s2])
  | .«`( % `) %» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some s1])
  | .«'{#}'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "{#}")
  | .«`{ % % `}» x0 x1 => do
      let s0 ← print_sequenceOrRecordElementExpression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "{", _root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1], _root_.Option.some "}"])
  | .«ERROR '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "error", _root_.Option.some ".", _root_.Option.some s0])
  | .«% '.' %» x0 x1 => do
      let s0 ← print_memberAccessBase x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ".", _root_.Option.some s1])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«% `[ % % % `]» x0 x1 x2 x3 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← _root_.SpecTecPrint.print? x2
      let s3 ← print_expression x3
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.specTecPrintFiltered [_root_.Option.some s1, _root_.Option.some s2, _root_.Option.some s3], _root_.Option.some "]"]])
  | .«% `( % `)» x0 x1 => do
      let s0 ← print_callTarget x0
      let s1 ← print_argumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s1, _root_.Option.some ")"]])
  | .«% `< % `> `( % `)» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_realTypeArgumentList x1
      let s2 ← print_argumentList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"], _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s2, _root_.Option.some ")"]])
  | .«`( % `)» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"])
termination_by structural value

def print_callTarget (value : callTarget) : _root_.Option _root_.String :=
  match value with
  | .TRUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "true")
  | .FALSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "false")
  | .D x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.Option.some s0)
  | .«% W %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "w")) (_root_.Option.some s1))
  | .«% S %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "s")) (_root_.Option.some s1))
  | .«'"' % '"'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some "\"") (_root_.Option.some s0)) (_root_.Option.some "\""))
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
  | .«_ID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .THIS => do
      return _root_.specTecPrintFinish (_root_.Option.some "this")
  | .«'...'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "...")
  | .«% %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1])
  | .«% % %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1, _root_.Option.some s2])
  | .«% '?' % ':' %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "?", _root_.Option.some s1, _root_.Option.some ":", _root_.Option.some s2])
  | .«`( % `) %» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some s1])
  | .«'{#}'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "{#}")
  | .«`{ % % `}» x0 x1 => do
      let s0 ← print_sequenceOrRecordElementExpression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "{", _root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1], _root_.Option.some "}"])
  | .«ERROR '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "error", _root_.Option.some ".", _root_.Option.some s0])
  | .«% '.' %» x0 x1 => do
      let s0 ← print_memberAccessBase x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ".", _root_.Option.some s1])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«% `[ % % % `]» x0 x1 x2 x3 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← _root_.SpecTecPrint.print? x2
      let s3 ← print_expression x3
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.specTecPrintFiltered [_root_.Option.some s1, _root_.Option.some s2, _root_.Option.some s3], _root_.Option.some "]"]])
  | .«% `( % `)» x0 x1 => do
      let s0 ← print_callTarget x0
      let s1 ← print_argumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s1, _root_.Option.some ")"]])
  | .«% `< % `> `( % `)» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_realTypeArgumentList x1
      let s2 ← print_argumentList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"], _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s2, _root_.Option.some ")"]])
  | .«`( % `)» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"])
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .«_TID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .«% `< % `>» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_typeArgumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"]])
termination_by structural value

def print_argumentList (value : argumentList) : _root_.Option _root_.String :=
  match value with
  | ._EMPTY => do
      return _root_.specTecPrintFinish (_root_.Option.none)
  | .TRUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "true")
  | .FALSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "false")
  | .D x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.Option.some s0)
  | .«% W %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "w")) (_root_.Option.some s1))
  | .«% S %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "s")) (_root_.Option.some s1))
  | .«'"' % '"'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some "\"") (_root_.Option.some s0)) (_root_.Option.some "\""))
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
  | .«_ID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .THIS => do
      return _root_.specTecPrintFinish (_root_.Option.some "this")
  | .«'...'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "...")
  | .«% %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1])
  | .«% % %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1, _root_.Option.some s2])
  | .«% '?' % ':' %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "?", _root_.Option.some s1, _root_.Option.some ":", _root_.Option.some s2])
  | .«`( % `) %» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some s1])
  | .«'{#}'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "{#}")
  | .«`{ % % `}» x0 x1 => do
      let s0 ← print_sequenceOrRecordElementExpression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "{", _root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1], _root_.Option.some "}"])
  | .«ERROR '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "error", _root_.Option.some ".", _root_.Option.some s0])
  | .«% '.' %» x0 x1 => do
      let s0 ← print_memberAccessBase x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ".", _root_.Option.some s1])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«% `[ % % % `]» x0 x1 x2 x3 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← _root_.SpecTecPrint.print? x2
      let s3 ← print_expression x3
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.specTecPrintFiltered [_root_.Option.some s1, _root_.Option.some s2, _root_.Option.some s3], _root_.Option.some "]"]])
  | .«% `( % `)» x0 x1 => do
      let s0 ← print_callTarget x0
      let s1 ← print_argumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s1, _root_.Option.some ")"]])
  | .«% `< % `> `( % `)» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_realTypeArgumentList x1
      let s2 ← print_argumentList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"], _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s2, _root_.Option.some ")"]])
  | .«`( % `)» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"])
  | .«% '=' %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some s1])
  | .«% '=' '_'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some "_"])
  | .«'_'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "_")
  | .«% ',' %» x0 x1 => do
      let s0 ← print_argumentListNonEmpty x0
      let s1 ← print_argument x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ",", _root_.Option.some s1])
termination_by structural value

def print_realTypeArgumentList (value : realTypeArgumentList) : _root_.Option _root_.String :=
  match value with
  | .BOOL => do
      return _root_.specTecPrintFinish (_root_.Option.some "bool")
  | .ERROR => do
      return _root_.specTecPrintFinish (_root_.Option.some "error")
  | .MATCH_KIND => do
      return _root_.specTecPrintFinish (_root_.Option.some "match_kind")
  | .STRING => do
      return _root_.specTecPrintFinish (_root_.Option.some "string")
  | .INT => do
      return _root_.specTecPrintFinish (_root_.Option.some "int")
  | .«INT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«INT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .BIT => do
      return _root_.specTecPrintFinish (_root_.Option.some "bit")
  | .«BIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«BIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .«VARBIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«VARBIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .«_TID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .«% `< % `>» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_typeArgumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"]])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«LIST `< % `>» x0 => do
      let s0 ← print_typeArgument x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "list", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«TUPLE `< % `>» x0 => do
      let s0 ← print_typeArgumentList x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "tuple", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .VOID => do
      return _root_.specTecPrintFinish (_root_.Option.some "void")
  | .«'_'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "_")
  | .«% ',' %» x0 x1 => do
      let s0 ← print_realTypeArgumentList x0
      let s1 ← print_realTypeArgument x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ",", _root_.Option.some s1])
termination_by structural value

def print_typeArgumentList (value : typeArgumentList) : _root_.Option _root_.String :=
  match value with
  | ._EMPTY => do
      return _root_.specTecPrintFinish (_root_.Option.none)
  | .BOOL => do
      return _root_.specTecPrintFinish (_root_.Option.some "bool")
  | .ERROR => do
      return _root_.specTecPrintFinish (_root_.Option.some "error")
  | .MATCH_KIND => do
      return _root_.specTecPrintFinish (_root_.Option.some "match_kind")
  | .STRING => do
      return _root_.specTecPrintFinish (_root_.Option.some "string")
  | .INT => do
      return _root_.specTecPrintFinish (_root_.Option.some "int")
  | .«INT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«INT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .BIT => do
      return _root_.specTecPrintFinish (_root_.Option.some "bit")
  | .«BIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«BIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .«VARBIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«VARBIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .«_TID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .«% `< % `>» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_typeArgumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"]])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«LIST `< % `>» x0 => do
      let s0 ← print_typeArgument x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "list", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«TUPLE `< % `>» x0 => do
      let s0 ← print_typeArgumentList x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "tuple", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .VOID => do
      return _root_.specTecPrintFinish (_root_.Option.some "void")
  | .«'_'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "_")
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
  | .«% ',' %» x0 x1 => do
      let s0 ← print_typeArgumentList x0
      let s1 ← print_typeArgument x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ",", _root_.Option.some s1])
termination_by structural value

def print_typeArgument (value : typeArgument) : _root_.Option _root_.String :=
  match value with
  | .BOOL => do
      return _root_.specTecPrintFinish (_root_.Option.some "bool")
  | .ERROR => do
      return _root_.specTecPrintFinish (_root_.Option.some "error")
  | .MATCH_KIND => do
      return _root_.specTecPrintFinish (_root_.Option.some "match_kind")
  | .STRING => do
      return _root_.specTecPrintFinish (_root_.Option.some "string")
  | .INT => do
      return _root_.specTecPrintFinish (_root_.Option.some "int")
  | .«INT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«INT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .BIT => do
      return _root_.specTecPrintFinish (_root_.Option.some "bit")
  | .«BIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«BIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .«VARBIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«VARBIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .«_TID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .«% `< % `>» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_typeArgumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"]])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«LIST `< % `>» x0 => do
      let s0 ← print_typeArgument x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "list", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«TUPLE `< % `>» x0 => do
      let s0 ← print_typeArgumentList x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "tuple", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .VOID => do
      return _root_.specTecPrintFinish (_root_.Option.some "void")
  | .«'_'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "_")
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
termination_by structural value

def print_realTypeArgument (value : realTypeArgument) : _root_.Option _root_.String :=
  match value with
  | .BOOL => do
      return _root_.specTecPrintFinish (_root_.Option.some "bool")
  | .ERROR => do
      return _root_.specTecPrintFinish (_root_.Option.some "error")
  | .MATCH_KIND => do
      return _root_.specTecPrintFinish (_root_.Option.some "match_kind")
  | .STRING => do
      return _root_.specTecPrintFinish (_root_.Option.some "string")
  | .INT => do
      return _root_.specTecPrintFinish (_root_.Option.some "int")
  | .«INT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«INT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "int", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .BIT => do
      return _root_.specTecPrintFinish (_root_.Option.some "bit")
  | .«BIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«BIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "bit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | .«VARBIT `< % `>» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«VARBIT `< `( % `) `>» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "varbit", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some ">"]])
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .«_TID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .«% `< % `>» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_typeArgumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"]])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«LIST `< % `>» x0 => do
      let s0 ← print_typeArgument x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "list", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .«TUPLE `< % `>» x0 => do
      let s0 ← print_typeArgumentList x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "tuple", _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s0, _root_.Option.some ">"]])
  | .VOID => do
      return _root_.specTecPrintFinish (_root_.Option.some "void")
  | .«'_'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "_")
termination_by structural value

def print_argumentListNonEmpty (value : argumentListNonEmpty) : _root_.Option _root_.String :=
  match value with
  | .TRUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "true")
  | .FALSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "false")
  | .D x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.Option.some s0)
  | .«% W %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "w")) (_root_.Option.some s1))
  | .«% S %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "s")) (_root_.Option.some s1))
  | .«'"' % '"'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some "\"") (_root_.Option.some s0)) (_root_.Option.some "\""))
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
  | .«_ID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .THIS => do
      return _root_.specTecPrintFinish (_root_.Option.some "this")
  | .«'...'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "...")
  | .«% %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1])
  | .«% % %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1, _root_.Option.some s2])
  | .«% '?' % ':' %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "?", _root_.Option.some s1, _root_.Option.some ":", _root_.Option.some s2])
  | .«`( % `) %» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some s1])
  | .«'{#}'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "{#}")
  | .«`{ % % `}» x0 x1 => do
      let s0 ← print_sequenceOrRecordElementExpression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "{", _root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1], _root_.Option.some "}"])
  | .«ERROR '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "error", _root_.Option.some ".", _root_.Option.some s0])
  | .«% '.' %» x0 x1 => do
      let s0 ← print_memberAccessBase x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ".", _root_.Option.some s1])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«% `[ % % % `]» x0 x1 x2 x3 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← _root_.SpecTecPrint.print? x2
      let s3 ← print_expression x3
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.specTecPrintFiltered [_root_.Option.some s1, _root_.Option.some s2, _root_.Option.some s3], _root_.Option.some "]"]])
  | .«% `( % `)» x0 x1 => do
      let s0 ← print_callTarget x0
      let s1 ← print_argumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s1, _root_.Option.some ")"]])
  | .«% `< % `> `( % `)» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_realTypeArgumentList x1
      let s2 ← print_argumentList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"], _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s2, _root_.Option.some ")"]])
  | .«`( % `)» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"])
  | .«% '=' %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some s1])
  | .«% '=' '_'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some "_"])
  | .«'_'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "_")
  | .«% ',' %» x0 x1 => do
      let s0 ← print_argumentListNonEmpty x0
      let s1 ← print_argument x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ",", _root_.Option.some s1])
termination_by structural value

def print_argument (value : argument) : _root_.Option _root_.String :=
  match value with
  | .TRUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "true")
  | .FALSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "false")
  | .D x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.Option.some s0)
  | .«% W %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "w")) (_root_.Option.some s1))
  | .«% S %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "s")) (_root_.Option.some s1))
  | .«'"' % '"'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some "\"") (_root_.Option.some s0)) (_root_.Option.some "\""))
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
  | .«_ID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .THIS => do
      return _root_.specTecPrintFinish (_root_.Option.some "this")
  | .«'...'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "...")
  | .«% %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1])
  | .«% % %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1, _root_.Option.some s2])
  | .«% '?' % ':' %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "?", _root_.Option.some s1, _root_.Option.some ":", _root_.Option.some s2])
  | .«`( % `) %» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some s1])
  | .«'{#}'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "{#}")
  | .«`{ % % `}» x0 x1 => do
      let s0 ← print_sequenceOrRecordElementExpression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "{", _root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1], _root_.Option.some "}"])
  | .«ERROR '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "error", _root_.Option.some ".", _root_.Option.some s0])
  | .«% '.' %» x0 x1 => do
      let s0 ← print_memberAccessBase x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ".", _root_.Option.some s1])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«% `[ % % % `]» x0 x1 x2 x3 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← _root_.SpecTecPrint.print? x2
      let s3 ← print_expression x3
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.specTecPrintFiltered [_root_.Option.some s1, _root_.Option.some s2, _root_.Option.some s3], _root_.Option.some "]"]])
  | .«% `( % `)» x0 x1 => do
      let s0 ← print_callTarget x0
      let s1 ← print_argumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s1, _root_.Option.some ")"]])
  | .«% `< % `> `( % `)» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_realTypeArgumentList x1
      let s2 ← print_argumentList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"], _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s2, _root_.Option.some ")"]])
  | .«`( % `)» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"])
  | .«% '=' %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some s1])
  | .«% '=' '_'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some "_"])
  | .«'_'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "_")
termination_by structural value

def print_expressionList (value : expressionList) : _root_.Option _root_.String :=
  match value with
  | ._EMPTY => do
      return _root_.specTecPrintFinish (_root_.Option.none)
  | .TRUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "true")
  | .FALSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "false")
  | .D x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.Option.some s0)
  | .«% W %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "w")) (_root_.Option.some s1))
  | .«% S %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some s0) (_root_.Option.some "s")) (_root_.Option.some s1))
  | .«'"' % '"'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some "\"") (_root_.Option.some s0)) (_root_.Option.some "\""))
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
  | .«_ID '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some ".", _root_.Option.some s0])
  | .THIS => do
      return _root_.specTecPrintFinish (_root_.Option.some "this")
  | .«'...'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "...")
  | .«% %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1])
  | .«% % %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1, _root_.Option.some s2])
  | .«% '?' % ':' %» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← print_expression x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "?", _root_.Option.some s1, _root_.Option.some ":", _root_.Option.some s2])
  | .«`( % `) %» x0 x1 => do
      let s0 ← print_type x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"], _root_.Option.some s1])
  | .«'{#}'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "{#}")
  | .«`{ % % `}» x0 x1 => do
      let s0 ← print_sequenceOrRecordElementExpression x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "{", _root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some s1], _root_.Option.some "}"])
  | .«ERROR '.' %» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "error", _root_.Option.some ".", _root_.Option.some s0])
  | .«% '.' %» x0 x1 => do
      let s0 ← print_memberAccessBase x0
      let s1 ← _root_.SpecTecPrint.print? x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ".", _root_.Option.some s1])
  | .«% `[ % `]» x0 x1 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.Option.some s1, _root_.Option.some "]"]])
  | .«% `[ % % % `]» x0 x1 x2 x3 => do
      let s0 ← print_expression x0
      let s1 ← print_expression x1
      let s2 ← _root_.SpecTecPrint.print? x2
      let s3 ← print_expression x3
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "[", _root_.specTecPrintFiltered [_root_.Option.some s1, _root_.Option.some s2, _root_.Option.some s3], _root_.Option.some "]"]])
  | .«% `( % `)» x0 x1 => do
      let s0 ← print_callTarget x0
      let s1 ← print_argumentList x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s1, _root_.Option.some ")"]])
  | .«% `< % `> `( % `)» x0 x1 x2 => do
      let s0 ← print_expression x0
      let s1 ← print_realTypeArgumentList x1
      let s2 ← print_argumentList x2
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.specTecPrintFiltered [_root_.Option.some "<", _root_.Option.some s1, _root_.Option.some ">"], _root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s2, _root_.Option.some ")"]])
  | .«`( % `)» x0 => do
      let s0 ← print_expression x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some "(", _root_.Option.some s0, _root_.Option.some ")"])
  | .«% ',' %» x0 x1 => do
      let s0 ← print_expressionList x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ",", _root_.Option.some s1])
termination_by structural value

def print_namedExpressionList (value : namedExpressionList) : _root_.Option _root_.String :=
  match value with
  | .«% '=' %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some s1])
  | .«% ',' %» x0 x1 => do
      let s0 ← print_namedExpressionList x0
      let s1 ← print_namedExpression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some ",", _root_.Option.some s1])
termination_by structural value

def print_namedExpression (value : namedExpression) : _root_.Option _root_.String :=
  match value with
  | .«% '=' %» x0 x1 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      let s1 ← print_expression x1
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.some s0, _root_.Option.some "=", _root_.Option.some s1])
termination_by structural value

end

instance : _root_.SpecTecPrint type := ⟨print_type⟩

instance : _root_.SpecTecPrint namedExpression := ⟨print_namedExpression⟩

instance : _root_.SpecTecPrint namedExpressionList := ⟨print_namedExpressionList⟩

instance : _root_.SpecTecPrint expression := ⟨print_expression⟩

instance : _root_.SpecTecPrint expressionList := ⟨print_expressionList⟩

instance : _root_.SpecTecPrint memberAccessBase := ⟨print_memberAccessBase⟩

instance : _root_.SpecTecPrint sequenceOrRecordElementExpression := ⟨print_sequenceOrRecordElementExpression⟩

instance : _root_.SpecTecPrint callTarget := ⟨print_callTarget⟩

instance : _root_.SpecTecPrint realTypeArgument := ⟨print_realTypeArgument⟩

instance : _root_.SpecTecPrint realTypeArgumentList := ⟨print_realTypeArgumentList⟩

instance : _root_.SpecTecPrint typeArgument := ⟨print_typeArgument⟩

instance : _root_.SpecTecPrint typeArgumentList := ⟨print_typeArgumentList⟩

instance : _root_.SpecTecPrint argument := ⟨print_argument⟩

instance : _root_.SpecTecPrint argumentListNonEmpty := ⟨print_argumentListNonEmpty⟩

instance : _root_.SpecTecPrint argumentList := ⟨print_argumentList⟩


abbrev callableTarget : Type := expression


inductive baseType : Type where
  | BOOL : baseType
  | ERROR : baseType
  | MATCH_KIND : baseType
  | STRING : baseType
  | INT : baseType
  | «INT `< % `>» : _root_.Int → baseType
  | «INT `< `( % `) `>» : expression → baseType
  | BIT : baseType
  | «BIT `< % `>» : _root_.Int → baseType
  | «BIT `< `( % `) `>» : expression → baseType
  | «VARBIT `< % `>» : _root_.Int → baseType
  | «VARBIT `< `( % `) `>» : expression → baseType
deriving _root_.DecidableEq


inductive specializedType : Type where
  | «% `< % `>» : prefixedTypeName → typeArgumentList → specializedType
deriving _root_.DecidableEq


inductive namedType : Type where
  | _TID : _root_.String → namedType
  | «_TID '.' %» : typeName → namedType
  | «% `< % `>» : prefixedTypeName → typeArgumentList → namedType
deriving _root_.DecidableEq


inductive arrayType : Type where
  | «% `[ % `]» : type → expression → arrayType
deriving _root_.DecidableEq


inductive listType : Type where
  | «LIST `< % `>» : typeArgument → listType
deriving _root_.DecidableEq


inductive tupleType : Type where
  | «TUPLE `< % `>» : typeArgumentList → tupleType
deriving _root_.DecidableEq


inductive typeOrVoid : Type where
  | BOOL : typeOrVoid
  | ERROR : typeOrVoid
  | MATCH_KIND : typeOrVoid
  | STRING : typeOrVoid
  | INT : typeOrVoid
  | «INT `< % `>» : _root_.Int → typeOrVoid
  | «INT `< `( % `) `>» : expression → typeOrVoid
  | BIT : typeOrVoid
  | «BIT `< % `>» : _root_.Int → typeOrVoid
  | «BIT `< `( % `) `>» : expression → typeOrVoid
  | «VARBIT `< % `>» : _root_.Int → typeOrVoid
  | «VARBIT `< `( % `) `>» : expression → typeOrVoid
  | _TID : _root_.String → typeOrVoid
  | «_TID '.' %» : typeName → typeOrVoid
  | «% `< % `>» : prefixedTypeName → typeArgumentList → typeOrVoid
  | «% `[ % `]» : type → expression → typeOrVoid
  | «LIST `< % `>» : typeArgument → typeOrVoid
  | «TUPLE `< % `>» : typeArgumentList → typeOrVoid
  | VOID : typeOrVoid
  | _ID : _root_.String → typeOrVoid
deriving _root_.DecidableEq

end SpecTec
