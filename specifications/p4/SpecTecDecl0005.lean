import SpecTecDecl0004

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive switchLabel : Type where
  | DEFAULT : switchLabel
  | TRUE : switchLabel
  | FALSE : switchLabel
  | D : _root_.Int → switchLabel
  | «% W %» : _root_.Nat → _root_.Int → switchLabel
  | «% S %» : _root_.Nat → _root_.Int → switchLabel
  | «'"' % '"'» : _root_.String → switchLabel
  | _ID : _root_.String → switchLabel
  | APPLY : switchLabel
  | KEY : switchLabel
  | ACTIONS : switchLabel
  | STATE : switchLabel
  | ENTRIES : switchLabel
  | TYPE : switchLabel
  | PRIORITY : switchLabel
  | «_ID '.' %» : nonTypeName → switchLabel
  | THIS : switchLabel
  | «% %» : unop → expression → switchLabel
  | «% % %» : expressionNonBrace → binop → expression → switchLabel
  | «% '?' % ':' %» : expressionNonBrace → expression → expression → switchLabel
  | «`( % `) %» : type → expression → switchLabel
  | «ERROR '.' %» : member → switchLabel
  | «% '.' %» : memberAccessBaseNonBrace → member → switchLabel
  | «% `[ % `]» : expressionNonBrace → expression → switchLabel
  | «% `[ % % % `]» : expressionNonBrace → expression → sliceop → expression → switchLabel
  | «% `( % `)» : callTargetNonBrace → argumentList → switchLabel
  | «% `< % `> `( % `)» : callableTargetNonBrace → realTypeArgumentList → argumentList → switchLabel
  | «`( % `)» : expression → switchLabel
deriving _root_.DecidableEq


inductive breakStatement : Type where
  | «BREAK ';'» : breakStatement
deriving _root_.DecidableEq


inductive continueStatement : Type where
  | «CONTINUE ';'» : continueStatement
deriving _root_.DecidableEq


inductive initializer : Type where
  | «'=' %» : expression → initializer
deriving _root_.DecidableEq


inductive initializerOpt : Type where
  | _EMPTY : initializerOpt
  | «'=' %» : expression → initializerOpt
deriving _root_.DecidableEq


inductive errorDeclaration : Type where
  | «ERROR `{ % `}» : nameList → errorDeclaration
deriving _root_.DecidableEq


inductive matchKindDeclaration : Type where
  | «MATCH_KIND `{ % % `}» : nameList → trailingCommaOpt → matchKindDeclaration
deriving _root_.DecidableEq


inductive selectCase : Type where
  | «% ':' % ';'» : keysetExpression → name → selectCase
deriving _root_.DecidableEq


inductive selectCaseList : Type where
  | _EMPTY : selectCaseList
  | «% %» : selectCaseList → selectCase → selectCaseList
deriving _root_.DecidableEq


inductive selectExpression : Type where
  | «SELECT `( % `) `{ % `}» : expressionList → selectCaseList → selectExpression
deriving _root_.DecidableEq


inductive stateExpression : Type where
  | «% ';'» : name → stateExpression
  | «SELECT `( % `) `{ % `}» : expressionList → selectCaseList → stateExpression
deriving _root_.DecidableEq


inductive transitionStatement : Type where
  | _EMPTY : transitionStatement
  | TRANSITION : stateExpression → transitionStatement
deriving _root_.DecidableEq


inductive valueSetType : Type where
  | BOOL : valueSetType
  | ERROR : valueSetType
  | MATCH_KIND : valueSetType
  | STRING : valueSetType
  | INT : valueSetType
  | «INT `< % `>» : _root_.Int → valueSetType
  | «INT `< `( % `) `>» : expression → valueSetType
  | BIT : valueSetType
  | «BIT `< % `>» : _root_.Int → valueSetType
  | «BIT `< `( % `) `>» : expression → valueSetType
  | «VARBIT `< % `>» : _root_.Int → valueSetType
  | «VARBIT `< `( % `) `>» : expression → valueSetType
  | «TUPLE `< % `>» : typeArgumentList → valueSetType
  | _TID : _root_.String → valueSetType
  | «_TID '.' %» : typeName → valueSetType
deriving _root_.DecidableEq


inductive const : Type where
  | CONST : const
deriving _root_.DecidableEq


inductive constOpt : Type where
  | _EMPTY : constOpt
  | CONST : constOpt
deriving _root_.DecidableEq


def «$flatten_constOpt:case_2:downcast:0» (arg0 : constOpt) : (_root_.Option const) := match arg0 with | .CONST => some (const.CONST) | _ => none


inductive tableActionReference : Type where
  | _ID : _root_.String → tableActionReference
  | APPLY : tableActionReference
  | KEY : tableActionReference
  | ACTIONS : tableActionReference
  | STATE : tableActionReference
  | ENTRIES : tableActionReference
  | TYPE : tableActionReference
  | PRIORITY : tableActionReference
  | «_ID '.' %» : nonTypeName → tableActionReference
  | «% `( % `)» : prefixedNonTypeName → argumentList → tableActionReference
deriving _root_.DecidableEq


inductive tableEntryPriority : Type where
  | «PRIORITY '=' % ':'» : integerLiteral → tableEntryPriority
  | «PRIORITY '=' `( % `) ':'» : expression → tableEntryPriority
deriving _root_.DecidableEq


inductive annotationToken : Type where
  | UNEXPECTED_TOKEN : annotationToken
  | ABSTRACT : annotationToken
  | ACTION : annotationToken
  | ACTIONS : annotationToken
  | APPLY : annotationToken
  | BOOL : annotationToken
  | BIT : annotationToken
  | BREAK : annotationToken
  | CONST : annotationToken
  | CONTINUE : annotationToken
  | CONTROL : annotationToken
  | DEFAULT : annotationToken
  | ELSE : annotationToken
  | ENTRIES : annotationToken
  | ENUM : annotationToken
  | ERROR : annotationToken
  | EXIT : annotationToken
  | EXTERN : annotationToken
  | FALSE : annotationToken
  | FOR : annotationToken
  | HEADER : annotationToken
  | HEADER_UNION : annotationToken
  | IF : annotationToken
  | IN : annotationToken
  | INOUT : annotationToken
  | INT : annotationToken
  | KEY : annotationToken
  | MATCH_KIND : annotationToken
  | TYPE : annotationToken
  | OUT : annotationToken
  | PARSER : annotationToken
  | PACKAGE : annotationToken
  | PRAGMA : annotationToken
  | RETURN : annotationToken
  | SELECT : annotationToken
  | STATE : annotationToken
  | STRING : annotationToken
  | STRUCT : annotationToken
  | SWITCH : annotationToken
  | TABLE : annotationToken
  | THIS : annotationToken
  | TRANSITION : annotationToken
  | TRUE : annotationToken
  | TUPLE : annotationToken
  | TYPEDEF : annotationToken
  | VARBIT : annotationToken
  | VALUE_SET : annotationToken
  | LIST : annotationToken
  | VOID : annotationToken
  | «'_'» : annotationToken
  | _ID : _root_.String → annotationToken
  | _TID : _root_.String → annotationToken
  | «'"' % '"'» : _root_.String → annotationToken
  | D : _root_.Int → annotationToken
  | «% W %» : _root_.Nat → _root_.Int → annotationToken
  | «% S %» : _root_.Nat → _root_.Int → annotationToken
  | «'&&&'» : annotationToken
  | «'..'» : annotationToken
  | «'<<'» : annotationToken
  | «'&&'» : annotationToken
  | «'||'» : annotationToken
  | «'=='» : annotationToken
  | «'!='» : annotationToken
  | «'>='» : annotationToken
  | «'<='» : annotationToken
  | «'++'» : annotationToken
  | «'+'» : annotationToken
  | «'|+|'» : annotationToken
  | «'-'» : annotationToken
  | «'|-|'» : annotationToken
  | «'*'» : annotationToken
  | «'/'» : annotationToken
  | «'%'» : annotationToken
  | «'|'» : annotationToken
  | «'&'» : annotationToken
  | «'^'» : annotationToken
  | «'~'» : annotationToken
  | «'['» : annotationToken
  | «']'» : annotationToken
  | «'{'» : annotationToken
  | «'}'» : annotationToken
  | «'<'» : annotationToken
  | «'>'» : annotationToken
  | «'!'» : annotationToken
  | «':'» : annotationToken
  | «','» : annotationToken
  | «'?'» : annotationToken
  | «'.'» : annotationToken
  | «'='» : annotationToken
  | «';'» : annotationToken
  | «'@'» : annotationToken
deriving _root_.DecidableEq


mutual

def print_annotationToken (value : annotationToken) : _root_.Option _root_.String :=
  match value with
  | .UNEXPECTED_TOKEN => do
      return _root_.specTecPrintFinish (_root_.Option.some "unexpected_token")
  | .ABSTRACT => do
      return _root_.specTecPrintFinish (_root_.Option.some "abstract")
  | .ACTION => do
      return _root_.specTecPrintFinish (_root_.Option.some "action")
  | .ACTIONS => do
      return _root_.specTecPrintFinish (_root_.Option.some "actions")
  | .APPLY => do
      return _root_.specTecPrintFinish (_root_.Option.some "apply")
  | .BOOL => do
      return _root_.specTecPrintFinish (_root_.Option.some "bool")
  | .BIT => do
      return _root_.specTecPrintFinish (_root_.Option.some "bit")
  | .BREAK => do
      return _root_.specTecPrintFinish (_root_.Option.some "break")
  | .CONST => do
      return _root_.specTecPrintFinish (_root_.Option.some "const")
  | .CONTINUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "continue")
  | .CONTROL => do
      return _root_.specTecPrintFinish (_root_.Option.some "control")
  | .DEFAULT => do
      return _root_.specTecPrintFinish (_root_.Option.some "default")
  | .ELSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "else")
  | .ENTRIES => do
      return _root_.specTecPrintFinish (_root_.Option.some "entries")
  | .ENUM => do
      return _root_.specTecPrintFinish (_root_.Option.some "enum")
  | .ERROR => do
      return _root_.specTecPrintFinish (_root_.Option.some "error")
  | .EXIT => do
      return _root_.specTecPrintFinish (_root_.Option.some "exit")
  | .EXTERN => do
      return _root_.specTecPrintFinish (_root_.Option.some "extern")
  | .FALSE => do
      return _root_.specTecPrintFinish (_root_.Option.some "false")
  | .FOR => do
      return _root_.specTecPrintFinish (_root_.Option.some "for")
  | .HEADER => do
      return _root_.specTecPrintFinish (_root_.Option.some "header")
  | .HEADER_UNION => do
      return _root_.specTecPrintFinish (_root_.Option.some "header_union")
  | .IF => do
      return _root_.specTecPrintFinish (_root_.Option.some "if")
  | .IN => do
      return _root_.specTecPrintFinish (_root_.Option.some "in")
  | .INOUT => do
      return _root_.specTecPrintFinish (_root_.Option.some "inout")
  | .INT => do
      return _root_.specTecPrintFinish (_root_.Option.some "int")
  | .KEY => do
      return _root_.specTecPrintFinish (_root_.Option.some "key")
  | .MATCH_KIND => do
      return _root_.specTecPrintFinish (_root_.Option.some "match_kind")
  | .TYPE => do
      return _root_.specTecPrintFinish (_root_.Option.some "type")
  | .OUT => do
      return _root_.specTecPrintFinish (_root_.Option.some "out")
  | .PARSER => do
      return _root_.specTecPrintFinish (_root_.Option.some "parser")
  | .PACKAGE => do
      return _root_.specTecPrintFinish (_root_.Option.some "package")
  | .PRAGMA => do
      return _root_.specTecPrintFinish (_root_.Option.some "pragma")
  | .RETURN => do
      return _root_.specTecPrintFinish (_root_.Option.some "return")
  | .SELECT => do
      return _root_.specTecPrintFinish (_root_.Option.some "select")
  | .STATE => do
      return _root_.specTecPrintFinish (_root_.Option.some "state")
  | .STRING => do
      return _root_.specTecPrintFinish (_root_.Option.some "string")
  | .STRUCT => do
      return _root_.specTecPrintFinish (_root_.Option.some "struct")
  | .SWITCH => do
      return _root_.specTecPrintFinish (_root_.Option.some "switch")
  | .TABLE => do
      return _root_.specTecPrintFinish (_root_.Option.some "table")
  | .THIS => do
      return _root_.specTecPrintFinish (_root_.Option.some "this")
  | .TRANSITION => do
      return _root_.specTecPrintFinish (_root_.Option.some "transition")
  | .TRUE => do
      return _root_.specTecPrintFinish (_root_.Option.some "true")
  | .TUPLE => do
      return _root_.specTecPrintFinish (_root_.Option.some "tuple")
  | .TYPEDEF => do
      return _root_.specTecPrintFinish (_root_.Option.some "typedef")
  | .VARBIT => do
      return _root_.specTecPrintFinish (_root_.Option.some "varbit")
  | .VALUE_SET => do
      return _root_.specTecPrintFinish (_root_.Option.some "value_set")
  | .LIST => do
      return _root_.specTecPrintFinish (_root_.Option.some "list")
  | .VOID => do
      return _root_.specTecPrintFinish (_root_.Option.some "void")
  | .«'_'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "_")
  | ._ID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | ._TID x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFiltered [_root_.Option.none, _root_.Option.some s0])
  | .«'"' % '"'» x0 => do
      let s0 ← _root_.SpecTecPrint.print? x0
      return _root_.specTecPrintFinish (_root_.specTecPrintFuse (_root_.specTecPrintFuse (_root_.Option.some "\"") (_root_.Option.some s0)) (_root_.Option.some "\""))
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
  | .«'&&&'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "&&&")
  | .«'..'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "..")
  | .«'<<'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "<<")
  | .«'&&'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "&&")
  | .«'||'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "||")
  | .«'=='» => do
      return _root_.specTecPrintFinish (_root_.Option.some "==")
  | .«'!='» => do
      return _root_.specTecPrintFinish (_root_.Option.some "!=")
  | .«'>='» => do
      return _root_.specTecPrintFinish (_root_.Option.some ">=")
  | .«'<='» => do
      return _root_.specTecPrintFinish (_root_.Option.some "<=")
  | .«'++'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "++")
  | .«'+'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "+")
  | .«'|+|'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "|+|")
  | .«'-'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "-")
  | .«'|-|'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "|-|")
  | .«'*'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "*")
  | .«'/'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "/")
  | .«'%'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "%")
  | .«'|'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "|")
  | .«'&'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "&")
  | .«'^'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "^")
  | .«'~'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "~")
  | .«'['» => do
      return _root_.specTecPrintFinish (_root_.Option.some "[")
  | .«']'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "]")
  | .«'{'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "{")
  | .«'}'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "}")
  | .«'<'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "<")
  | .«'>'» => do
      return _root_.specTecPrintFinish (_root_.Option.some ">")
  | .«'!'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "!")
  | .«':'» => do
      return _root_.specTecPrintFinish (_root_.Option.some ":")
  | .«','» => do
      return _root_.specTecPrintFinish (_root_.Option.some ",")
  | .«'?'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "?")
  | .«'.'» => do
      return _root_.specTecPrintFinish (_root_.Option.some ".")
  | .«'='» => do
      return _root_.specTecPrintFinish (_root_.Option.some "=")
  | .«';'» => do
      return _root_.specTecPrintFinish (_root_.Option.some ";")
  | .«'@'» => do
      return _root_.specTecPrintFinish (_root_.Option.some "@")

end

instance : _root_.SpecTecPrint annotationToken := ⟨print_annotationToken⟩


inductive annotationBody : Type where
  | _EMPTY : annotationBody
  | «% `( % `)» : annotationBody → annotationBody → annotationBody
  | «% %» : annotationBody → annotationToken → annotationBody
deriving _root_.DecidableEq


inductive structuredAnnotationBody : Type where
  | «% %» : sequenceOrRecordElementExpression → trailingCommaOpt → structuredAnnotationBody
deriving _root_.DecidableEq


inductive annotation : Type where
  | «'@' %» : name → annotation
  | «'@' % `( % `)» : name → annotationBody → annotation
  | «'@' % `[ % `]» : name → structuredAnnotationBody → annotation
  | «'@' PRAGMA % %» : name → annotationBody → annotation
deriving _root_.DecidableEq


inductive annotationListNonEmpty : Type where
  | «'@' %» : name → annotationListNonEmpty
  | «'@' % `( % `)» : name → annotationBody → annotationListNonEmpty
  | «'@' % `[ % `]» : name → structuredAnnotationBody → annotationListNonEmpty
  | «'@' PRAGMA % %» : name → annotationBody → annotationListNonEmpty
  | «% %» : annotationListNonEmpty → annotation → annotationListNonEmpty
deriving _root_.DecidableEq


inductive annotationList : Type where
  | _EMPTY : annotationList
  | «'@' %» : name → annotationList
  | «'@' % `( % `)» : name → annotationBody → annotationList
  | «'@' % `[ % `]» : name → structuredAnnotationBody → annotationList
  | «'@' PRAGMA % %» : name → annotationBody → annotationList
  | «% %» : annotationListNonEmpty → annotation → annotationList
deriving _root_.DecidableEq


inductive parameter : Type where
  | «% % % % %» : annotationList → direction → type → name → initializerOpt → parameter
deriving _root_.DecidableEq


inductive nonEmptyParameterList : Type where
  | «% % % % %» : annotationList → direction → type → name → initializerOpt → nonEmptyParameterList
  | «% ',' %» : nonEmptyParameterList → parameter → nonEmptyParameterList
deriving _root_.DecidableEq


inductive parameterList : Type where
  | _EMPTY : parameterList
  | «% % % % %» : annotationList → direction → type → name → initializerOpt → parameterList
  | «% ',' %» : nonEmptyParameterList → parameter → parameterList
deriving _root_.DecidableEq


def «$flatten_parameterList:case_2:downcast:0» (arg0 : parameterList) : (_root_.Option parameter) := match arg0 with | .«% % % % %» field0 field1 field2 field3 field4 => some (parameter.«% % % % %» field0 field1 field2 field3 field4) | _ => none


def «$flatten_parameterList:case_3:downcast:0» (arg0 : parameterList) : (_root_.Option nonEmptyParameterList) := match arg0 with | .«% % % % %» field0 field1 field2 field3 field4 => some (nonEmptyParameterList.«% % % % %» field0 field1 field2 field3 field4) | .«% ',' %» field0 field1 => some (nonEmptyParameterList.«% ',' %» field0 field1) | _ => none


abbrev constructorParameter : Type := parameter


abbrev constructorParameterList : Type := parameterList

end SpecTec
