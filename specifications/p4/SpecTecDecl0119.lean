import SpecTecDecl0118

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:b279563c2fb8a313d071c57bb03d87d3» : expressionListResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:b9f5c7534fa7f3cdbd31b1c57258ac22» : tableMatchesResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:baseTypeIR:boolTypeIR» : baseTypeIR → Bool
  | .BOOL => true
  | _ => false


def «sub:baseTypeIR:errorTypeIR» : baseTypeIR → Bool
  | .ERROR => true
  | _ => false


def «sub:baseTypeIR:fixedBitTypeIR» : baseTypeIR → Bool
  | .«BIT `< % `>» _ => true
  | _ => false


def «sub:baseTypeIR:fixedIntTypeIR» : baseTypeIR → Bool
  | .«INT `< % `>» _ => true
  | _ => false


def «sub:baseTypeIR:intTypeIR» : baseTypeIR → Bool
  | .INT => true
  | _ => false


def «sub:baseTypeIR:matchKindTypeIR» : baseTypeIR → Bool
  | .MATCH_KIND => true
  | _ => false


def «sub:baseTypeIR:stringTypeIR» : baseTypeIR → Bool
  | .STRING => true
  | _ => false


def «sub:baseTypeIR:varBitTypeIR» : baseTypeIR → Bool
  | .«VARBIT `< % `>» _ => true
  | _ => false


def «sub:blockElementStatement:constantDeclaration» : blockElementStatement → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:blockElementStatement:statement» : blockElementStatement → Bool
  | .«';'» => true
  | .«% % % ';'» _ _ _ => true
  | .«% `( % `) ';'» _ _ => true
  | .«% `< % `> `( % `) ';'» _ _ _ => true
  | .«% '.' APPLY `( % `) ';'» _ _ => true
  | .«RETURN ';'» => true
  | .«RETURN % ';'» _ => true
  | .«EXIT ';'» => true
  | .«% `{ % `}» _ _ => true
  | .«IF `( % `) %» _ _ => true
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => true
  | .«% FOR `( % % IN % `) %» _ _ _ _ _ => true
  | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => true
  | .«BREAK ';'» => true
  | .«CONTINUE ';'» => true
  | .«SWITCH `( % `) `{ % `}» _ _ => true
  | _ => false


def «sub:blockElementStatement:variableDeclaration» : blockElementStatement → Bool
  | .«% % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:blockElementStatementIR:constantDeclarationIR» : blockElementStatementIR → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:blockElementStatementIR:statementIR» : blockElementStatementIR → Bool
  | .«';'» => true
  | .«% % % ';'» _ _ _ => true
  | .«% `< % `> `( % `) ';'» _ _ _ => true
  | .«% '.' APPLY `( % `) ';'» _ _ => true
  | .«RETURN ';'» => true
  | .«RETURN % ';'» _ => true
  | .«EXIT ';'» => true
  | .«% `{ % `}» _ _ => true
  | .«IF `( % `) %» _ _ => true
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => true
  | .«% FOR `( % % IN % `) %» _ _ _ _ _ => true
  | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => true
  | .«BREAK ';'» => true
  | .«CONTINUE ';'» => true
  | .«SWITCH `( % `) `{ % `}» _ _ => true
  | _ => false


def «sub:blockElementStatementIR:variableDeclarationIR» : blockElementStatementIR → Bool
  | .«% % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:builtinMethodTypeIR:builtinIsValidMethodTypeIR» : builtinMethodTypeIR → Bool
  | .BUILTIN_IS_VALID => true
  | _ => false


def «sub:builtinMethodTypeIR:builtinPopFrontMethodTypeIR» : builtinMethodTypeIR → Bool
  | .BUILTIN_POP_FRONT => true
  | _ => false


def «sub:builtinMethodTypeIR:builtinPushFrontMethodTypeIR» : builtinMethodTypeIR → Bool
  | .BUILTIN_PUSH_FRONT => true
  | _ => false


def «sub:builtinMethodTypeIR:builtinSetInvalidMethodTypeIR» : builtinMethodTypeIR → Bool
  | .BUILTIN_SET_INVALID => true
  | _ => false


def «sub:builtinMethodTypeIR:builtinSetValidMethodTypeIR» : builtinMethodTypeIR → Bool
  | .BUILTIN_SET_VALID => true
  | _ => false


def «sub:builtinMethodTypeIR:builtinSizeMethodTypeIR» : builtinMethodTypeIR → Bool
  | .BUILTIN_SIZE_OF => true
  | _ => false


def «sub:callResult:abortResult» : callResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:callResult:rejectTransitionResult» : callResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:callResult:returnResult» : callResult → Bool
  | .RETURN _ => true
  | _ => false


def «sub:callTarget:expression» : callTarget → Bool
  | .TRUE => true
  | .FALSE => true
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«'"' % '"'» _ => true
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | .«_ID '.' %» _ => true
  | .THIS => true
  | .«'...'» => true
  | .«% %» _ _ => true
  | .«% % %» _ _ _ => true
  | .«% '?' % ':' %» _ _ _ => true
  | .«`( % `) %» _ _ => true
  | .«'{#}'» => true
  | .«`{ % % `}» _ _ => true
  | .«ERROR '.' %» _ => true
  | .«% '.' %» _ _ => true
  | .«% `[ % `]» _ _ => true
  | .«% `[ % % % `]» _ _ _ _ => true
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«`( % `)» _ => true
  | _ => false


def «sub:callTarget:namedType» : callTarget → Bool
  | ._TID _ => true
  | .«_TID '.' %» _ => true
  | .«% `< % `>» _ _ => true
  | _ => false


def «sub:callTarget:prefixedNonTypeName» : callTarget → Bool
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | .«_ID '.' %» _ => true
  | _ => false


def «sub:callTarget:prefixedTypeName» : callTarget → Bool
  | ._TID _ => true
  | .«_TID '.' %» _ => true
  | _ => false


def «sub:callTarget:specializedType» : callTarget → Bool
  | .«% `< % `>» _ _ => true
  | _ => false


def «sub:callTargetNonBrace:expressionNonBrace» : callTargetNonBrace → Bool
  | .TRUE => true
  | .FALSE => true
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«'"' % '"'» _ => true
  | ._ID _ => true
  | .APPLY => true
  | .KEY => true
  | .ACTIONS => true
  | .STATE => true
  | .ENTRIES => true
  | .TYPE => true
  | .PRIORITY => true
  | .«_ID '.' %» _ => true
  | .THIS => true
  | .«% %» _ _ => true
  | .«% % %» _ _ _ => true
  | .«% '?' % ':' %» _ _ _ => true
  | .«`( % `) %» _ _ => true
  | .«ERROR '.' %» _ => true
  | .«% '.' %» _ _ => true
  | .«% `[ % `]» _ _ => true
  | .«% `[ % % % `]» _ _ _ _ => true
  | .«% `( % `)» _ _ => true
  | .«% `< % `> `( % `)» _ _ _ => true
  | .«`( % `)» _ => true
  | _ => false


def «sub:callTargetNonBrace:namedType» : callTargetNonBrace → Bool
  | ._TID _ => true
  | .«_TID '.' %» _ => true
  | .«% `< % `>» _ _ => true
  | _ => false

end SpecTec
