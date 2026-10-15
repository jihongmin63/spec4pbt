import SpecTecDecl0125

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:functionTypeDefIR:definedFunctionTypeDefIR» : functionTypeDefIR → Bool
  | .«FUNCTION % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | _ => false


def «sub:functionTypeDefIR:externFunctionTypeDefIR» : functionTypeDefIR → Bool
  | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | _ => false


def «sub:initializerOpt:initializer» : initializerOpt → Bool
  | .«'=' %» _ => true
  | _ => false


def «sub:integerTypeIR:fixedBitTypeIR» : integerTypeIR → Bool
  | .«BIT `< % `>» _ => true
  | _ => false


def «sub:integerTypeIR:fixedIntTypeIR» : integerTypeIR → Bool
  | .«INT `< % `>» _ => true
  | _ => false


def «sub:integerTypeIR:intTypeIR» : integerTypeIR → Bool
  | .INT => true
  | _ => false


def «sub:integerTypeIR:varBitTypeIR» : integerTypeIR → Bool
  | .«VARBIT `< % `>» _ => true
  | _ => false


def «sub:integerValue:integerLiteral» : integerValue → Bool
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | _ => false


def «sub:keysetExpression:expression» : keysetExpression → Bool
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


def «sub:keysetExpression:simpleKeysetExpression» : keysetExpression → Bool
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
  | .«% '&&&' %» _ _ => true
  | .«% '..' %» _ _ => true
  | .DEFAULT => true
  | .«'_'» => true
  | _ => false


def «sub:keysetExpression:tupleKeysetExpression» : keysetExpression → Bool
  | .«`( % '&&&' % `)» _ _ => true
  | .«`( % '..' % `)» _ _ => true
  | .«`( DEFAULT `)» => true
  | .«`( '_' `)» => true
  | .«`( % ',' % `)» _ _ => true
  | _ => false


def «sub:keysetExpressionIR:simpleKeysetExpressionIR» : keysetExpressionIR → Bool
  | .«% '#' %» _ _ => true
  | .«% '&&&' %» _ _ => true
  | .«% '..' %» _ _ => true
  | .DEFAULT => true
  | .«'_'» => true
  | _ => false


def «sub:keysetExpressionIR:tupleKeysetExpressionIR» : keysetExpressionIR → Bool
  | .«`( % `)» _ => true
  | _ => false


def «sub:keysetExpressionResult:abortResult» : keysetExpressionResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:keysetExpressionResult:exitResult» : keysetExpressionResult → Bool
  | .EXIT => true
  | _ => false


def «sub:keysetExpressionResult:rejectTransitionResult» : keysetExpressionResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:localKind:definedFunctionLocalKind» : localKind → Bool
  | .«FUNCTION ':' %» _ => true
  | _ => false


def «sub:localKind:externFunctionLocalKind» : localKind → Bool
  | .«EXTERN_FUNCTION ':' %» _ => true
  | _ => false


def «sub:localKind:externMethodLocalKind» : localKind → Bool
  | .«EXTERN_METHOD ':' %» _ => true
  | .«EXTERN_METHOD ABSTRACT ':' %» _ => true
  | _ => false


def «sub:lvalue:prefixedNonTypeName» : lvalue → Bool
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


def «sub:lvalue:referenceExpression» : lvalue → Bool
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
  | _ => false


def «sub:lvalueIR:prefixedNameIR» : lvalueIR → Bool
  | ._BARE _ => true
  | .«'.' %» _ => true
  | _ => false


def «sub:memberAccessBase:expression» : memberAccessBase → Bool
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


def «sub:memberAccessBase:prefixedTypeName» : memberAccessBase → Bool
  | ._TID _ => true
  | .«_TID '.' %» _ => true
  | _ => false


def «sub:memberAccessBaseIR:typedExpressionIR» : memberAccessBaseIR → Bool
  | .«% '#' %» _ _ => true
  | _ => false


def «sub:memberAccessBaseNonBrace:expressionNonBrace» : memberAccessBaseNonBrace → Bool
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


def «sub:memberAccessBaseNonBrace:prefixedTypeName» : memberAccessBaseNonBrace → Bool
  | ._TID _ => true
  | .«_TID '.' %» _ => true
  | _ => false


def «sub:methodDef:controlApplyMethodDef» : methodDef → Bool
  | .«CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» _ _ _ _ => true
  | _ => false


def «sub:methodDef:externMethodDef» : methodDef → Bool
  | .«EXTERN_METHOD % `< % `> `( % `) %» _ _ _ _ => true
  | .«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» _ _ _ => true
  | _ => false


def «sub:methodDef:parserApplyMethodDef» : methodDef → Bool
  | .«PARSER_APPLY `( % `) `{ % ';' % `}» _ _ _ => true
  | _ => false


def «sub:methodDef:tableApplyMethodDef» : methodDef → Bool
  | .«TABLE_APPLY `{ % `}» _ => true
  | _ => false


def «sub:methodTypeDefIR:controlApplyMethodTypeIR» : methodTypeDefIR → Bool
  | .«CONTROL_APPLY `( % `)» _ => true
  | _ => false

end SpecTec
