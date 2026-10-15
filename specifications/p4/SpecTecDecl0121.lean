import SpecTecDecl0120

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:callee:controlApplyMethodCallee» : callee → Bool
  | .«CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» _ _ _ _ _ _ _ _ => true
  | _ => false


def «sub:callee:definedFunctionCallee» : callee → Bool
  | .«FUNCTION % `< % `> `( % '#' % `) %» _ _ _ _ _ => true
  | _ => false


def «sub:callee:externFunctionCallee» : callee → Bool
  | .«EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» _ _ _ _ _ => true
  | _ => false


def «sub:callee:externMethodCallee» : callee → Bool
  | .«EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» _ _ _ _ _ _ _ _ _ => true
  | _ => false


def «sub:callee:parserApplyMethodCallee» : callee → Bool
  | .«PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» _ _ _ _ _ _ _ => true
  | _ => false


def «sub:callee:tableApplyMethodCallee» : callee → Bool
  | .«TABLE % '.' APPLY `{ % ';' % `}» _ _ _ => true
  | _ => false


def «sub:calleeResult:abortResult» : calleeResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:ce5381e22073a31cfba0971eaff16c1e» : tableKeyResult → Bool
  | ._CONT _ => true
  | _ => false


def «sub:constOpt:const» : constOpt → Bool
  | .CONST => true
  | _ => false


def «sub:constructorDef:controlObjectConstructorDef» : constructorDef → Bool
  | .«CONTROL `< % `> `( % `) `( % `) `{ % APPLY % `}» _ _ _ _ _ => true
  | _ => false


def «sub:constructorDef:externObjectConstructorDef» : constructorDef → Bool
  | .«EXTERN % `< % `> `( % `) `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:constructorDef:packageObjectConstructorDef» : constructorDef → Bool
  | .«PACKAGE `< % `> `( % `)» _ _ => true
  | _ => false


def «sub:constructorDef:parserObjectConstructorDef» : constructorDef → Bool
  | .«PARSER `< % `> `( % `) `( % `) `{ % % `}» _ _ _ _ _ => true
  | _ => false


def «sub:controlBodyResult:exitResult» : controlBodyResult → Bool
  | .EXIT => true
  | _ => false


def «sub:controlLocalDeclaration:actionDeclaration» : controlLocalDeclaration → Bool
  | .«% ACTION % `( % `) %» _ _ _ _ => true
  | _ => false


def «sub:controlLocalDeclaration:constantDeclaration» : controlLocalDeclaration → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:controlLocalDeclaration:instantiation» : controlLocalDeclaration → Bool
  | .«% % `( % `) % ';'» _ _ _ _ => true
  | .«% % `( % `) % % ';'» _ _ _ _ _ => true
  | _ => false


def «sub:controlLocalDeclaration:tableDeclaration» : controlLocalDeclaration → Bool
  | .«% TABLE % `{ % `}» _ _ _ => true
  | _ => false


def «sub:controlLocalDeclaration:variableDeclaration» : controlLocalDeclaration → Bool
  | .«% % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:controlLocalDeclarationIR:actionDeclarationIR» : controlLocalDeclarationIR → Bool
  | .«% ACTION % `( % `) %» _ _ _ _ => true
  | _ => false


def «sub:controlLocalDeclarationIR:constantDeclarationIR» : controlLocalDeclarationIR → Bool
  | .«% CONST % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:controlLocalDeclarationIR:instantiationIR» : controlLocalDeclarationIR → Bool
  | .«% % % `( % `) % % ';'» _ _ _ _ _ _ => true
  | _ => false


def «sub:controlLocalDeclarationIR:tableDeclarationIR» : controlLocalDeclarationIR → Bool
  | .«% TABLE % % `{ % `}» _ _ _ _ => true
  | _ => false


def «sub:controlLocalDeclarationIR:variableDeclarationIR» : controlLocalDeclarationIR → Bool
  | .«% % % % ';'» _ _ _ _ => true
  | _ => false


def «sub:controlLocalDeclarationResult:continueEmptyResult» : controlLocalDeclarationResult → Bool
  | ._EMPTY => true
  | _ => false


def «sub:controlLocalDeclarationResult:exitResult» : controlLocalDeclarationResult → Bool
  | .EXIT => true
  | _ => false


def «sub:copyInArgumentResult:abortResult» : copyInArgumentResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:copyInResult:abortResult» : copyInResult → Bool
  | .EXIT => true
  | .REJECT _ => true
  | _ => false


def «sub:copyInResult:exitResult» : copyInResult → Bool
  | .EXIT => true
  | _ => false


def «sub:copyInResult:rejectTransitionResult» : copyInResult → Bool
  | .REJECT _ => true
  | _ => false


def «sub:dataExpressionIR:invalidHeaderExpression» : dataExpressionIR → Bool
  | .«'{#}'» => true
  | _ => false


def «sub:dataExpressionIR:recordExpressionIR» : dataExpressionIR → Bool
  | .«RECORD `{ % `}» _ => true
  | .«RECORD `{ % ',' '...' `}» _ => true
  | _ => false

end SpecTec
