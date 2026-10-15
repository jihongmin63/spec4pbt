import SpecTecDecl0110

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «exec:match:baseType:STRING» : baseType → Bool
  | .STRING => true
  | _ => false


def «exec:match:baseType:VARBIT `< % `>» : baseType → Bool
  | .«VARBIT `< % `>» _ => true
  | _ => false


def «exec:match:baseType:VARBIT `< `( % `) `>» : baseType → Bool
  | .«VARBIT `< `( % `) `>» _ => true
  | _ => false


def «exec:match:binop:'!='» : binop → Bool
  | .«'!='» => true
  | _ => false


def «exec:match:binop:'%'» : binop → Bool
  | .«'%'» => true
  | _ => false


def «exec:match:binop:'&'» : binop → Bool
  | .«'&'» => true
  | _ => false


def «exec:match:binop:'*'» : binop → Bool
  | .«'*'» => true
  | _ => false


def «exec:match:binop:'+'» : binop → Bool
  | .«'+'» => true
  | _ => false


def «exec:match:binop:'++'» : binop → Bool
  | .«'++'» => true
  | _ => false


def «exec:match:binop:'-'» : binop → Bool
  | .«'-'» => true
  | _ => false


def «exec:match:binop:'/'» : binop → Bool
  | .«'/'» => true
  | _ => false


def «exec:match:binop:'<'» : binop → Bool
  | .«'<'» => true
  | _ => false


def «exec:match:binop:'<<'» : binop → Bool
  | .«'<<'» => true
  | _ => false


def «exec:match:binop:'<='» : binop → Bool
  | .«'<='» => true
  | _ => false


def «exec:match:binop:'=='» : binop → Bool
  | .«'=='» => true
  | _ => false


def «exec:match:binop:'>'» : binop → Bool
  | .«'>'» => true
  | _ => false


def «exec:match:binop:'>='» : binop → Bool
  | .«'>='» => true
  | _ => false


def «exec:match:binop:'>>'» : binop → Bool
  | .«'>>'» => true
  | _ => false


def «exec:match:binop:'^'» : binop → Bool
  | .«'^'» => true
  | _ => false


def «exec:match:binop:'|'» : binop → Bool
  | .«'|'» => true
  | _ => false


def «exec:match:binop:'|+|'» : binop → Bool
  | .«'|+|'» => true
  | _ => false


def «exec:match:binop:'|-|'» : binop → Bool
  | .«'|-|'» => true
  | _ => false


def «exec:match:blockElementStatementList:% %» : blockElementStatementList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:blockElementStatementList:_EMPTY» : blockElementStatementList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:callExpression:% `( % `)» : callExpression → Bool
  | .«% `( % `)» _ _ => true
  | _ => false


def «exec:match:callExpression:% `< % `> `( % `)» : callExpression → Bool
  | .«% `< % `> `( % `)» _ _ _ => true
  | _ => false


def «exec:match:callExpressionIR:% `( % `)» : callExpressionIR → Bool
  | .«% `( % `)» _ _ => true
  | _ => false


def «exec:match:callExpressionIR:% `< % `> `( % `)» : callExpressionIR → Bool
  | .«% `< % `> `( % `)» _ _ _ => true
  | _ => false


def «exec:match:callExpressionNonBrace:% `( % `)» : callExpressionNonBrace → Bool
  | .«% `( % `)» _ _ => true
  | _ => false


def «exec:match:callExpressionNonBrace:% `< % `> `( % `)» : callExpressionNonBrace → Bool
  | .«% `< % `> `( % `)» _ _ _ => true
  | _ => false


def «exec:match:callStatement:% `( % `) ';'» : callStatement → Bool
  | .«% `( % `) ';'» _ _ => true
  | _ => false


def «exec:match:callStatement:% `< % `> `( % `) ';'» : callStatement → Bool
  | .«% `< % `> `( % `) ';'» _ _ _ => true
  | _ => false

end SpecTec
