import SpecTecDecl0115

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «exec:match:setValue:SET `{ % '&&&' % `}» : setValue → Bool
  | .«SET `{ % '&&&' % `}» _ _ => true
  | _ => false


def «exec:match:setValue:SET `{ % '..' % `}» : setValue → Bool
  | .«SET `{ % '..' % `}» _ _ => true
  | _ => false


def «exec:match:setValue:SET `{ % `( % `) `}» : setValue → Bool
  | .«SET `{ % `( % `) `}» _ _ => true
  | _ => false


def «exec:match:setValue:SET `{ % `}» : setValue → Bool
  | .«SET `{ % `}» _ => true
  | _ => false


def «exec:match:setValue:SET `{ '...' `}» : setValue → Bool
  | .«SET `{ '...' `}» => true
  | _ => false


def «exec:match:simpleKeysetExpression:% '&&&' %» : simpleKeysetExpression → Bool
  | .«% '&&&' %» _ _ => true
  | _ => false


def «exec:match:simpleKeysetExpression:% '..' %» : simpleKeysetExpression → Bool
  | .«% '..' %» _ _ => true
  | _ => false


def «exec:match:simpleKeysetExpression:'_'» : simpleKeysetExpression → Bool
  | .«'_'» => true
  | _ => false


def «exec:match:simpleKeysetExpression:DEFAULT» : simpleKeysetExpression → Bool
  | .DEFAULT => true
  | _ => false


def «exec:match:simpleKeysetExpressionIR:% '&&&' %» : simpleKeysetExpressionIR → Bool
  | .«% '&&&' %» _ _ => true
  | _ => false


def «exec:match:simpleKeysetExpressionIR:% '..' %» : simpleKeysetExpressionIR → Bool
  | .«% '..' %» _ _ => true
  | _ => false


def «exec:match:simpleKeysetExpressionIR:'_'» : simpleKeysetExpressionIR → Bool
  | .«'_'» => true
  | _ => false


def «exec:match:simpleKeysetExpressionIR:DEFAULT» : simpleKeysetExpressionIR → Bool
  | .DEFAULT => true
  | _ => false


def «exec:match:simpleKeysetExpressionList:% ',' %» : simpleKeysetExpressionList → Bool
  | .«% ',' %» _ _ => true
  | _ => false


def «exec:match:sliceop:'+:'» : sliceop → Bool
  | .«'+:'» => true
  | _ => false


def «exec:match:sliceop:':'» : sliceop → Bool
  | .«':'» => true
  | _ => false


def «exec:match:stateExpression:% ';'» : stateExpression → Bool
  | .«% ';'» _ => true
  | _ => false


def «exec:match:stateExpressionIR:% ';'» : stateExpressionIR → Bool
  | .«% ';'» _ => true
  | _ => false


def «exec:match:storageReference:% '.' %» : storageReference → Bool
  | .«% '.' %» _ _ => true
  | _ => false


def «exec:match:storageReference:% `[ % % % `]» : storageReference → Bool
  | .«% `[ % % % `]» _ _ _ _ => true
  | _ => false


def «exec:match:storageReference:% `[ % `]» : storageReference → Bool
  | .«% `[ % `]» _ _ => true
  | _ => false


def «exec:match:switchCase:% ':'» : switchCase → Bool
  | .«% ':'» _ => true
  | _ => false


def «exec:match:switchCase:% ':' %» : switchCase → Bool
  | .«% ':' %» _ _ => true
  | _ => false


def «exec:match:switchCaseIR:% ':'» : switchCaseIR → Bool
  | .«% ':'» _ => true
  | _ => false


def «exec:match:switchCaseIR:% ':' %» : switchCaseIR → Bool
  | .«% ':' %» _ _ => true
  | _ => false


def «exec:match:switchCaseList:% %» : switchCaseList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:switchCaseList:_EMPTY» : switchCaseList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:switchLabelIR:DEFAULT» : switchLabelIR → Bool
  | .DEFAULT => true
  | _ => false


def «exec:match:tableActionList:% %» : tableActionList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:tableActionList:_EMPTY» : tableActionList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:tableActionReference:% `( % `)» : tableActionReference → Bool
  | .«% `( % `)» _ _ => true
  | _ => false


def «exec:match:tableCustomPropertyIR:% % CUSTOM % % ';'» : tableCustomPropertyIR → Bool
  | .«% % CUSTOM % % ';'» _ _ _ _ => true
  | _ => false

end SpecTec
