import SpecTecDecl0116

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «exec:match:tableCustomPropertyIR:% % CUSTOM_CONST % % ';'» : tableCustomPropertyIR → Bool
  | .«% % CUSTOM_CONST % % ';'» _ _ _ _ => true
  | _ => false


def «exec:match:tableEntry:% % % ':' % % ';'» : tableEntry → Bool
  | .«% % % ':' % % ';'» _ _ _ _ _ => true
  | _ => false


def «exec:match:tableEntry:% % ':' % % ';'» : tableEntry → Bool
  | .«% % ':' % % ';'» _ _ _ _ => true
  | _ => false


def «exec:match:tableEntryList:% %» : tableEntryList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:tableEntryList:_EMPTY» : tableEntryList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:tableEntryPriority:PRIORITY '=' % ':'» : tableEntryPriority → Bool
  | .«PRIORITY '=' % ':'» _ => true
  | _ => false


def «exec:match:tableEntryPriority:PRIORITY '=' `( % `) ':'» : tableEntryPriority → Bool
  | .«PRIORITY '=' `( % `) ':'» _ => true
  | _ => false


def «exec:match:tableEntryState:LPM» : tableEntryState → Bool
  | .LPM _ => true
  | _ => false


def «exec:match:tableEntryState:NON_LPM» : tableEntryState → Bool
  | .NON_LPM => true
  | _ => false


def «exec:match:tableKeyList:% %» : tableKeyList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:tableKeyList:_EMPTY» : tableKeyList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:tableKeyValueInterface:% _SLASH %» : tableKeyValueInterface → Bool
  | .«% _SLASH %» _ _ => true
  | _ => false


def «exec:match:tableKeyValueInterface:_BIN» : tableKeyValueInterface → Bool
  | ._BIN _ => true
  | _ => false


def «exec:match:tableKeyValueInterface:_DEC» : tableKeyValueInterface → Bool
  | ._DEC _ => true
  | _ => false


def «exec:match:tableKeyValueInterface:_HEX» : tableKeyValueInterface → Bool
  | ._HEX _ => true
  | _ => false


def «exec:match:tableProperty:% % % % ';'» : tableProperty → Bool
  | .«% % % % ';'» _ _ _ _ => true
  | _ => false


def «exec:match:tableProperty:% % ENTRIES '=' `{ % `}» : tableProperty → Bool
  | .«% % ENTRIES '=' `{ % `}» _ _ _ => true
  | _ => false


def «exec:match:tableProperty:ACTIONS '=' `{ % `}» : tableProperty → Bool
  | .«ACTIONS '=' `{ % `}» _ => true
  | _ => false


def «exec:match:tableProperty:KEY '=' `{ % `}» : tableProperty → Bool
  | .«KEY '=' `{ % `}» _ => true
  | _ => false


def «exec:match:tablePropertyList:% %» : tablePropertyList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:tablePropertyList:_EMPTY» : tablePropertyList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:trailingCommaOpt:_EMPTY» : trailingCommaOpt → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:transitionStatement:TRANSITION» : transitionStatement → Bool
  | .TRANSITION _ => true
  | _ => false


def «exec:match:tupleKeysetExpression:`( % '&&&' % `)» : tupleKeysetExpression → Bool
  | .«`( % '&&&' % `)» _ _ => true
  | _ => false


def «exec:match:tupleKeysetExpression:`( % ',' % `)» : tupleKeysetExpression → Bool
  | .«`( % ',' % `)» _ _ => true
  | _ => false


def «exec:match:tupleKeysetExpression:`( % '..' % `)» : tupleKeysetExpression → Bool
  | .«`( % '..' % `)» _ _ => true
  | _ => false


def «exec:match:typeArgumentList:% ',' %» : typeArgumentList → Bool
  | .«% ',' %» _ _ => true
  | _ => false


def «exec:match:typeArgumentList:_EMPTY» : typeArgumentList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:typeFieldList:% %» : typeFieldList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:typeFieldList:_EMPTY» : typeFieldList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:typeOrVoid:VOID» : typeOrVoid → Bool
  | .VOID => true
  | _ => false


def «exec:match:typeParameterList:% ',' %» : typeParameterList → Bool
  | .«% ',' %» _ _ => true
  | _ => false

end SpecTec
