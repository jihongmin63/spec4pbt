import SpecTecDecl0435

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def TableEntry_keyset_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : keysetExpression) (arg3 : tableEntryState) (arg4 : keysetExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableEntryState × keysetExpressionIR), SpecTecCall.TableEntry_keyset_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableEntry_keyset_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableEntry_keyset_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableEntry_keyset_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableEntry_keyset_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableEntry_keyset_ok] unexpandRelationNotation
end Notation.TableEntry_keyset_ok


noncomputable def TableEntry_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : tableEntry) (arg3 : tableEntryState) (arg4 : tableEntryIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableEntryState × tableEntryIR), SpecTecCall.TableEntry_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableEntry_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableEntry_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableEntry_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableEntry_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableEntry_ok] unexpandRelationNotation
end Notation.TableEntry_ok


noncomputable def «TableProperty_ok:entries:iter:2» (arg0 : typingContext) (arg1 : tableContext) (arg2 : (_root_.List tableEntry)) (arg3 : (_root_.List tableEntryState)) (arg4 : (_root_.List tableEntryIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List tableEntryState) × (_root_.List tableEntryIR)), SpecTecCall.«TableProperty_ok:entries:iter:2» arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply


noncomputable def TableProperty_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : tableProperty) (arg3 : tableContext) (arg4 : tablePropertyIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableContext × tablePropertyIR), SpecTecCall.TableProperty_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableProperty_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableProperty_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableProperty_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableProperty_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableProperty_ok] unexpandRelationNotation
end Notation.TableProperty_ok


noncomputable def TableProperties_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : (_root_.List tableProperty)) (arg3 : tableContext) (arg4 : tablePropertyListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableContext × tablePropertyListIR), SpecTecCall.TableProperties_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableProperties_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableProperties_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableProperties_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableProperties_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableProperties_ok] unexpandRelationNotation
end Notation.TableProperties_ok


noncomputable def Table_ok (arg0 : typingContext) (arg1 : (_root_.List tableProperty)) (arg2 : tableContext) (arg3 : tablePropertyListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableContext × tablePropertyListIR), SpecTecCall.Table_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.Table_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Table_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Table_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Table_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Table_ok] unexpandRelationNotation
end Notation.Table_ok


noncomputable def ControlLocalDecl_ok (arg0 : typingContext) (arg1 : controlLocalDeclaration) (arg2 : typingContext) (arg3 : controlLocalDeclarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × controlLocalDeclarationIR), SpecTecCall.ControlLocalDecl_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ControlLocalDecl_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ControlLocalDecl_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ControlLocalDecl_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ControlLocalDecl_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ControlLocalDecl_ok] unexpandRelationNotation
end Notation.ControlLocalDecl_ok


noncomputable def ControlLocalDecls_ok (arg0 : typingContext) (arg1 : (_root_.List controlLocalDeclaration)) (arg2 : typingContext) (arg3 : (_root_.List controlLocalDeclarationIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List controlLocalDeclarationIR)), SpecTecCall.ControlLocalDecls_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ControlLocalDecls_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ControlLocalDecls_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ControlLocalDecls_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ControlLocalDecls_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ControlLocalDecls_ok] unexpandRelationNotation
end Notation.ControlLocalDecls_ok


noncomputable def ControlLocalDeclList_ok (arg0 : typingContext) (arg1 : controlLocalDeclarationList) (arg2 : typingContext) (arg3 : (_root_.List controlLocalDeclarationIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List controlLocalDeclarationIR)), SpecTecCall.ControlLocalDeclList_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ControlLocalDeclList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ControlLocalDeclList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ControlLocalDeclList_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ControlLocalDeclList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ControlLocalDeclList_ok] unexpandRelationNotation
end Notation.ControlLocalDeclList_ok


noncomputable def Decl_ok (arg0 : typingContext) (arg1 : declaration) (arg2 : typingContext) (arg3 : declarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × declarationIR), SpecTecCall.Decl_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.Decl_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Decl_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Decl_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Decl_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Decl_ok] unexpandRelationNotation
end Notation.Decl_ok


noncomputable def Decls_ok (arg0 : typingContext) (arg1 : (_root_.List declaration)) (arg2 : typingContext) (arg3 : (_root_.List declarationIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List declarationIR)), SpecTecCall.Decls_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.Decls_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Decls_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Decls_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Decls_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Decls_ok] unexpandRelationNotation
end Notation.Decls_ok


noncomputable def Program_ok (arg0 : p4program) (arg1 : p4programIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨p4programIR, SpecTecCall.Program_ok arg0⟩) 0 (.success (.of (arg1))) finalSupply

namespace Notation.Program_ok
scoped notation:50 " |- " x0:51 " : " x1:51 => _root_.SpecTec.Program_ok x0 x1
end Notation.Program_ok


noncomputable def Expr_inst (arg0 : cursor) (arg1 : instContext) (arg2 : store) (arg3 : typedExpressionIR) (arg4 : store) (arg5 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × value), SpecTecCall.Expr_inst arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, arg5)))) finalSupply

namespace Notation.Expr_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Expr_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Expr_inst.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Expr_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Expr_inst] unexpandRelationNotation
end Notation.Expr_inst


noncomputable def Exprs_inst (arg0 : cursor) (arg1 : instContext) (arg2 : store) (arg3 : (_root_.List typedExpressionIR)) (arg4 : store) (arg5 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × (_root_.List value)), SpecTecCall.Exprs_inst arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, arg5)))) finalSupply

namespace Notation.Exprs_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Exprs_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Exprs_inst.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Exprs_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Exprs_inst] unexpandRelationNotation
end Notation.Exprs_inst


noncomputable def Argument_inst (arg0 : cursor) (arg1 : instContext) (arg2 : store) (arg3 : argumentIR) (arg4 : store) (arg5 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × value), SpecTecCall.Argument_inst arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, arg5)))) finalSupply

namespace Notation.Argument_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Argument_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Argument_inst.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Argument_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Argument_inst] unexpandRelationNotation
end Notation.Argument_inst


noncomputable def DirectApplicationStmt_inst (arg0 : cursor) (arg1 : instContext) (arg2 : store) (arg3 : directApplicationStatementIR) (arg4 : store) (arg5 : constantDeclarationIR) (arg6 : callStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × (constantDeclarationIR × callStatementIR)), SpecTecCall.DirectApplicationStmt_inst arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.DirectApplicationStmt_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.DirectApplicationStmt_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.DirectApplicationStmt_inst.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.DirectApplicationStmt_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.DirectApplicationStmt_inst] unexpandRelationNotation
end Notation.DirectApplicationStmt_inst


noncomputable def Stmt_inst (arg0 : cursor) (arg1 : instContext) (arg2 : store) (arg3 : statementIR) (arg4 : instContext) (arg5 : store) (arg6 : statementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × statementIR)), SpecTecCall.Stmt_inst arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Stmt_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Stmt_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Stmt_inst.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Stmt_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Stmt_inst] unexpandRelationNotation
end Notation.Stmt_inst


noncomputable def BlockElementStmt_inst (arg0 : instContext) (arg1 : store) (arg2 : blockElementStatementIR) (arg3 : instContext) (arg4 : store) (arg5 : blockElementStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × blockElementStatementIR)), SpecTecCall.BlockElementStmt_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.BlockElementStmt_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.BlockElementStmt_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.BlockElementStmt_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.BlockElementStmt_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.BlockElementStmt_inst] unexpandRelationNotation
end Notation.BlockElementStmt_inst


noncomputable def BlockElementStmtList_inst (arg0 : instContext) (arg1 : store) (arg2 : blockElementStatementListIR) (arg3 : instContext) (arg4 : store) (arg5 : (_root_.List blockElementStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × (_root_.List blockElementStatementIR))), SpecTecCall.BlockElementStmtList_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.BlockElementStmtList_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.BlockElementStmtList_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.BlockElementStmtList_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.BlockElementStmtList_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.BlockElementStmtList_inst] unexpandRelationNotation
end Notation.BlockElementStmtList_inst


noncomputable def Block_inst (arg0 : instContext) (arg1 : store) (arg2 : blockStatementIR) (arg3 : instContext) (arg4 : store) (arg5 : blockStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × blockStatementIR)), SpecTecCall.Block_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.Block_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Block_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Block_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Block_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Block_inst] unexpandRelationNotation
end Notation.Block_inst


noncomputable def ParserStmt_inst (arg0 : instContext) (arg1 : store) (arg2 : parserStatementIR) (arg3 : instContext) (arg4 : store) (arg5 : parserStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × parserStatementIR)), SpecTecCall.ParserStmt_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserStmt_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserStmt_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserStmt_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserStmt_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserStmt_inst] unexpandRelationNotation
end Notation.ParserStmt_inst


noncomputable def ParserBlockElementStmt_inst (arg0 : instContext) (arg1 : store) (arg2 : parserBlockElementStatementIR) (arg3 : instContext) (arg4 : store) (arg5 : parserBlockElementStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × parserBlockElementStatementIR)), SpecTecCall.ParserBlockElementStmt_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserBlockElementStmt_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlockElementStmt_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserBlockElementStmt_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlockElementStmt_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlockElementStmt_inst] unexpandRelationNotation
end Notation.ParserBlockElementStmt_inst


noncomputable def ParserBlockElementStmtList_inst (arg0 : instContext) (arg1 : store) (arg2 : parserBlockElementStatementListIR) (arg3 : instContext) (arg4 : store) (arg5 : (_root_.List parserBlockElementStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × (_root_.List parserBlockElementStatementIR))), SpecTecCall.ParserBlockElementStmtList_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserBlockElementStmtList_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlockElementStmtList_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserBlockElementStmtList_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlockElementStmtList_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlockElementStmtList_inst] unexpandRelationNotation
end Notation.ParserBlockElementStmtList_inst


noncomputable def ParserBlock_inst (arg0 : instContext) (arg1 : store) (arg2 : parserBlockStatementIR) (arg3 : instContext) (arg4 : store) (arg5 : parserBlockStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × parserBlockStatementIR)), SpecTecCall.ParserBlock_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserBlock_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlock_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserBlock_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlock_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlock_inst] unexpandRelationNotation
end Notation.ParserBlock_inst


noncomputable def ParserState_inst (arg0 : instContext) (arg1 : store) (arg2 : parserStateIR) (arg3 : instContext) (arg4 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × store), SpecTecCall.ParserState_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.ParserState_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserState_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.ParserState_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserState_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserState_inst] unexpandRelationNotation
end Notation.ParserState_inst


noncomputable def ParserStates_inst (arg0 : instContext) (arg1 : store) (arg2 : (_root_.List parserStateIR)) (arg3 : instContext) (arg4 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × store), SpecTecCall.ParserStates_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.ParserStates_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserStates_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.ParserStates_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserStates_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserStates_inst] unexpandRelationNotation
end Notation.ParserStates_inst


noncomputable def ParserLocalDecl_inst (arg0 : instContext) (arg1 : store) (arg2 : parserLocalDeclarationIR) (arg3 : instContext) (arg4 : store) (arg5 : parserLocalDeclarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × parserLocalDeclarationIR)), SpecTecCall.ParserLocalDecl_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserLocalDecl_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserLocalDecl_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserLocalDecl_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserLocalDecl_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserLocalDecl_inst] unexpandRelationNotation
end Notation.ParserLocalDecl_inst


noncomputable def ParserLocalDecls_inst (arg0 : instContext) (arg1 : store) (arg2 : (_root_.List parserLocalDeclarationIR)) (arg3 : instContext) (arg4 : store) (arg5 : (_root_.List parserLocalDeclarationIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × (_root_.List parserLocalDeclarationIR))), SpecTecCall.ParserLocalDecls_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserLocalDecls_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserLocalDecls_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserLocalDecls_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserLocalDecls_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserLocalDecls_inst] unexpandRelationNotation
end Notation.ParserLocalDecls_inst


noncomputable def TableProperty_inst (arg0 : instContext) (arg1 : store) (arg2 : tablePropertyIR) (arg3 : store) (arg4 : tablePropertyIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × tablePropertyIR), SpecTecCall.TableProperty_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableProperty_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableProperty_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableProperty_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableProperty_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableProperty_inst] unexpandRelationNotation
end Notation.TableProperty_inst


noncomputable def TableProperties_inst (arg0 : instContext) (arg1 : store) (arg2 : (_root_.List tablePropertyIR)) (arg3 : store) (arg4 : (_root_.List tablePropertyIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × (_root_.List tablePropertyIR)), SpecTecCall.TableProperties_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableProperties_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableProperties_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableProperties_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableProperties_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableProperties_inst] unexpandRelationNotation
end Notation.TableProperties_inst


noncomputable def ControlLocalDecl_inst (arg0 : instContext) (arg1 : store) (arg2 : controlLocalDeclarationIR) (arg3 : instContext) (arg4 : store) (arg5 : (_root_.Option controlLocalDeclarationIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × (_root_.Option controlLocalDeclarationIR))), SpecTecCall.ControlLocalDecl_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ControlLocalDecl_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ControlLocalDecl_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ControlLocalDecl_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ControlLocalDecl_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ControlLocalDecl_inst] unexpandRelationNotation
end Notation.ControlLocalDecl_inst


noncomputable def ControlLocalDecls_inst (arg0 : instContext) (arg1 : store) (arg2 : (_root_.List controlLocalDeclarationIR)) (arg3 : instContext) (arg4 : store) (arg5 : (_root_.List controlLocalDeclarationIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × (_root_.List controlLocalDeclarationIR))), SpecTecCall.ControlLocalDecls_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ControlLocalDecls_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ControlLocalDecls_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ControlLocalDecls_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ControlLocalDecls_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ControlLocalDecls_inst] unexpandRelationNotation
end Notation.ControlLocalDecls_inst

end SpecTec
