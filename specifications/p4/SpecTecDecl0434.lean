import SpecTecDecl0433

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def ConstDecl_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : constantDeclaration) (arg3 : typingContext) (arg4 : constantDeclarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × constantDeclarationIR), SpecTecCall.ConstDecl_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.ConstDecl_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ConstDecl_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.ConstDecl_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ConstDecl_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ConstDecl_ok] unexpandRelationNotation
end Notation.ConstDecl_ok


noncomputable def «Decl_ok:structTypeDeclaration:iter:4» (arg0 : typingContext) (arg1 : (_root_.List type)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List (_root_.List typeId))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeIR) × (_root_.List (_root_.List typeId))), SpecTecCall.«Decl_ok:structTypeDeclaration:iter:4» arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply


noncomputable def «Decl_ok:headerTypeDeclaration:iter:4» (arg0 : typingContext) (arg1 : (_root_.List type)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List (_root_.List typeId))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeIR) × (_root_.List (_root_.List typeId))), SpecTecCall.«Decl_ok:headerTypeDeclaration:iter:4» arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:4» (arg0 : typingContext) (arg1 : (_root_.List type)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List (_root_.List typeId))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeIR) × (_root_.List (_root_.List typeId))), SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:iter:4» arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply


noncomputable def CallableTarget_lvalue_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : lvalue) (arg3 : callableTargetIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableTargetIR, SpecTecCall.CallableTarget_lvalue_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.CallableTarget_lvalue_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.CallableTarget_lvalue_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.CallableTarget_lvalue_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.CallableTarget_lvalue_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.CallableTarget_lvalue_ok] unexpandRelationNotation
end Notation.CallableTarget_lvalue_ok


noncomputable def Parameters_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List parameter)) (arg3 : parameterListIR) (arg4 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(parameterListIR × (_root_.List typeId)), SpecTecCall.Parameters_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.Parameters_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Parameters_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Parameters_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, Lean.mkAtom "#", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.Parameters_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Parameters_ok] unexpandRelationNotation
end Notation.Parameters_ok


noncomputable def ParameterList_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : parameterList) (arg3 : typingContext) (arg4 : parameterListIR) (arg5 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (parameterListIR × (_root_.List typeId))), SpecTecCall.ParameterList_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParameterList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParameterList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParameterList_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, Lean.mkAtom "#", x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.ParameterList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParameterList_ok] unexpandRelationNotation
end Notation.ParameterList_ok


noncomputable def ConstructorParameterListOpt_ok (arg0 : typingContext) (arg1 : constructorParameterListOpt) (arg2 : typingContext) (arg3 : constructorParameterListIR) (arg4 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (constructorParameterListIR × (_root_.List typeId))), SpecTecCall.ConstructorParameterListOpt_ok arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.ConstructorParameterListOpt_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ConstructorParameterListOpt_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.ConstructorParameterListOpt_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3, Lean.mkAtom "#", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.ConstructorParameterListOpt_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ConstructorParameterListOpt_ok] unexpandRelationNotation
end Notation.ConstructorParameterListOpt_ok


noncomputable def ExternMethod_ok (arg0 : typingContext) (arg1 : typeId) (arg2 : externMethodPrototype) (arg3 : externMethodPrototypeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externMethodPrototypeIR, SpecTecCall.ExternMethod_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ExternMethod_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ExternMethod_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ExternMethod_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ExternMethod_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ExternMethod_ok] unexpandRelationNotation
end Notation.ExternMethod_ok


noncomputable def ExternConstructor_ok (arg0 : typingContext) (arg1 : typeId) (arg2 : externConstructorPrototype) (arg3 : externConstructorPrototypeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externConstructorPrototypeIR, SpecTecCall.ExternConstructor_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ExternConstructor_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ExternConstructor_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ExternConstructor_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ExternConstructor_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ExternConstructor_ok] unexpandRelationNotation
end Notation.ExternConstructor_ok


noncomputable def «Decl_ok:externObjectDeclaration:iter:3» (arg0 : typingContext) (arg1 : nameIR) (arg2 : (_root_.List externMethodPrototype)) (arg3 : (_root_.List externMethodPrototypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externMethodPrototypeIR), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:3» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_ok:externObjectDeclaration:iter:13» (arg0 : typingContext) (arg1 : nameIR) (arg2 : (_root_.List externConstructorPrototype)) (arg3 : (_root_.List externConstructorPrototypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externConstructorPrototypeIR), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:13» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def ForCollectionExpr_ok (arg0 : typingContext) (arg1 : typeIR) (arg2 : forCollectionExpression) (arg3 : forCollectionExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨forCollectionExpressionIR, SpecTecCall.ForCollectionExpr_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ForCollectionExpr_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForCollectionExpr_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ForCollectionExpr_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ForCollectionExpr_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForCollectionExpr_ok] unexpandRelationNotation
end Notation.ForCollectionExpr_ok


noncomputable def SwitchLabel_general_ok (arg0 : typingContext) (arg1 : typeIR) (arg2 : switchLabel) (arg3 : switchLabelIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨switchLabelIR, SpecTecCall.SwitchLabel_general_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.SwitchLabel_general_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchLabel_general_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.SwitchLabel_general_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchLabel_general_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchLabel_general_ok] unexpandRelationNotation
end Notation.SwitchLabel_general_ok


noncomputable def Stmt_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : statement) (arg3 : typingContext) (arg4 : statementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × statementIR), SpecTecCall.Stmt_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.Stmt_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Stmt_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Stmt_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Stmt_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Stmt_ok] unexpandRelationNotation
end Notation.Stmt_ok


noncomputable def BlockElementStmt_ok (arg0 : typingContext) (arg1 : blockElementStatement) (arg2 : typingContext) (arg3 : blockElementStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × blockElementStatementIR), SpecTecCall.BlockElementStmt_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.BlockElementStmt_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.BlockElementStmt_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.BlockElementStmt_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.BlockElementStmt_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.BlockElementStmt_ok] unexpandRelationNotation
end Notation.BlockElementStmt_ok


noncomputable def BlockElementStmtList_ok (arg0 : typingContext) (arg1 : blockElementStatementList) (arg2 : typingContext) (arg3 : (_root_.List blockElementStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List blockElementStatementIR)), SpecTecCall.BlockElementStmtList_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.BlockElementStmtList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.BlockElementStmtList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.BlockElementStmtList_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.BlockElementStmtList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.BlockElementStmtList_ok] unexpandRelationNotation
end Notation.BlockElementStmtList_ok


noncomputable def Block_ok (arg0 : typingContext) (arg1 : blockStatement) (arg2 : typingContext) (arg3 : blockStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × blockStatementIR), SpecTecCall.Block_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.Block_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Block_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Block_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Block_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Block_ok] unexpandRelationNotation
end Notation.Block_ok


noncomputable def ForUpdateStmt_ok (arg0 : typingContext) (arg1 : forUpdateStatement) (arg2 : forUpdateStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨forUpdateStatementIR, SpecTecCall.ForUpdateStmt_ok arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.ForUpdateStmt_ok
scoped notation:50 x0:51 " |- " x1:51 " : " x2:51 => _root_.SpecTec.ForUpdateStmt_ok x0 x1 x2
end Notation.ForUpdateStmt_ok


noncomputable def ForUpdateStmtList_ok (arg0 : typingContext) (arg1 : forUpdateStatementList) (arg2 : (_root_.List forUpdateStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List forUpdateStatementIR), SpecTecCall.ForUpdateStmtList_ok arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.ForUpdateStmtList_ok
scoped notation:50 x0:51 " |- " x1:51 " : " x2:51 => _root_.SpecTec.ForUpdateStmtList_ok x0 x1 x2
end Notation.ForUpdateStmtList_ok


noncomputable def «ForUpdateStmtList_ok:rule:iter:1» (arg0 : typingContext) (arg1 : (_root_.List forUpdateStatement)) (arg2 : (_root_.List forUpdateStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List forUpdateStatementIR), SpecTecCall.«ForUpdateStmtList_ok:rule:iter:1» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def ForInitStmt_ok (arg0 : typingContext) (arg1 : forInitStatement) (arg2 : typingContext) (arg3 : forInitStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × forInitStatementIR), SpecTecCall.ForInitStmt_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ForInitStmt_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForInitStmt_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ForInitStmt_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForInitStmt_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForInitStmt_ok] unexpandRelationNotation
end Notation.ForInitStmt_ok


noncomputable def ForInitStmts_ok (arg0 : typingContext) (arg1 : (_root_.List forInitStatement)) (arg2 : typingContext) (arg3 : (_root_.List forInitStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List forInitStatementIR)), SpecTecCall.ForInitStmts_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ForInitStmts_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForInitStmts_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ForInitStmts_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForInitStmts_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForInitStmts_ok] unexpandRelationNotation
end Notation.ForInitStmts_ok


noncomputable def ForInitStmtList_ok (arg0 : typingContext) (arg1 : forInitStatementList) (arg2 : typingContext) (arg3 : (_root_.List forInitStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List forInitStatementIR)), SpecTecCall.ForInitStmtList_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ForInitStmtList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForInitStmtList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ForInitStmtList_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForInitStmtList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForInitStmtList_ok] unexpandRelationNotation
end Notation.ForInitStmtList_ok


noncomputable def SwitchCase_table_ok (arg0 : typingContext) (arg1 : typeId) (arg2 : switchCase) (arg3 : typingContext) (arg4 : switchCaseIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × switchCaseIR), SpecTecCall.SwitchCase_table_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.SwitchCase_table_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchCase_table_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.SwitchCase_table_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchCase_table_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchCase_table_ok] unexpandRelationNotation
end Notation.SwitchCase_table_ok


noncomputable def SwitchCases_table_ok (arg0 : typingContext) (arg1 : typeId) (arg2 : (_root_.List switchCase)) (arg3 : typingContext) (arg4 : switchCaseListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × switchCaseListIR), SpecTecCall.SwitchCases_table_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.SwitchCases_table_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchCases_table_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.SwitchCases_table_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchCases_table_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchCases_table_ok] unexpandRelationNotation
end Notation.SwitchCases_table_ok


noncomputable def SwitchCaseList_table_ok (arg0 : typingContext) (arg1 : typeId) (arg2 : switchCaseList) (arg3 : typingContext) (arg4 : switchCaseListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × switchCaseListIR), SpecTecCall.SwitchCaseList_table_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.SwitchCaseList_table_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchCaseList_table_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.SwitchCaseList_table_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchCaseList_table_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchCaseList_table_ok] unexpandRelationNotation
end Notation.SwitchCaseList_table_ok


noncomputable def Switch_table_ok (arg0 : typingContext) (arg1 : id) (arg2 : switchCaseList) (arg3 : typingContext) (arg4 : (_root_.List switchCaseIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List switchCaseIR)), SpecTecCall.Switch_table_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.Switch_table_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[4]⟩, ⟨stx[7]⟩, ⟨stx[10]⟩, ⟨stx[11]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Switch_table_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Switch_table_ok.relationNotation
        #[x0, Lean.mkAtom "|-", Lean.mkAtom "SWITCH", Lean.mkAtom "(", x1, Lean.mkAtom ")", Lean.mkAtom "{", x2, Lean.mkAtom "}", Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " " SWITCH " " ( " term:51 " ) " " { " term:51 " } " " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Switch_table_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Switch_table_ok] unexpandRelationNotation
end Notation.Switch_table_ok


noncomputable def SwitchCase_general_ok (arg0 : typingContext) (arg1 : typeIR) (arg2 : switchCase) (arg3 : typingContext) (arg4 : switchCaseIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × switchCaseIR), SpecTecCall.SwitchCase_general_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.SwitchCase_general_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchCase_general_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.SwitchCase_general_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchCase_general_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchCase_general_ok] unexpandRelationNotation
end Notation.SwitchCase_general_ok


noncomputable def SwitchCases_general_ok (arg0 : typingContext) (arg1 : typeIR) (arg2 : (_root_.List switchCase)) (arg3 : typingContext) (arg4 : switchCaseListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × switchCaseListIR), SpecTecCall.SwitchCases_general_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.SwitchCases_general_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchCases_general_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.SwitchCases_general_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchCases_general_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchCases_general_ok] unexpandRelationNotation
end Notation.SwitchCases_general_ok


noncomputable def SwitchCaseList_general_ok (arg0 : typingContext) (arg1 : typeIR) (arg2 : switchCaseList) (arg3 : typingContext) (arg4 : switchCaseListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × switchCaseListIR), SpecTecCall.SwitchCaseList_general_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.SwitchCaseList_general_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchCaseList_general_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.SwitchCaseList_general_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchCaseList_general_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchCaseList_general_ok] unexpandRelationNotation
end Notation.SwitchCaseList_general_ok


noncomputable def Switch_general_ok (arg0 : typingContext) (arg1 : typedExpressionIR) (arg2 : switchCaseList) (arg3 : typingContext) (arg4 : (_root_.List switchCaseIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List switchCaseIR)), SpecTecCall.Switch_general_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.Switch_general_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[4]⟩, ⟨stx[7]⟩, ⟨stx[10]⟩, ⟨stx[11]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Switch_general_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Switch_general_ok.relationNotation
        #[x0, Lean.mkAtom "|-", Lean.mkAtom "SWITCH", Lean.mkAtom "(", x1, Lean.mkAtom ")", Lean.mkAtom "{", x2, Lean.mkAtom "}", Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " " SWITCH " " ( " term:51 " ) " " { " term:51 " } " " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Switch_general_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Switch_general_ok] unexpandRelationNotation
end Notation.Switch_general_ok

end SpecTec
