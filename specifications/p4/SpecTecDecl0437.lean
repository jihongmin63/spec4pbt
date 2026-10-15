import SpecTecDecl0436

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def InstDecl_inst (arg0 : cursor) (arg1 : instContext) (arg2 : store) (arg3 : instantiationIR) (arg4 : instContext) (arg5 : store) (arg6 : constantDeclarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × (store × constantDeclarationIR)), SpecTecCall.InstDecl_inst arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.InstDecl_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.InstDecl_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.InstDecl_inst.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.InstDecl_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.InstDecl_inst] unexpandRelationNotation
end Notation.InstDecl_inst


noncomputable def Copy_in_arg_inst (arg0 : store) (arg1 : cursor) (arg2 : instContext) (arg3 : argumentIR) (arg4 : cursor) (arg5 : instContext) (arg6 : id) (arg7 : store) (arg8 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × instContext), SpecTecCall.Copy_in_arg_inst arg0 arg1 arg2 arg3 arg4 arg5 arg6⟩) 0 (.success (.of ((arg7, arg8)))) finalSupply

namespace Notation.Copy_in_arg_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[9]⟩, ⟨stx[10]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_in_arg_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8) =>
      pure (.node .none `SpecTec.Notation.Copy_in_arg_inst.relationNotation
        #[x0, x1, x2, x3, Lean.mkAtom "@", x4, x5, x6, Lean.mkAtom "~>", x7, x8])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:arg ppSpace colGt term:arg " @ " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " ~> " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_in_arg_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_in_arg_inst] unexpandRelationNotation
end Notation.Copy_in_arg_inst


noncomputable def Copy_in_inst (arg0 : store) (arg1 : cursor) (arg2 : instContext) (arg3 : (_root_.List argumentIR)) (arg4 : cursor) (arg5 : instContext) (arg6 : (_root_.List id)) (arg7 : store) (arg8 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × instContext), SpecTecCall.Copy_in_inst arg0 arg1 arg2 arg3 arg4 arg5 arg6⟩) 0 (.success (.of ((arg7, arg8)))) finalSupply

namespace Notation.Copy_in_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[9]⟩, ⟨stx[10]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_in_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8) =>
      pure (.node .none `SpecTec.Notation.Copy_in_inst.relationNotation
        #[x0, x1, x2, x3, Lean.mkAtom "@", x4, x5, x6, Lean.mkAtom "~>", x7, x8])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:arg ppSpace colGt term:arg " @ " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " ~> " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_in_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_in_inst] unexpandRelationNotation
end Notation.Copy_in_inst


noncomputable def Copy_in_arg_inst_default (arg0 : store) (arg1 : cursor) (arg2 : instContext) (arg3 : cursor) (arg4 : instContext) (arg5 : parameterIR) (arg6 : store) (arg7 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × instContext), SpecTecCall.Copy_in_arg_inst_default arg0 arg1 arg2 arg3 arg4 arg5⟩) 0 (.success (.of ((arg6, arg7)))) finalSupply

namespace Notation.Copy_in_arg_inst_default
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_in_arg_inst_default arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.Copy_in_arg_inst_default.relationNotation
        #[x0, x1, x2, Lean.mkAtom "@", x3, x4, x5, Lean.mkAtom "~>", x6, x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:arg " @ " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " ~> " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_in_arg_inst_default.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_in_arg_inst_default] unexpandRelationNotation
end Notation.Copy_in_arg_inst_default


noncomputable def Copy_in_inst_default (arg0 : store) (arg1 : cursor) (arg2 : instContext) (arg3 : cursor) (arg4 : instContext) (arg5 : (_root_.List parameterIR)) (arg6 : store) (arg7 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × instContext), SpecTecCall.Copy_in_inst_default arg0 arg1 arg2 arg3 arg4 arg5⟩) 0 (.success (.of ((arg6, arg7)))) finalSupply

namespace Notation.Copy_in_inst_default
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_in_inst_default arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.Copy_in_inst_default.relationNotation
        #[x0, x1, x2, Lean.mkAtom "@", x3, x4, x5, Lean.mkAtom "~>", x6, x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:arg " @ " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " ~> " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_in_inst_default.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_in_inst_default] unexpandRelationNotation
end Notation.Copy_in_inst_default


noncomputable def Constructor_call (arg0 : cursor) (arg1 : instContext) (arg2 : store) (arg3 : constructorDef) (arg4 : typeArgumentListIR) (arg5 : argumentListIR) (arg6 : (_root_.List id)) (arg7 : (_root_.List id)) (arg8 : store) (arg9 : object) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × object), SpecTecCall.Constructor_call arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7⟩) 0 (.success (.of ((arg8, arg9)))) finalSupply

namespace Notation.Constructor_call
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[9]⟩, ⟨stx[11]⟩, ⟨stx[13]⟩, ⟨stx[16]⟩, ⟨stx[17]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Constructor_call arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9) =>
      pure (.node .none `SpecTec.Notation.Constructor_call.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom "<", x4, Lean.mkAtom ">", Lean.mkAtom "(", x5, Lean.mkAtom "#", x6, Lean.mkAtom "#", x7, Lean.mkAtom ")", Lean.mkAtom ":", x8, x9])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " < " term:51 " > " " ( " term:51 " # " term:51 " # " term:51 " ) " " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Constructor_call.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Constructor_call] unexpandRelationNotation
end Notation.Constructor_call


noncomputable def SwitchCase_inst (arg0 : cursor) (arg1 : instContext) (arg2 : store) (arg3 : switchCaseIR) (arg4 : store) (arg5 : switchCaseIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × switchCaseIR), SpecTecCall.SwitchCase_inst arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, arg5)))) finalSupply

namespace Notation.SwitchCase_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchCase_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.SwitchCase_inst.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchCase_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchCase_inst] unexpandRelationNotation
end Notation.SwitchCase_inst


noncomputable def SwitchCases_inst (arg0 : cursor) (arg1 : instContext) (arg2 : store) (arg3 : (_root_.List switchCaseIR)) (arg4 : store) (arg5 : (_root_.List switchCaseIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × (_root_.List switchCaseIR)), SpecTecCall.SwitchCases_inst arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, arg5)))) finalSupply

namespace Notation.SwitchCases_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchCases_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.SwitchCases_inst.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchCases_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchCases_inst] unexpandRelationNotation
end Notation.SwitchCases_inst


noncomputable def ObjectDecl_inst (arg0 : instContext) (arg1 : store) (arg2 : objectDeclarationIR) (arg3 : instContext) (arg4 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × store), SpecTecCall.ObjectDecl_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.ObjectDecl_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ObjectDecl_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.ObjectDecl_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ObjectDecl_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ObjectDecl_inst] unexpandRelationNotation
end Notation.ObjectDecl_inst


noncomputable def ObjectDecls_inst (arg0 : instContext) (arg1 : store) (arg2 : objectDeclarationListIR) (arg3 : instContext) (arg4 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × store), SpecTecCall.ObjectDecls_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.ObjectDecls_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ObjectDecls_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.ObjectDecls_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ObjectDecls_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ObjectDecls_inst] unexpandRelationNotation
end Notation.ObjectDecls_inst


noncomputable def Decl_inst (arg0 : instContext) (arg1 : store) (arg2 : declarationIR) (arg3 : instContext) (arg4 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × store), SpecTecCall.Decl_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.Decl_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Decl_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Decl_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Decl_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Decl_inst] unexpandRelationNotation
end Notation.Decl_inst


noncomputable def Decls_inst (arg0 : instContext) (arg1 : store) (arg2 : (_root_.List declarationIR)) (arg3 : instContext) (arg4 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(instContext × store), SpecTecCall.Decls_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.Decls_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Decls_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Decls_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Decls_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Decls_inst] unexpandRelationNotation
end Notation.Decls_inst


noncomputable def Program_inst (arg0 : p4program) (arg1 : globalInstLayer) (arg2 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(globalInstLayer × store), SpecTecCall.Program_inst arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

namespace Notation.Program_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Program_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2) =>
      pure (.node .none `SpecTec.Notation.Program_inst.relationNotation
        #[Lean.mkAtom "|-", x0, Lean.mkAtom ":", x1, x2])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Program_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Program_inst] unexpandRelationNotation
end Notation.Program_inst


noncomputable def «$match_keyset:case_3:iter:0» (arg0 : value) (arg1 : (_root_.List value)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_keyset:case_3:iter:0» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$match_keyset» (arg0 : setValue) (arg1 : value) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$match_keyset» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$match_keysets» (arg0 : (_root_.List setValue)) (arg1 : (_root_.List value)) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$match_keysets» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$values_of_setValue» (arg0 : setTypeIR) (arg1 : setValue) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$values_of_setValue» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$match_switchLabelIR_general» (arg0 : value) (arg1 : value) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$match_switchLabelIR_general» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def Expr_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : typedExpressionIR) (arg4 : evalContext) (arg5 : arch) (arg6 : expressionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × expressionResult)), SpecTecCall.Expr_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Expr_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Expr_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Expr_eval.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Expr_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Expr_eval] unexpandRelationNotation
end Notation.Expr_eval


noncomputable def Exprs_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : (_root_.List typedExpressionIR)) (arg4 : evalContext) (arg5 : arch) (arg6 : expressionListResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × expressionListResult)), SpecTecCall.Exprs_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Exprs_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Exprs_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Exprs_eval.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Exprs_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Exprs_eval] unexpandRelationNotation
end Notation.Exprs_eval


noncomputable def Eval_keyset (arg0 : evalContext) (arg1 : arch) (arg2 : keysetExpressionIR) (arg3 : evalContext) (arg4 : arch) (arg5 : keysetExpressionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × keysetExpressionResult)), SpecTecCall.Eval_keyset arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.Eval_keyset
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Eval_keyset arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Eval_keyset.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Eval_keyset.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Eval_keyset] unexpandRelationNotation
end Notation.Eval_keyset


noncomputable def Argument_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : argumentIR) (arg4 : evalContext) (arg5 : arch) (arg6 : expressionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × expressionResult)), SpecTecCall.Argument_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Argument_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Argument_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Argument_eval.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Argument_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Argument_eval] unexpandRelationNotation
end Notation.Argument_eval


noncomputable def Argument_eval_lvalue (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : argumentIR) (arg4 : evalContext) (arg5 : arch) (arg6 : storageReferenceResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × storageReferenceResult)), SpecTecCall.Argument_eval_lvalue arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Argument_eval_lvalue
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Argument_eval_lvalue arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Argument_eval_lvalue.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Argument_eval_lvalue.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Argument_eval_lvalue] unexpandRelationNotation
end Notation.Argument_eval_lvalue


noncomputable def Lvalue_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : typedLvalueIR) (arg4 : evalContext) (arg5 : arch) (arg6 : storageReferenceResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × storageReferenceResult)), SpecTecCall.Lvalue_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Lvalue_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Lvalue_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Lvalue_eval.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Lvalue_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Lvalue_eval] unexpandRelationNotation
end Notation.Lvalue_eval


noncomputable def Stmt_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : statementIR) (arg4 : evalContext) (arg5 : arch) (arg6 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.Stmt_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Stmt_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Stmt_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Stmt_eval.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Stmt_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Stmt_eval] unexpandRelationNotation
end Notation.Stmt_eval


noncomputable def BlockElementStmt_eval (arg0 : evalContext) (arg1 : arch) (arg2 : blockElementStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.BlockElementStmt_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.BlockElementStmt_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.BlockElementStmt_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.BlockElementStmt_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.BlockElementStmt_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.BlockElementStmt_eval] unexpandRelationNotation
end Notation.BlockElementStmt_eval


noncomputable def BlockElementStmtList_eval (arg0 : evalContext) (arg1 : arch) (arg2 : blockElementStatementListIR) (arg3 : evalContext) (arg4 : arch) (arg5 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.BlockElementStmtList_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.BlockElementStmtList_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.BlockElementStmtList_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.BlockElementStmtList_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.BlockElementStmtList_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.BlockElementStmtList_eval] unexpandRelationNotation
end Notation.BlockElementStmtList_eval


noncomputable def Block_eval (arg0 : evalContext) (arg1 : arch) (arg2 : blockStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.Block_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.Block_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Block_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Block_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Block_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Block_eval] unexpandRelationNotation
end Notation.Block_eval


noncomputable def ParserStmt_eval (arg0 : evalContext) (arg1 : arch) (arg2 : parserStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : parserStatementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × parserStatementResult)), SpecTecCall.ParserStmt_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserStmt_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserStmt_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserStmt_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserStmt_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserStmt_eval] unexpandRelationNotation
end Notation.ParserStmt_eval


noncomputable def ParserBlockElementStmt_eval (arg0 : evalContext) (arg1 : arch) (arg2 : parserBlockElementStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : parserStatementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × parserStatementResult)), SpecTecCall.ParserBlockElementStmt_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserBlockElementStmt_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlockElementStmt_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserBlockElementStmt_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlockElementStmt_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlockElementStmt_eval] unexpandRelationNotation
end Notation.ParserBlockElementStmt_eval


noncomputable def ParserBlockElementStmtList_eval (arg0 : evalContext) (arg1 : arch) (arg2 : parserBlockElementStatementListIR) (arg3 : evalContext) (arg4 : arch) (arg5 : parserStatementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × parserStatementResult)), SpecTecCall.ParserBlockElementStmtList_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserBlockElementStmtList_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlockElementStmtList_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserBlockElementStmtList_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlockElementStmtList_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlockElementStmtList_eval] unexpandRelationNotation
end Notation.ParserBlockElementStmtList_eval


noncomputable def ParserBlock_eval (arg0 : evalContext) (arg1 : arch) (arg2 : parserBlockStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : parserStatementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × parserStatementResult)), SpecTecCall.ParserBlock_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserBlock_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlock_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserBlock_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlock_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlock_eval] unexpandRelationNotation
end Notation.ParserBlock_eval

end SpecTec
