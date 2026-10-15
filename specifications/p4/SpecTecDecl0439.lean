import SpecTecDecl0438

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def TableMatch_eval (arg0 : evalContext) (arg1 : arch) (arg2 : (_root_.List tableKeyValue)) (arg3 : tableEntryIR) (arg4 : evalContext) (arg5 : arch) (arg6 : tableMatchResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × tableMatchResult)), SpecTecCall.TableMatch_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.TableMatch_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableMatch_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.TableMatch_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom "@", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg " @ " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableMatch_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableMatch_eval] unexpandRelationNotation
end Notation.TableMatch_eval


noncomputable def TableMatches_eval (arg0 : evalContext) (arg1 : arch) (arg2 : (_root_.List tableKeyValue)) (arg3 : tableEntryListIR) (arg4 : evalContext) (arg5 : arch) (arg6 : tableMatchesResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × tableMatchesResult)), SpecTecCall.TableMatches_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.TableMatches_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableMatches_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.TableMatches_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom "@", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg " @ " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableMatches_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableMatches_eval] unexpandRelationNotation
end Notation.TableMatches_eval


noncomputable def ActionBody_eval (arg0 : evalContext) (arg1 : arch) (arg2 : blockStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : actionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × actionResult)), SpecTecCall.ActionBody_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ActionBody_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ActionBody_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ActionBody_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ActionBody_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ActionBody_eval] unexpandRelationNotation
end Notation.ActionBody_eval


noncomputable def DefinedFunctionBody_eval (arg0 : evalContext) (arg1 : arch) (arg2 : blockStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : definedFunctionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × definedFunctionResult)), SpecTecCall.DefinedFunctionBody_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.DefinedFunctionBody_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.DefinedFunctionBody_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.DefinedFunctionBody_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.DefinedFunctionBody_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.DefinedFunctionBody_eval] unexpandRelationNotation
end Notation.DefinedFunctionBody_eval


noncomputable def Var_init (arg0 : evalContext) (arg1 : typeIR) (arg2 : nameIR) (arg3 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.Var_init arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.Var_init
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Var_init arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Var_init.relationNotation
        #[x0, Lean.mkAtom "|-", x1, x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:arg ppSpace colGt term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Var_init.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Var_init] unexpandRelationNotation
end Notation.Var_init


noncomputable def Extern_init (arg0 : evalContext) (arg1 : arch) (arg2 : nameIR) (arg3 : nameIR) (arg4 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨arch, SpecTecCall.Extern_init arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply

namespace Notation.Extern_init
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Extern_init arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Extern_init.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, Lean.mkAtom ":", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Extern_init.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Extern_init] unexpandRelationNotation
end Notation.Extern_init


noncomputable def Program_init (arg0 : p4program) (arg1 : evalContext) (arg2 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × store), SpecTecCall.Program_init arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

namespace Notation.Program_init
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Program_init arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2) =>
      pure (.node .none `SpecTec.Notation.Program_init.relationNotation
        #[Lean.mkAtom "|-", x0, Lean.mkAtom ":", x1, x2])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Program_init.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Program_init] unexpandRelationNotation
end Notation.Program_init


noncomputable def V1Model_init (arg0 : p4program) (arg1 : evalContext) (arg2 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.V1Model_init arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

namespace Notation.V1Model_init
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_init arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2) =>
      pure (.node .none `SpecTec.Notation.V1Model_init.relationNotation
        #[Lean.mkAtom "|-", x0, Lean.mkAtom ":", x1, x2])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_init.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_init] unexpandRelationNotation
end Notation.V1Model_init


noncomputable def V1Model_init_packet_in (arg0 : evalContext) (arg1 : arch) (arg2 : objectState) (arg3 : evalContext) (arg4 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.V1Model_init_packet_in arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.V1Model_init_packet_in
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_init_packet_in arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.V1Model_init_packet_in.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_init_packet_in.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_init_packet_in] unexpandRelationNotation
end Notation.V1Model_init_packet_in


noncomputable def V1Model_init_packet_out (arg0 : evalContext) (arg1 : arch) (arg2 : objectState) (arg3 : evalContext) (arg4 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.V1Model_init_packet_out arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.V1Model_init_packet_out
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_init_packet_out arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.V1Model_init_packet_out.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_init_packet_out.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_init_packet_out] unexpandRelationNotation
end Notation.V1Model_init_packet_out


noncomputable def V1Model_init_globals (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.V1Model_init_globals arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.V1Model_init_globals
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_init_globals arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.V1Model_init_globals.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_init_globals.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_init_globals] unexpandRelationNotation
end Notation.V1Model_init_globals


noncomputable def V1Model_parser (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : transitionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × transitionResult)), SpecTecCall.V1Model_parser arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.V1Model_parser
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_parser arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.V1Model_parser.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_parser.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_parser] unexpandRelationNotation
end Notation.V1Model_parser


noncomputable def V1Model_verify (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.V1Model_verify arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.V1Model_verify
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_verify arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.V1Model_verify.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_verify.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_verify] unexpandRelationNotation
end Notation.V1Model_verify


noncomputable def V1Model_ingress (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.V1Model_ingress arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.V1Model_ingress
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_ingress arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.V1Model_ingress.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_ingress.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_ingress] unexpandRelationNotation
end Notation.V1Model_ingress


noncomputable def V1Model_egress (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.V1Model_egress arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.V1Model_egress
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_egress arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.V1Model_egress.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_egress.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_egress] unexpandRelationNotation
end Notation.V1Model_egress


noncomputable def V1Model_check (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.V1Model_check arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.V1Model_check
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_check arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.V1Model_check.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_check.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_check] unexpandRelationNotation
end Notation.V1Model_check


noncomputable def V1Model_deparse (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.V1Model_deparse arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.V1Model_deparse
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_deparse arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.V1Model_deparse.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_deparse.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_deparse] unexpandRelationNotation
end Notation.V1Model_deparse


noncomputable def «$field_list_annotation_index» (arg0 : annotationList) (arg1 : (_root_.Option integerLiteral)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option integerLiteral), SpecTecCall.«$field_list_annotation_index» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$field_has_field_list_index» (arg0 : fieldTypeIR) (arg1 : integerLiteral) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$field_has_field_list_index» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$fields_with_field_list_index» (arg0 : (_root_.List fieldTypeIR)) (arg1 : integerLiteral) (arg2 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$fields_with_field_list_index» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$V1Model_meta_fields_of_index» (arg0 : arch) (arg1 : integerLiteral) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«$V1Model_meta_fields_of_index» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def V1Model_setup_preserved_meta_fields (arg0 : evalContext) (arg1 : arch) (arg2 : integerLiteral) (arg3 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.V1Model_setup_preserved_meta_fields arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.V1Model_setup_preserved_meta_fields
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.V1Model_setup_preserved_meta_fields arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.V1Model_setup_preserved_meta_fields.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.V1Model_setup_preserved_meta_fields.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.V1Model_setup_preserved_meta_fields] unexpandRelationNotation
end Notation.V1Model_setup_preserved_meta_fields


noncomputable def EBPF_init (arg0 : p4program) (arg1 : evalContext) (arg2 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.EBPF_init arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

namespace Notation.EBPF_init
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.EBPF_init arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2) =>
      pure (.node .none `SpecTec.Notation.EBPF_init.relationNotation
        #[Lean.mkAtom "|-", x0, Lean.mkAtom ":", x1, x2])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.EBPF_init.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.EBPF_init] unexpandRelationNotation
end Notation.EBPF_init


noncomputable def EBPF_init_packet_in (arg0 : evalContext) (arg1 : arch) (arg2 : objectState) (arg3 : evalContext) (arg4 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.EBPF_init_packet_in arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.EBPF_init_packet_in
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.EBPF_init_packet_in arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.EBPF_init_packet_in.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.EBPF_init_packet_in.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.EBPF_init_packet_in] unexpandRelationNotation
end Notation.EBPF_init_packet_in


noncomputable def EBPF_init_globals (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.EBPF_init_globals arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.EBPF_init_globals
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.EBPF_init_globals arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2) =>
      pure (.node .none `SpecTec.Notation.EBPF_init_globals.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 : term
attribute [scoped macro SpecTec.Notation.EBPF_init_globals.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.EBPF_init_globals] unexpandRelationNotation
end Notation.EBPF_init_globals


noncomputable def EBPF_parse (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : transitionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × transitionResult)), SpecTecCall.EBPF_parse arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.EBPF_parse
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.EBPF_parse arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.EBPF_parse.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.EBPF_parse.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.EBPF_parse] unexpandRelationNotation
end Notation.EBPF_parse


noncomputable def EBPF_filter (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.EBPF_filter arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.EBPF_filter
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.EBPF_filter arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.EBPF_filter.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.EBPF_filter.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.EBPF_filter] unexpandRelationNotation
end Notation.EBPF_filter


noncomputable def PSA_init (arg0 : p4program) (arg1 : evalContext) (arg2 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.PSA_init arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

namespace Notation.PSA_init
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_init arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2) =>
      pure (.node .none `SpecTec.Notation.PSA_init.relationNotation
        #[Lean.mkAtom "|-", x0, Lean.mkAtom ":", x1, x2])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_init.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_init] unexpandRelationNotation
end Notation.PSA_init


noncomputable def PSA_ingress_init_packet_in (arg0 : evalContext) (arg1 : arch) (arg2 : objectState) (arg3 : evalContext) (arg4 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.PSA_ingress_init_packet_in arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.PSA_ingress_init_packet_in
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress_init_packet_in arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress_init_packet_in.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress_init_packet_in.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress_init_packet_in] unexpandRelationNotation
end Notation.PSA_ingress_init_packet_in


noncomputable def PSA_ingress_init_packet_out (arg0 : evalContext) (arg1 : arch) (arg2 : objectState) (arg3 : evalContext) (arg4 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.PSA_ingress_init_packet_out arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.PSA_ingress_init_packet_out
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress_init_packet_out arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress_init_packet_out.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress_init_packet_out.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress_init_packet_out] unexpandRelationNotation
end Notation.PSA_ingress_init_packet_out


noncomputable def PSA_ingress_init_globals (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_ingress_init_globals arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.PSA_ingress_init_globals
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress_init_globals arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress_init_globals.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress_init_globals.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress_init_globals] unexpandRelationNotation
end Notation.PSA_ingress_init_globals


noncomputable def PSA_ingress_parser (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : transitionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × transitionResult)), SpecTecCall.PSA_ingress_parser arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.PSA_ingress_parser
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress_parser arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress_parser.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress_parser.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress_parser] unexpandRelationNotation
end Notation.PSA_ingress_parser

end SpecTec
