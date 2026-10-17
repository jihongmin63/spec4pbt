namespace SpecTec
open SpecTecExecution

def noPrimitives : PrimitiveRunner specTecExecutableProgram := .unavailable _

#guard (runEval specTecExecutableProgram noPrimitives 20
  (.call (SpecTecCall.Choose 7)) 0 == .done (.success 1) 0)
#guard (runEval specTecExecutableProgram noPrimitives 20
  (.call (SpecTecCall.Caller 7)) 0 == .done (.success 30) 0)
#guard (runEval specTecExecutableProgram noPrimitives 20
  (.call (SpecTecCall.Guarded 0)) 0 == .done (.success 10) 0)
#guard (runEval specTecExecutableProgram noPrimitives 20
  (.call (SpecTecCall.Guarded 2)) 0 == .done (.success 11) 0)

/-- info: true -/
#guard_msgs in
#eval runEval specTecExecutableProgram noPrimitives 20
  (.call (SpecTecCall.Caller 7)) 0 == .done (.success 30) 0

theorem caller_by_execution : Caller 7 30 :=
  ⟨0, runEval_sound specTecExecutableProgram noPrimitives 20
    (.call (SpecTecCall.Caller 7)) 0 (.success 30) 0 rfl⟩

end SpecTec
