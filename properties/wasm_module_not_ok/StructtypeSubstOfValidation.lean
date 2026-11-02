import properties.wasm_module_not_ok.FieldtypeSubstOfValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substFieldtypeListResult (ts : List SpecTec.fieldtype)
    (dts : List SpecTec.deftype) : Option (List SpecTec.fieldtype) :=
  match ts with
  | [] => some []
  | t :: tail => do
      let t' ← substFieldtypeResult t dts
      let tail' ← substFieldtypeListResult tail dts
      pure (t' :: tail')

theorem subst_structtype_iter_of_total (ts : List SpecTec.fieldtype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.fieldtype,
        SpecTec.Call.«$subst_structtype:case_1:iter:0»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ts⟩)
      start (optionOutcome (substFieldtypeListResult ts dts)) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_structtype:case_1:iter:0_clauses»
            (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» []))
        start (optionOutcome (substFieldtypeListResult [] dts)) start
      simp only [substFieldtypeListResult, optionOutcome]
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» [])
        start (.success (.of ([] : List SpecTec.fieldtype))) start
      simpa [SpecTec.«$subst_structtype:case_1:iter:0:clause:0»] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.fieldtype) (n := start))
  | cons t tail ih =>
      cases hhead : substFieldtypeResult t dts with
      | none =>
          have hv : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.fieldtype,
                SpecTec.Call.«$subst_fieldtype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» t⟩)
              start .unmatch start := by
            simpa [optionOutcome, hhead] using subst_fieldtype_of_total t dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«$subst_structtype:case_1:iter:0_clauses»
                (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» (t :: tail)))
            start (optionOutcome (substFieldtypeListResult (t :: tail) dts)) start
          simp only [substFieldtypeListResult, hhead, Option.bind, optionOutcome]
          apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
                (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» (t :: tail))
              start .unmatch start
            unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
            exact SpecTecExecution.Eval.unmatch
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.Body
                (SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» (t :: tail))
                start .unmatch start
              unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
              exact SpecTecExecution.Eval.bind_unmatch hv
            · exact SpecTecExecution.tryClauses_nil start
      | some t' =>
          have hv : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.fieldtype,
                SpecTec.Call.«$subst_fieldtype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» t⟩)
              start (.success (.of t')) start := by
            simpa [optionOutcome, hhead] using subst_fieldtype_of_total t dts start
          cases htail : substFieldtypeListResult tail dts with
          | none =>
              have ht : SpecTecExecution.Eval SpecTec.Body
                  (.call ⟨List SpecTec.fieldtype,
                    SpecTec.Call.«$subst_structtype:case_1:iter:0»
                      (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» tail⟩)
                  start .unmatch start := by
                simpa [optionOutcome, htail] using ih
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.Body
                (SpecTecExecution.tryClauses
                  (SpecTec.«$subst_structtype:case_1:iter:0_clauses»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail)))
                start (optionOutcome (substFieldtypeListResult (t :: tail) dts)) start
              simp only [substFieldtypeListResult, hhead, Option.bind, htail, optionOutcome]
              apply SpecTecExecution.tryClauses_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.Body
                  (SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail)) start .unmatch start
                unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
                exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.tryClauses_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.Body
                    (SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
                      (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                      (t :: tail)) start .unmatch start
                  unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
                  apply SpecTecExecution.Eval.bind_success hv
                  exact SpecTecExecution.Eval.bind_unmatch ht
                · exact SpecTecExecution.tryClauses_nil start
          | some tail' =>
              have ht : SpecTecExecution.Eval SpecTec.Body
                  (.call ⟨List SpecTec.fieldtype,
                    SpecTec.Call.«$subst_structtype:case_1:iter:0»
                      (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» tail⟩)
                  start (.success (.of tail')) start := by
                simpa [optionOutcome, htail] using ih
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.Body
                (SpecTecExecution.tryClauses
                  (SpecTec.«$subst_structtype:case_1:iter:0_clauses»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail)))
                start (optionOutcome (substFieldtypeListResult (t :: tail) dts)) start
              simp [substFieldtypeListResult, hhead, htail, optionOutcome]
              apply SpecTecExecution.tryClauses_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.Body
                  (SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail)) start .unmatch start
                unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
                exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.tryClauses_cons_success
                change SpecTecExecution.Eval SpecTec.Body
                  (SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail))
                  start (.success (.of (t' :: tail'))) start
                unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
                apply SpecTecExecution.Eval.bind_success hv
                apply SpecTecExecution.Eval.bind_success ht
                exact SpecTecExecution.Eval.pure (t' :: tail')

def substStructtypeResult (st : SpecTec.structtype)
    (dts : List SpecTec.deftype) : Option SpecTec.structtype :=
  match st with
  | .StructT fields => (substFieldtypeListResult fields dts).map SpecTec.structtype.StructT

theorem subst_structtype_of_total (st : SpecTec.structtype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.structtype,
        SpecTec.Call.«$subst_structtype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» st⟩)
      start (optionOutcome (substStructtypeResult st dts)) start := by
  cases st with
  | StructT fields =>
      cases hresult : substFieldtypeListResult fields dts with
      | some fields' =>
          have hiter : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨List SpecTec.fieldtype,
                SpecTec.Call.«$subst_structtype:case_1:iter:0»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» fields⟩)
              start (.success (.of fields')) start := by
            simpa [optionOutcome, hresult] using
              subst_structtype_iter_of_total fields dts start
          simp only [substStructtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«$subst_structtype_clauses» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.StructT fields)))
            start (.success (.of (SpecTec.structtype.StructT fields'))) start
          apply SpecTecExecution.tryClauses_cons_success
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$subst_structtype:clause:0» (List SpecTec.deftype) dts
              SpecTec.Call.«$subst_of» (.StructT fields))
            start (.success (.of (SpecTec.structtype.StructT fields'))) start
          unfold SpecTec.«$subst_structtype:clause:0»
          apply SpecTecExecution.Eval.bind_success hiter
          exact SpecTecExecution.Eval.pure (SpecTec.structtype.StructT fields')
      | none =>
          have hiter : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨List SpecTec.fieldtype,
                SpecTec.Call.«$subst_structtype:case_1:iter:0»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» fields⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using
              subst_structtype_iter_of_total fields dts start
          simp only [substStructtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«$subst_structtype_clauses» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.StructT fields)))
            start .unmatch start
          apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«$subst_structtype:clause:0» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.StructT fields)) start .unmatch start
            unfold SpecTec.«$subst_structtype:clause:0»
            exact SpecTecExecution.Eval.bind_unmatch hiter
          · exact SpecTecExecution.tryClauses_nil start

theorem subst_structtype_of_deterministic (st : SpecTec.structtype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.structtype,
        SpecTec.Call.«$subst_structtype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» st⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substStructtypeResult st dts) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_structtype_of_total st dts start)

end properties.wasm_module_not_ok.Rejection
