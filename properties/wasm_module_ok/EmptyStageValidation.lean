import properties.wasm_module_ok.bundle.Helpers
import properties.wasm_module_ok.StartValidation
import properties.wasm_module_ok.FuncsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.EmptyStageValidation

theorem types_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Types_ok c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Types_ok_clauses c []))
    n (.success (.of c)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Types_ok:clause:0» c []) n .unmatch n
    unfold SpecTec.«Types_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Types_ok:clause:1» c []) n (.success (.of c)) n
  unfold SpecTec.«Types_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  exact SpecTecExecution.Eval.pure c

theorem imports_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Imports_ok c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Imports_ok_clauses c []))
    n (.success (.of c)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Imports_ok:clause:0» c []) n .unmatch n
    unfold SpecTec.«Imports_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Imports_ok:clause:1» c []) n (.success (.of c)) n
  unfold SpecTec.«Imports_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  exact SpecTecExecution.Eval.pure c

theorem tables_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tables_ok c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Tables_ok_clauses c []))
    n (.success (.of c)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Tables_ok:clause:0» c []) n .unmatch n
    unfold SpecTec.«Tables_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Tables_ok:clause:1» c []) n (.success (.of c)) n
  unfold SpecTec.«Tables_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  exact SpecTecExecution.Eval.pure c

theorem mems_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Mems_ok c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Mems_ok_clauses c []))
    n (.success (.of c)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Mems_ok:clause:0» c []) n .unmatch n
    unfold SpecTec.«Mems_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Mems_ok:clause:1» c []) n (.success (.of c)) n
  unfold SpecTec.«Mems_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  exact SpecTecExecution.Eval.pure c

theorem globals_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Globals_ok c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Globals_ok_clauses c []))
    n (.success (.of c)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Globals_ok:clause:0» c []) n .unmatch n
    unfold SpecTec.«Globals_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Globals_ok:clause:1» c []) n (.success (.of c)) n
  unfold SpecTec.«Globals_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  exact SpecTecExecution.Eval.pure c

theorem tags_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tags_ok c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Tags_ok_clauses c []))
    n (.success (.of c)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Tags_ok:clause:0» c []) n .unmatch n
    unfold SpecTec.«Tags_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Tags_ok:clause:1» c []) n (.success (.of c)) n
  unfold SpecTec.«Tags_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  exact SpecTecExecution.Eval.pure c

theorem elems_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Elems_ok c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Elems_ok_clauses c []))
    n (.success (.of c)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Elems_ok:clause:0» c []) n .unmatch n
    unfold SpecTec.«Elems_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Elems_ok:clause:1» c []) n (.success (.of c)) n
  unfold SpecTec.«Elems_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  exact SpecTecExecution.Eval.pure c

theorem datas_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Datas_ok c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Datas_ok_clauses c []))
    n (.success (.of c)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Datas_ok:clause:0» c []) n .unmatch n
    unfold SpecTec.«Datas_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Datas_ok:clause:1» c []) n (.success (.of c)) n
  unfold SpecTec.«Datas_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  exact SpecTecExecution.Eval.pure c

theorem exports_nil_total
    (c : SpecTec.context) (names : SpecTec.nameset) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.nameset,
        SpecTec.Call.Exports_ok c names []⟩)
      n (.success (.of names)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.Exports_ok_clauses c names []))
    n (.success (.of names)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Exports_ok:clause:0» c names []) n .unmatch n
    unfold SpecTec.«Exports_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Exports_ok:clause:1» c names [])
    n (.success (.of names)) n
  unfold SpecTec.«Exports_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  exact SpecTecExecution.Eval.pure names

end properties.wasm_module_ok.EmptyStageValidation
