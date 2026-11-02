import properties.wasm_module_ok.ReadyMatchHeaptypeIndex
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyMatchHeaptypeVar

theorem ready_match_heaptype_statx_def_total
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.VarHT (.StatX p)) (.DefHT dtQ)⟩)
      start (.success (.of (ValidatedMatchIndexFuel.matchIndex c p q))) start := by
  apply MatchHeaptypeBasic.match_heaptype_statx_total_of_def
    c.TYPES p dtP (.DefHT dtQ)
      (ValidatedMatchIndexFuel.matchIndex c p q) start hP
  exact ReadyMatchHeaptypeIndex.ready_match_heaptype_def_pair_total
    c p q start dtP dtQ hready hp hq hP hQ

theorem ready_match_heaptype_def_statx_total
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.VarHT (.StatX q))⟩)
      start (.success (.of (ValidatedMatchIndexFuel.matchIndex c p q))) start := by
  apply MatchHeaptypeBasic.match_heaptype_def_statx_total_of_defs
    c.TYPES q dtP dtQ
      (ValidatedMatchIndexFuel.matchIndex c p q) start hQ
  exact ReadyMatchHeaptypeIndex.ready_match_heaptype_def_pair_total
    c p q start dtP dtQ hready hp hq hP hQ

theorem ready_match_heaptype_statx_statx_total
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.VarHT (.StatX p)) (.VarHT (.StatX q))⟩)
      start (.success (.of (ValidatedMatchIndexFuel.matchIndex c p q))) start := by
  apply MatchHeaptypeBasic.match_heaptype_statx_total_of_def
    c.TYPES p dtP (.VarHT (.StatX q))
      (ValidatedMatchIndexFuel.matchIndex c p q) start hP
  exact ready_match_heaptype_def_statx_total
    c p q start dtP dtQ hready hp hq hP hQ

theorem ready_match_heaptype_statx_def_success_iff
    (c : SpecTec.context) (p q start finish : Nat)
    (dtP dtQ : SpecTec.deftype) (result : Bool)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.VarHT (.StatX p)) (.DefHT dtQ)⟩)
      start (.success (.of result)) finish ↔
    result = ValidatedMatchIndexFuel.matchIndex c p q ∧ finish = start := by
  constructor
  · intro heval
    have hknown := ready_match_heaptype_statx_def_total
      c p q start dtP dtQ hready hp hq hP hQ
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic heval hknown
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨hresult, hfinish⟩
    subst result
    subst finish
    exact ready_match_heaptype_statx_def_total
      c p q start dtP dtQ hready hp hq hP hQ

theorem ready_match_heaptype_def_statx_success_iff
    (c : SpecTec.context) (p q start finish : Nat)
    (dtP dtQ : SpecTec.deftype) (result : Bool)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.VarHT (.StatX q))⟩)
      start (.success (.of result)) finish ↔
    result = ValidatedMatchIndexFuel.matchIndex c p q ∧ finish = start := by
  constructor
  · intro heval
    have hknown := ready_match_heaptype_def_statx_total
      c p q start dtP dtQ hready hp hq hP hQ
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic heval hknown
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨hresult, hfinish⟩
    subst result
    subst finish
    exact ready_match_heaptype_def_statx_total
      c p q start dtP dtQ hready hp hq hP hQ

theorem ready_match_heaptype_statx_statx_success_iff
    (c : SpecTec.context) (p q start finish : Nat)
    (dtP dtQ : SpecTec.deftype) (result : Bool)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.VarHT (.StatX p)) (.VarHT (.StatX q))⟩)
      start (.success (.of result)) finish ↔
    result = ValidatedMatchIndexFuel.matchIndex c p q ∧ finish = start := by
  constructor
  · intro heval
    have hknown := ready_match_heaptype_statx_statx_total
      c p q start dtP dtQ hready hp hq hP hQ
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic heval hknown
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨hresult, hfinish⟩
    subst result
    subst finish
    exact ready_match_heaptype_statx_statx_total
      c p q start dtP dtQ hready hp hq hP hQ

end properties.wasm_module_ok.ReadyMatchHeaptypeVar
