import properties.wasm_module_ok.ReadyMatchHeaptypeVar

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyHeapMatchIndexed

open properties.wasm_module_ok.ReadyMatchHeaptypeIndex
open properties.wasm_module_ok.ValidatedMatchIndexFuel

/-- A pure finite result for the four indexed heap-type pair shapes. Other
shapes are handled by the base-type part of the matcher. -/
def indexedHeapMatch (c : SpecTec.context) :
    SpecTec.heaptype → SpecTec.heaptype → Option Bool
  | .DefHT dtP, .DefHT dtQ => indexedDefMatch c dtP dtQ
  | .VarHT (.StatX p), .DefHT dtQ =>
      (indexOfDeftype c.TYPES dtQ).map (matchIndex c p)
  | .DefHT dtP, .VarHT (.StatX q) =>
      (indexOfDeftype c.TYPES dtP).map (fun p => matchIndex c p q)
  | .VarHT (.StatX p), .VarHT (.StatX q) =>
      some (matchIndex c p q)
  | _, _ => none

theorem indexedHeapMatch_def_def
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    indexedHeapMatch c (.DefHT dtP) (.DefHT dtQ) =
      some (matchIndex c p q) := by
  exact indexedDefMatch_of_positions c p q start dtP dtQ
    hready hp hq hP hQ

theorem indexedHeapMatch_statx_def
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    indexedHeapMatch c (.VarHT (.StatX p)) (.DefHT dtQ) =
      some (matchIndex c p q) := by
  obtain ⟨q', hfound⟩ := indexOfDeftype_complete c.TYPES dtQ
    (List.mem_iff_getElem?.mpr ⟨q, hQ⟩)
  obtain ⟨hq', hQ', _⟩ :=
    indexOfDeftype_sound c.TYPES dtQ q' hfound
  have hsame := ready_match_index_same_values c p p q' q start
    dtP dtQ hready hp hp hq' hq hP hP hQ' hQ
  simp [indexedHeapMatch, hfound, hsame]

theorem indexedHeapMatch_def_statx
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    indexedHeapMatch c (.DefHT dtP) (.VarHT (.StatX q)) =
      some (matchIndex c p q) := by
  obtain ⟨p', hfound⟩ := indexOfDeftype_complete c.TYPES dtP
    (List.mem_iff_getElem?.mpr ⟨p, hP⟩)
  obtain ⟨hp', hP', _⟩ :=
    indexOfDeftype_sound c.TYPES dtP p' hfound
  have hsame := ready_match_index_same_values c p' p q q start
    dtP dtQ hready hp' hp hq hq hP' hP hQ hQ
  simp [indexedHeapMatch, hfound, hsame]

theorem indexedHeapMatch_statx_statx
    (c : SpecTec.context) (p q : Nat) :
    indexedHeapMatch c (.VarHT (.StatX p)) (.VarHT (.StatX q)) =
      some (matchIndex c p q) := rfl

theorem indexedHeapMatch_def_def_eval
    (c : SpecTec.context) (p q n : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.DefHT dtQ)⟩)
      n (.success (.of ((indexedHeapMatch c
        (.DefHT dtP) (.DefHT dtQ)).getD false))) n := by
  rw [indexedHeapMatch_def_def c p q n dtP dtQ hready hp hq hP hQ]
  exact ready_match_heaptype_def_pair_total
    c p q n dtP dtQ hready hp hq hP hQ

theorem indexedHeapMatch_statx_def_eval
    (c : SpecTec.context) (p q n : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
        (.VarHT (.StatX p)) (.DefHT dtQ)⟩)
      n (.success (.of ((indexedHeapMatch c
        (.VarHT (.StatX p)) (.DefHT dtQ)).getD false))) n := by
  rw [indexedHeapMatch_statx_def c p q n dtP dtQ hready hp hq hP hQ]
  exact ReadyMatchHeaptypeVar.ready_match_heaptype_statx_def_total
    c p q n dtP dtQ hready hp hq hP hQ

theorem indexedHeapMatch_def_statx_eval
    (c : SpecTec.context) (p q n : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.VarHT (.StatX q))⟩)
      n (.success (.of ((indexedHeapMatch c
        (.DefHT dtP) (.VarHT (.StatX q))).getD false))) n := by
  rw [indexedHeapMatch_def_statx c p q n dtP dtQ hready hp hq hP hQ]
  exact ReadyMatchHeaptypeVar.ready_match_heaptype_def_statx_total
    c p q n dtP dtQ hready hp hq hP hQ

theorem indexedHeapMatch_statx_statx_eval
    (c : SpecTec.context) (p q n : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
        (.VarHT (.StatX p)) (.VarHT (.StatX q))⟩)
      n (.success (.of ((indexedHeapMatch c
        (.VarHT (.StatX p)) (.VarHT (.StatX q))).getD false))) n := by
  rw [indexedHeapMatch_statx_statx]
  exact ReadyMatchHeaptypeVar.ready_match_heaptype_statx_statx_total
    c p q n dtP dtQ hready hp hq hP hQ

end properties.wasm_module_ok.ReadyHeapMatchIndexed
