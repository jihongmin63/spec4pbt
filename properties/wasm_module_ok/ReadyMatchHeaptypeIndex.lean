import properties.wasm_module_ok.ReadyMatchIndexResult
import properties.wasm_module_ok.ReadyMatchTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyMatchHeaptypeIndex

theorem ready_match_heaptype_def_pair_index_iff
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype) (result : Bool)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.DefHT dtQ)⟩)
      start (.success (.of result)) start ↔
    result = ValidatedMatchIndexFuel.matchIndex c p q := by
  have hbridge :
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
          (.DefHT dtP) (.DefHT dtQ)⟩)
        start (.success (.of result)) start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
        start (.success (.of result)) start := by
    constructor
    · intro hheap
      obtain ⟨r, hdeftype⟩ :=
        ReadyMatchTotal.ready_match_deftype_total
          c p q start dtP dtQ hready hp hq hP hQ
      have hheap' :=
        MatchHeaptypeBasic.match_heaptype_def_def_total_of_match_deftype
          c.TYPES dtP dtQ r start hdeftype
      have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
        intro request x y hp
        cases hp
      obtain ⟨hout, _⟩ :=
        SpecTecExecution.eval_deterministic hdet hheap hheap'
      cases hout
      exact hdeftype
    · intro hdeftype
      exact MatchHeaptypeBasic.match_heaptype_def_def_total_of_match_deftype
        c.TYPES dtP dtQ result start hdeftype
  exact hbridge.trans
    (ReadyMatchIndexResult.ready_match_index_result_iff
      c p q start dtP dtQ result hready hp hq hP hQ)

theorem ready_match_heaptype_def_pair_total
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.DefHT dtQ)⟩)
      start (.success (.of (ValidatedMatchIndexFuel.matchIndex c p q))) start := by
  exact (ready_match_heaptype_def_pair_index_iff
    c p q start dtP dtQ (ValidatedMatchIndexFuel.matchIndex c p q)
    hready hp hq hP hQ).2 rfl

theorem ready_match_index_same_values
    (c : SpecTec.context) (p₁ p₂ q₁ q₂ start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp₁ : p₁ < c.TYPES.length) (hp₂ : p₂ < c.TYPES.length)
    (hq₁ : q₁ < c.TYPES.length) (hq₂ : q₂ < c.TYPES.length)
    (hP₁ : c.TYPES[p₁]? = some dtP)
    (hP₂ : c.TYPES[p₂]? = some dtP)
    (hQ₁ : c.TYPES[q₁]? = some dtQ)
    (hQ₂ : c.TYPES[q₂]? = some dtQ) :
    ValidatedMatchIndexFuel.matchIndex c p₁ q₁ =
      ValidatedMatchIndexFuel.matchIndex c p₂ q₂ := by
  exact (ready_match_heaptype_def_pair_index_iff
    c p₂ q₂ start dtP dtQ
    (ValidatedMatchIndexFuel.matchIndex c p₁ q₁)
    hready hp₂ hq₂ hP₂ hQ₂).1
    (ready_match_heaptype_def_pair_total
      c p₁ q₁ start dtP dtQ hready hp₁ hq₁ hP₁ hQ₁)

def indexOfDeftype : List SpecTec.deftype → SpecTec.deftype → Option Nat
  | [], _ => none
  | x :: xs, dt =>
      if x = dt then some 0 else (indexOfDeftype xs dt).map Nat.succ

theorem indexOfDeftype_sound
    (xs : List SpecTec.deftype) (dt : SpecTec.deftype) (p : Nat)
    (h : indexOfDeftype xs dt = some p) :
    p < xs.length ∧ xs[p]? = some dt ∧
      ∀ k < p, xs[k]? ≠ some dt := by
  induction xs generalizing p with
  | nil => simp [indexOfDeftype] at h
  | cons x xs ih =>
      by_cases heq : x = dt
      · simp [indexOfDeftype, heq] at h
        subst p
        simp [heq]
      · simp [indexOfDeftype, heq] at h
        cases htail : indexOfDeftype xs dt with
        | none => simp [htail] at h
        | some q =>
            simp [htail] at h
            subst p
            obtain ⟨hq, hget, hfirst⟩ := ih q htail
            constructor
            · simp [hq]
            constructor
            · simpa using hget
            · intro k hk
              cases k with
              | zero => simp [heq]
              | succ k =>
                  have hkq : k < q := by omega
                  simpa using hfirst k hkq

theorem indexOfDeftype_complete
    (xs : List SpecTec.deftype) (dt : SpecTec.deftype)
    (hmem : dt ∈ xs) :
    ∃ p, indexOfDeftype xs dt = some p := by
  induction xs with
  | nil => simp at hmem
  | cons x xs ih =>
      by_cases heq : x = dt
      · exact ⟨0, by simp [indexOfDeftype, heq]⟩
      · have htail : dt ∈ xs := by
          simpa [Ne.symm heq] using hmem
        obtain ⟨p, hp⟩ := ih htail
        exact ⟨p + 1, by simp [indexOfDeftype, heq, hp]⟩

theorem indexOfDeftype_eq_some_iff
    (xs : List SpecTec.deftype) (dt : SpecTec.deftype) (p : Nat) :
    indexOfDeftype xs dt = some p ↔
      p < xs.length ∧ xs[p]? = some dt ∧
        ∀ k < p, xs[k]? ≠ some dt := by
  constructor
  · exact indexOfDeftype_sound xs dt p
  · intro ⟨hp, hget, hfirst⟩
    obtain ⟨p', hfound⟩ :=
      indexOfDeftype_complete xs dt
        (List.mem_iff_getElem?.mpr ⟨p, hget⟩)
    obtain ⟨hp', hget', hfirst'⟩ :=
      indexOfDeftype_sound xs dt p' hfound
    have hle : p ≤ p' := by
      by_contra hn
      exact (hfirst p' (by omega)) hget'
    have hge : p' ≤ p := by
      by_contra hn
      exact (hfirst' p (by omega)) hget
    have heq : p' = p := by omega
    simpa [heq] using hfound

def indexedDefMatch (c : SpecTec.context)
    (dtP dtQ : SpecTec.deftype) : Option Bool := do
  let p ← indexOfDeftype c.TYPES dtP
  let q ← indexOfDeftype c.TYPES dtQ
  pure (ValidatedMatchIndexFuel.matchIndex c p q)

theorem indexedDefMatch_of_positions
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    indexedDefMatch c dtP dtQ =
      some (ValidatedMatchIndexFuel.matchIndex c p q) := by
  obtain ⟨p', hP'⟩ :=
    indexOfDeftype_complete c.TYPES dtP
      (List.mem_iff_getElem?.mpr ⟨p, hP⟩)
  obtain ⟨q', hQ'⟩ :=
    indexOfDeftype_complete c.TYPES dtQ
      (List.mem_iff_getElem?.mpr ⟨q, hQ⟩)
  obtain ⟨hp', hlookupP', _⟩ :=
    indexOfDeftype_sound c.TYPES dtP p' hP'
  obtain ⟨hq', hlookupQ', _⟩ :=
    indexOfDeftype_sound c.TYPES dtQ q' hQ'
  have hsame := ready_match_index_same_values
    c p' p q' q start dtP dtQ hready
    hp' hp hq' hq hlookupP' hP hlookupQ' hQ
  simp [indexedDefMatch, hP', hQ', hsame]

theorem ready_match_heaptype_indexed_value_total
    (c : SpecTec.context) (dtP dtQ : SpecTec.deftype)
    (start : Nat) (result : Bool)
    (hready : CandidateTypeReady.Ready c)
    (hresult : indexedDefMatch c dtP dtQ = some result) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.DefHT dtQ)⟩)
      start (.success (.of result)) start := by
  unfold indexedDefMatch at hresult
  cases hp : indexOfDeftype c.TYPES dtP with
  | none => simp [hp] at hresult
  | some p =>
      cases hq : indexOfDeftype c.TYPES dtQ with
      | none => simp [hp, hq] at hresult
      | some q =>
          simp [hp, hq] at hresult
          obtain ⟨hpBound, hP, _⟩ :=
            indexOfDeftype_sound c.TYPES dtP p hp
          obtain ⟨hqBound, hQ, _⟩ :=
            indexOfDeftype_sound c.TYPES dtQ q hq
          cases hresult
          exact ready_match_heaptype_def_pair_total
            c p q start dtP dtQ hready hpBound hqBound hP hQ

theorem ready_match_heaptype_indexed_value_success_iff
    (c : SpecTec.context) (p q start finish : Nat)
    (dtP dtQ : SpecTec.deftype) (result : Bool)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.DefHT dtQ)⟩)
      start (.success (.of result)) finish ↔
    indexedDefMatch c dtP dtQ = some result ∧ finish = start := by
  constructor
  · intro heval
    have hknown := ready_match_heaptype_def_pair_total
      c p q start dtP dtQ hready hp hq hP hQ
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hx
      cases hx
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet heval hknown
    cases hout
    exact ⟨indexedDefMatch_of_positions c p q start dtP dtQ
      hready hp hq hP hQ, hsupply⟩
  · rintro ⟨hresult, hfinish⟩
    subst finish
    exact ready_match_heaptype_indexed_value_total
      c dtP dtQ start result hready hresult

end properties.wasm_module_ok.ReadyMatchHeaptypeIndex
