import properties.wasm_module_ok.ReadyHeapMatchBase
import properties.wasm_module_ok.ReadyHeapMatchSpecialIndexed
import properties.wasm_module_ok.ReadyHeapMatchIndexed

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyHeapMatch

open properties.wasm_module_ok.ReadyMatchHeaptypeIndex

/-- A definition or static index in the ready type table. Invalid forms have
no result, so the executable classifier remains a partial function. -/
def indexedValue (c : SpecTec.context) : SpecTec.heaptype → Option SpecTec.deftype
  | .DefHT dt => (indexOfDeftype c.TYPES dt).map (fun _ => dt)
  | .VarHT (.StatX p) => c.TYPES[p]?
  | _ => none

theorem indexedValue_def_of_lookup
    (c : SpecTec.context) (p : Nat) (dt : SpecTec.deftype)
    (hlookup : c.TYPES[p]? = some dt) :
    indexedValue c (.DefHT dt) = some dt := by
  obtain ⟨q, hfound⟩ :=
    indexOfDeftype_complete c.TYPES dt
      (List.mem_iff_getElem?.mpr ⟨p, hlookup⟩)
  simp [indexedValue, hfound]

theorem indexedValue_statx_of_lookup
    (c : SpecTec.context) (p : Nat) (dt : SpecTec.deftype)
    (hlookup : c.TYPES[p]? = some dt) :
    indexedValue c (.VarHT (.StatX p)) = some dt := by
  exact hlookup

def baseIndexedMatch (source : SpecTec.heaptype) (dt : SpecTec.deftype) :
    Option Bool :=
  if source ∈ ReadyHeapMatchSpecialIndexed.specialBaseSources then
    some (ReadyHeapMatchSpecialIndexed.specialBaseMatch dt source)
  else if source ∈ MatchBaseDefTotal.simpleBaseHeaptypes then
    some (ReadyHeapMatchSimpleBase.simpleBaseMatch source (.DefHT dt))
  else none

theorem baseIndexedMatch_of_base
    (source : SpecTec.heaptype) (dt : SpecTec.deftype)
    (hbase : source ∈ HeaptypeValidation.baseHeaptypes) :
    baseIndexedMatch source dt =
      some ((baseIndexedMatch source dt).getD false) := by
  simp [HeaptypeValidation.baseHeaptypes] at hbase
  rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [baseIndexedMatch,
    ReadyHeapMatchSpecialIndexed.specialBaseSources,
    MatchBaseDefTotal.simpleBaseHeaptypes]

private theorem simple_of_base_not_special
    (source : SpecTec.heaptype)
    (hbase : source ∈ HeaptypeValidation.baseHeaptypes)
    (hnot : source ∉ ReadyHeapMatchSpecialIndexed.specialBaseSources) :
    source ∈ MatchBaseDefTotal.simpleBaseHeaptypes := by
  simp [HeaptypeValidation.baseHeaptypes] at hbase
  rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [ReadyHeapMatchSpecialIndexed.specialBaseSources,
    MatchBaseDefTotal.simpleBaseHeaptypes]

private theorem simpleBaseMatch_indexed_eq
    (source : SpecTec.heaptype) (p : Nat) (dt : SpecTec.deftype)
    (hsimple : source ∈ MatchBaseDefTotal.simpleBaseHeaptypes) :
    ReadyHeapMatchSimpleBase.simpleBaseMatch source (.VarHT (.StatX p)) =
      ReadyHeapMatchSimpleBase.simpleBaseMatch source (.DefHT dt) := by
  simp [MatchBaseDefTotal.simpleBaseHeaptypes] at hsimple
  rcases hsimple with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ReadyHeapMatchSimpleBase.simpleBaseMatch]

theorem baseIndexedMatch_def_eval
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (source : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : source ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES source (.DefHT dt)⟩)
      n (.success (.of ((baseIndexedMatch source dt).getD false))) n := by
  by_cases hspecial :
      source ∈ ReadyHeapMatchSpecialIndexed.specialBaseSources
  · simpa [baseIndexedMatch, hspecial] using
      (ReadyHeapMatchSpecialIndexed.special_base_def_result
        c p n dt source hready hlookup hspecial)
  · have hsimple := simple_of_base_not_special source hbase hspecial
    simpa [baseIndexedMatch, hspecial, hsimple] using
      (ReadyHeapMatchSimpleBase.simpleBaseMatch_eval
        c.TYPES source (.DefHT dt) n hsimple)

theorem baseIndexedMatch_statx_eval
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (source : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : source ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES source (.VarHT (.StatX p))⟩)
      n (.success (.of ((baseIndexedMatch source dt).getD false))) n := by
  by_cases hspecial :
      source ∈ ReadyHeapMatchSpecialIndexed.specialBaseSources
  · simpa [baseIndexedMatch, hspecial] using
      (ReadyHeapMatchSpecialIndexed.special_base_statx_result
        c p n dt source hready hlookup hspecial)
  · have hsimple := simple_of_base_not_special source hbase hspecial
    simpa [baseIndexedMatch, hspecial, hsimple,
      simpleBaseMatch_indexed_eq source p dt hsimple] using
      (ReadyHeapMatchSimpleBase.simpleBaseMatch_eval
        c.TYPES source (.VarHT (.StatX p)) n hsimple)

/-- Combine the proven finite heap matching cases without proof-only choice.
The result is defined on the base and ready indexed pairs needed by structural
matching; other pairs remain unsupported. -/
def readyHeapMatch (c : SpecTec.context)
    (source target : SpecTec.heaptype) : Option Bool :=
  if source ∈ HeaptypeValidation.baseHeaptypes then
    if target ∈ HeaptypeValidation.baseHeaptypes then
      some (ReadyHeapMatchBase.baseMatch source target)
    else
      (indexedValue c target).bind (baseIndexedMatch source)
  else if target ∈ HeaptypeValidation.baseHeaptypes then
    (indexedValue c source).map
      (fun dt => ReadyHeapMatchDefBase.readyDefBaseMatch dt target)
  else
    ReadyHeapMatchIndexed.indexedHeapMatch c source target

theorem readyHeapMatch_base_base
    (c : SpecTec.context) (source target : SpecTec.heaptype)
    (hsource : source ∈ HeaptypeValidation.baseHeaptypes)
    (htarget : target ∈ HeaptypeValidation.baseHeaptypes) :
    readyHeapMatch c source target =
      some (ReadyHeapMatchBase.baseMatch source target) := by
  simp [readyHeapMatch, hsource, htarget]

theorem readyHeapMatch_base_base_eval
    (c : SpecTec.context) (source target : SpecTec.heaptype)
    (n : Nat)
    (hsource : source ∈ HeaptypeValidation.baseHeaptypes)
    (htarget : target ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES source target⟩)
      n (.success (.of ((readyHeapMatch c source target).getD false))) n := by
  rw [readyHeapMatch_base_base c source target hsource htarget]
  exact ReadyHeapMatchBase.baseMatch_eval
    c.TYPES source target n hsource htarget

theorem readyHeapMatch_base_def
    (c : SpecTec.context) (p : Nat) (dt : SpecTec.deftype)
    (source : SpecTec.heaptype)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : source ∈ HeaptypeValidation.baseHeaptypes) :
    readyHeapMatch c source (.DefHT dt) =
      some ((baseIndexedMatch source dt).getD false) := by
  have htarget :
      (SpecTec.heaptype.DefHT dt) ∉ HeaptypeValidation.baseHeaptypes := by
    simp [HeaptypeValidation.baseHeaptypes]
  unfold readyHeapMatch
  rw [if_pos hbase, if_neg htarget,
    indexedValue_def_of_lookup c p dt hlookup]
  simpa using baseIndexedMatch_of_base source dt hbase

theorem readyHeapMatch_base_statx
    (c : SpecTec.context) (p : Nat) (dt : SpecTec.deftype)
    (source : SpecTec.heaptype)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : source ∈ HeaptypeValidation.baseHeaptypes) :
    readyHeapMatch c source (.VarHT (.StatX p)) =
      some ((baseIndexedMatch source dt).getD false) := by
  have htarget :
      (SpecTec.heaptype.VarHT (.StatX p)) ∉
        HeaptypeValidation.baseHeaptypes := by
    simp [HeaptypeValidation.baseHeaptypes]
  unfold readyHeapMatch
  rw [if_pos hbase, if_neg htarget,
    indexedValue_statx_of_lookup c p dt hlookup]
  simpa using baseIndexedMatch_of_base source dt hbase

theorem readyHeapMatch_base_def_eval
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (source : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : source ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES source (.DefHT dt)⟩)
      n (.success (.of ((readyHeapMatch c source (.DefHT dt)).getD false))) n := by
  rw [readyHeapMatch_base_def c p dt source hlookup hbase]
  exact baseIndexedMatch_def_eval c p n dt source hready hlookup hbase

theorem readyHeapMatch_base_statx_eval
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (source : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : source ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES source (.VarHT (.StatX p))⟩)
      n (.success (.of ((readyHeapMatch c source (.VarHT (.StatX p))).getD false))) n := by
  rw [readyHeapMatch_base_statx c p dt source hlookup hbase]
  exact baseIndexedMatch_statx_eval c p n dt source hready hlookup hbase

theorem readyHeapMatch_def_base
    (c : SpecTec.context) (p : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : target ∈ HeaptypeValidation.baseHeaptypes) :
    readyHeapMatch c (.DefHT dt) target =
      some (ReadyHeapMatchDefBase.readyDefBaseMatch dt target) := by
  have hsource :
      (SpecTec.heaptype.DefHT dt) ∉ HeaptypeValidation.baseHeaptypes := by
    simp [HeaptypeValidation.baseHeaptypes]
  unfold readyHeapMatch
  rw [if_neg hsource, if_pos hbase,
    indexedValue_def_of_lookup c p dt hlookup]
  rfl

theorem readyHeapMatch_statx_base
    (c : SpecTec.context) (p : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : target ∈ HeaptypeValidation.baseHeaptypes) :
    readyHeapMatch c (.VarHT (.StatX p)) target =
      some (ReadyHeapMatchDefBase.readyDefBaseMatch dt target) := by
  have hsource :
      (SpecTec.heaptype.VarHT (.StatX p)) ∉
        HeaptypeValidation.baseHeaptypes := by
    simp [HeaptypeValidation.baseHeaptypes]
  unfold readyHeapMatch
  rw [if_neg hsource, if_pos hbase,
    indexedValue_statx_of_lookup c p dt hlookup]
  rfl

theorem readyHeapMatch_def_base_eval
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : target ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES (.DefHT dt) target⟩)
      n (.success (.of ((readyHeapMatch c (.DefHT dt) target).getD false))) n := by
  rw [readyHeapMatch_def_base c p dt target hlookup hbase]
  exact ReadyHeapMatchDefBase.ready_def_base_result
    c p n dt target hready hlookup hbase

theorem readyHeapMatch_statx_base_eval
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : target ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES (.VarHT (.StatX p)) target⟩)
      n (.success (.of ((readyHeapMatch c (.VarHT (.StatX p)) target).getD false))) n := by
  rw [readyHeapMatch_statx_base c p dt target hlookup hbase]
  exact ReadyHeapMatchDefBase.ready_statx_base_result
    c p n dt target hready hlookup hbase

theorem readyHeapMatch_indexed_eq
    (c : SpecTec.context) (source target : SpecTec.heaptype)
    (hsource : source ∉ HeaptypeValidation.baseHeaptypes)
    (htarget : target ∉ HeaptypeValidation.baseHeaptypes) :
    readyHeapMatch c source target =
      ReadyHeapMatchIndexed.indexedHeapMatch c source target := by
  simp [readyHeapMatch, hsource, htarget]

theorem readyHeapMatch_def_def
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    readyHeapMatch c (.DefHT dtP) (.DefHT dtQ) =
      some (ValidatedMatchIndexFuel.matchIndex c p q) := by
  rw [readyHeapMatch_indexed_eq c (.DefHT dtP) (.DefHT dtQ)
    (by simp [HeaptypeValidation.baseHeaptypes])
    (by simp [HeaptypeValidation.baseHeaptypes])]
  exact ReadyHeapMatchIndexed.indexedHeapMatch_def_def
    c p q start dtP dtQ hready hp hq hP hQ

theorem readyHeapMatch_def_def_eval
    (c : SpecTec.context) (p q n : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.DefHT dtQ)⟩)
      n (.success (.of ((readyHeapMatch c
        (.DefHT dtP) (.DefHT dtQ)).getD false))) n := by
  rw [readyHeapMatch_indexed_eq c (.DefHT dtP) (.DefHT dtQ)
    (by simp [HeaptypeValidation.baseHeaptypes])
    (by simp [HeaptypeValidation.baseHeaptypes])]
  exact ReadyHeapMatchIndexed.indexedHeapMatch_def_def_eval
    c p q n dtP dtQ hready hp hq hP hQ

theorem readyHeapMatch_statx_def
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    readyHeapMatch c (.VarHT (.StatX p)) (.DefHT dtQ) =
      some (ValidatedMatchIndexFuel.matchIndex c p q) := by
  rw [readyHeapMatch_indexed_eq c (.VarHT (.StatX p)) (.DefHT dtQ)
    (by simp [HeaptypeValidation.baseHeaptypes])
    (by simp [HeaptypeValidation.baseHeaptypes])]
  exact ReadyHeapMatchIndexed.indexedHeapMatch_statx_def
    c p q start dtP dtQ hready hp hq hP hQ

theorem readyHeapMatch_def_statx
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    readyHeapMatch c (.DefHT dtP) (.VarHT (.StatX q)) =
      some (ValidatedMatchIndexFuel.matchIndex c p q) := by
  rw [readyHeapMatch_indexed_eq c (.DefHT dtP) (.VarHT (.StatX q))
    (by simp [HeaptypeValidation.baseHeaptypes])
    (by simp [HeaptypeValidation.baseHeaptypes])]
  exact ReadyHeapMatchIndexed.indexedHeapMatch_def_statx
    c p q start dtP dtQ hready hp hq hP hQ

theorem readyHeapMatch_statx_statx
    (c : SpecTec.context) (p q : Nat) :
    readyHeapMatch c (.VarHT (.StatX p)) (.VarHT (.StatX q)) =
      some (ValidatedMatchIndexFuel.matchIndex c p q) := by
  rw [readyHeapMatch_indexed_eq c (.VarHT (.StatX p))
    (.VarHT (.StatX q))
    (by simp [HeaptypeValidation.baseHeaptypes])
    (by simp [HeaptypeValidation.baseHeaptypes])]
  exact ReadyHeapMatchIndexed.indexedHeapMatch_statx_statx c p q

theorem readyHeapMatch_statx_def_eval
    (c : SpecTec.context) (p q n : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.VarHT (.StatX p)) (.DefHT dtQ)⟩)
      n (.success (.of ((readyHeapMatch c
        (.VarHT (.StatX p)) (.DefHT dtQ)).getD false))) n := by
  rw [readyHeapMatch_indexed_eq c (.VarHT (.StatX p)) (.DefHT dtQ)
    (by simp [HeaptypeValidation.baseHeaptypes])
    (by simp [HeaptypeValidation.baseHeaptypes])]
  exact ReadyHeapMatchIndexed.indexedHeapMatch_statx_def_eval
    c p q n dtP dtQ hready hp hq hP hQ

theorem readyHeapMatch_def_statx_eval
    (c : SpecTec.context) (p q n : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.VarHT (.StatX q))⟩)
      n (.success (.of ((readyHeapMatch c
        (.DefHT dtP) (.VarHT (.StatX q))).getD false))) n := by
  rw [readyHeapMatch_indexed_eq c (.DefHT dtP) (.VarHT (.StatX q))
    (by simp [HeaptypeValidation.baseHeaptypes])
    (by simp [HeaptypeValidation.baseHeaptypes])]
  exact ReadyHeapMatchIndexed.indexedHeapMatch_def_statx_eval
    c p q n dtP dtQ hready hp hq hP hQ

theorem readyHeapMatch_statx_statx_eval
    (c : SpecTec.context) (p q n : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» c.TYPES
        (.VarHT (.StatX p)) (.VarHT (.StatX q))⟩)
      n (.success (.of ((readyHeapMatch c
        (.VarHT (.StatX p)) (.VarHT (.StatX q))).getD false))) n := by
  rw [readyHeapMatch_indexed_eq c (.VarHT (.StatX p))
    (.VarHT (.StatX q))
    (by simp [HeaptypeValidation.baseHeaptypes])
    (by simp [HeaptypeValidation.baseHeaptypes])]
  exact ReadyHeapMatchIndexed.indexedHeapMatch_statx_statx_eval
    c p q n dtP dtQ hready hp hq hP hQ

end properties.wasm_module_ok.ReadyHeapMatch
