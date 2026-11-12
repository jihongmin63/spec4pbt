import properties.wasm_module_ok.ReadyHeapMatch

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateHeapMatch

/-- The heap forms whose table entries are available to the exact executable
matcher. A definition is admitted only when it occurs in the type table. -/
inductive InTable (c : SpecTec.context) : SpecTec.heaptype → Prop where
  | base (ht : SpecTec.heaptype)
      (h : ht ∈ HeaptypeValidation.baseHeaptypes) : InTable c ht
  | definition (p : Nat) (dt : SpecTec.deftype)
      (h : c.TYPES[p]? = some dt) : InTable c (.DefHT dt)
  | static (p : Nat) (dt : SpecTec.deftype)
      (h : c.TYPES[p]? = some dt) : InTable c (.VarHT (.StatX p))

theorem ready_heap_match_defined
    (c : SpecTec.context) (source target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hs : InTable c source) (ht : InTable c target) :
    ∃ b, ReadyHeapMatch.readyHeapMatch c source target = some b := by
  cases hs with
  | base source hs =>
    cases ht with
    | base target ht =>
        exact ⟨_, ReadyHeapMatch.readyHeapMatch_base_base c source target hs ht⟩
    | definition p dt hget =>
        exact ⟨_, ReadyHeapMatch.readyHeapMatch_base_def c p dt source hget hs⟩
    | static p dt hget =>
        exact ⟨_, ReadyHeapMatch.readyHeapMatch_base_statx c p dt source hget hs⟩
  | definition p dtP hP =>
    cases ht with
    | base target ht =>
        exact ⟨_, ReadyHeapMatch.readyHeapMatch_def_base c p dtP target hP ht⟩
    | definition q dtQ hQ =>
        exact ⟨_, ReadyHeapMatch.readyHeapMatch_def_def c p q 0 dtP dtQ
          hready (List.getElem?_eq_some_iff.mp hP).1
          (List.getElem?_eq_some_iff.mp hQ).1 hP hQ⟩
    | static q dtQ hQ =>
        exact ⟨_, ReadyHeapMatch.readyHeapMatch_def_statx c p q 0 dtP dtQ
          hready (List.getElem?_eq_some_iff.mp hP).1
          (List.getElem?_eq_some_iff.mp hQ).1 hP hQ⟩
  | static p dtP hP =>
    cases ht with
    | base target ht =>
        exact ⟨_, ReadyHeapMatch.readyHeapMatch_statx_base c p dtP target hP ht⟩
    | definition q dtQ hQ =>
        exact ⟨_, ReadyHeapMatch.readyHeapMatch_statx_def c p q 0 dtP dtQ
          hready (List.getElem?_eq_some_iff.mp hP).1
          (List.getElem?_eq_some_iff.mp hQ).1 hP hQ⟩
    | static q dtQ hQ =>
        exact ⟨_, ReadyHeapMatch.readyHeapMatch_statx_statx c p q⟩

theorem ready_heap_match_eval
    (c : SpecTec.context) (source target : SpecTec.heaptype)
    (n : Nat) (hready : CandidateTypeReady.Ready c)
    (hs : InTable c source) (ht : InTable c target) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES source target⟩)
      n (.success (.of
        ((ReadyHeapMatch.readyHeapMatch c source target).getD false))) n := by
  cases hs with
  | base source hs =>
    cases ht with
    | base target ht =>
        exact ReadyHeapMatch.readyHeapMatch_base_base_eval
          c source target n hs ht
    | definition p dt hget =>
        exact ReadyHeapMatch.readyHeapMatch_base_def_eval
          c p n dt source hready hget hs
    | static p dt hget =>
        exact ReadyHeapMatch.readyHeapMatch_base_statx_eval
          c p n dt source hready hget hs
  | definition p dtP hP =>
    cases ht with
    | base target ht =>
        exact ReadyHeapMatch.readyHeapMatch_def_base_eval
          c p n dtP target hready hP ht
    | definition q dtQ hQ =>
        exact ReadyHeapMatch.readyHeapMatch_def_def_eval c p q n dtP dtQ
          hready (List.getElem?_eq_some_iff.mp hP).1
          (List.getElem?_eq_some_iff.mp hQ).1 hP hQ
    | static q dtQ hQ =>
        exact ReadyHeapMatch.readyHeapMatch_def_statx_eval c p q n dtP dtQ
          hready (List.getElem?_eq_some_iff.mp hP).1
          (List.getElem?_eq_some_iff.mp hQ).1 hP hQ
  | static p dtP hP =>
    cases ht with
    | base target ht =>
        exact ReadyHeapMatch.readyHeapMatch_statx_base_eval
          c p n dtP target hready hP ht
    | definition q dtQ hQ =>
        exact ReadyHeapMatch.readyHeapMatch_statx_def_eval c p q n dtP dtQ
          hready (List.getElem?_eq_some_iff.mp hP).1
          (List.getElem?_eq_some_iff.mp hQ).1 hP hQ
    | static q dtQ hQ =>
        exact ReadyHeapMatch.readyHeapMatch_statx_statx_eval c p q n dtP dtQ
          hready (List.getElem?_eq_some_iff.mp hP).1
          (List.getElem?_eq_some_iff.mp hQ).1 hP hQ

end properties.wasm_module_ok.CandidateHeapMatch
