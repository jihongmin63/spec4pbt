import properties.wasm_module_ok.ValtypeValidation
import properties.wasm_module_ok.FiniteClosure
import properties.wasm_module_ok.ConstGlobalGetValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.FiniteValidTypes

def heapCandidates (c : SpecTec.context) : List SpecTec.heaptype :=
  HeaptypeValidation.baseHeaptypes ++
    (List.range c.TYPES.length).map
      (fun x => SpecTec.heaptype.VarHT (.StatX x))

theorem heapCandidates_spec
    (c : SpecTec.context) (ht : SpecTec.heaptype) :
    ht ∈ heapCandidates c ↔
      HeaptypeValidation.heaptypeValid c ht = true := by
  rw [HeaptypeValidation.heaptype_valid_iff]
  simp only [heapCandidates, List.mem_append, List.mem_map,
    List.mem_range]
  constructor
  · rintro (hbase | ⟨x, hbound, rfl⟩)
    · exact Or.inl hbase
    · exact Or.inr ⟨x, rfl, hbound⟩
  · rintro (hbase | ⟨x, rfl, hbound⟩)
    · exact Or.inl hbase
    · exact Or.inr ⟨x, hbound, rfl⟩

def refCandidates (c : SpecTec.context) : List SpecTec.valtype :=
  (heapCandidates c).flatMap fun ht =>
    [.RefT (.«% %» .NoNull ht), .RefT (.«% %» .Null ht)]

theorem refCandidates_spec
    (c : SpecTec.context) (null : SpecTec.null)
    (ht : SpecTec.heaptype) :
    SpecTec.valtype.RefT (.«% %» null ht) ∈ refCandidates c ↔
      ht ∈ heapCandidates c := by
  cases null <;>
    simp [refCandidates, List.mem_flatMap]

def validCandidates (c : SpecTec.context) : List SpecTec.valtype :=
  [.NumT .I32T, .NumT .I64T, .NumT .F32T, .NumT .F64T,
   .VecT .V128T] ++ refCandidates c

theorem validCandidates_spec
    (c : SpecTec.context) (t : SpecTec.valtype) :
    t ∈ validCandidates c ↔
      ValtypeValidation.valtypeValid c t = true := by
  cases t with
  | NumT num =>
      cases num <;> simp [validCandidates, refCandidates,
        ValtypeValidation.valtypeValid]
  | VecT vec =>
      cases vec <;> simp [validCandidates, refCandidates,
        ValtypeValidation.valtypeValid]
  | RefT ref =>
      cases ref with
      | «% %» null ht =>
          simp only [validCandidates, List.mem_append]
          have hnot : SpecTec.valtype.RefT (.«% %» null ht) ∉
              ([.NumT .I32T, .NumT .I64T, .NumT .F32T,
                .NumT .F64T, .VecT .V128T] : List SpecTec.valtype) := by
            simp
          simp only [hnot, false_or]
          rw [refCandidates_spec, heapCandidates_spec]
          rfl
  | BotT =>
      simp [validCandidates, refCandidates,
        ValtypeValidation.valtypeValid, List.mem_flatMap]

def validUniverse (c : SpecTec.context) : Finset SpecTec.valtype :=
  (validCandidates c).toFinset

theorem validUniverse_spec
    (c : SpecTec.context) (t : SpecTec.valtype) :
    t ∈ validUniverse c ↔
      ValtypeValidation.valtypeValid c t = true := by
  simpa [validUniverse] using validCandidates_spec c t

theorem ref_func_output_not_in_validUniverse
    (c : SpecTec.context) (dt : SpecTec.deftype) :
    SpecTec.valtype.RefT (.«% %» .NoNull (.DefHT dt)) ∉
      validUniverse c := by
  rw [validUniverse_spec]
  simp [ValtypeValidation.valtypeValid,
    HeaptypeValidation.heaptypeValid]

def internalRefCandidates
    (ds : List SpecTec.deftype) : List SpecTec.valtype :=
  ds.flatMap fun dt =>
    [.RefT (.«% %» .NoNull (.DefHT dt)),
     .RefT (.«% %» .Null (.DefHT dt))]

def candidateTypes (c : SpecTec.context) : List SpecTec.valtype :=
  validCandidates c ++
    internalRefCandidates (c.TYPES ++ c.FUNCS) ++
    (c.GLOBALS.map fun gt =>
      match gt with
      | .GlobalT _ t => t)

def candidateUniverse (c : SpecTec.context) :
    Finset SpecTec.valtype :=
  (candidateTypes c).toFinset

theorem valid_mem_candidateUniverse
    (c : SpecTec.context) (t : SpecTec.valtype)
    (h : ValtypeValidation.valtypeValid c t = true) :
    t ∈ candidateUniverse c := by
  simp only [candidateUniverse, List.mem_toFinset,
    candidateTypes, List.mem_append]
  exact Or.inl (Or.inl ((validCandidates_spec c t).2 h))

theorem ref_func_output_mem_candidateUniverse
    (c : SpecTec.context) (x : SpecTec.funcidx)
    (dt : SpecTec.deftype) (hget : c.FUNCS[x]? = some dt) :
    SpecTec.valtype.RefT (.«% %» .NoNull (.DefHT dt)) ∈
      candidateUniverse c := by
  have hmem : dt ∈ c.FUNCS := List.mem_of_getElem? hget
  have href : SpecTec.valtype.RefT
      (.«% %» .NoNull (.DefHT dt)) ∈
      internalRefCandidates (c.TYPES ++ c.FUNCS) := by
    simp only [internalRefCandidates, List.mem_flatMap]
    exact ⟨dt, List.mem_append.mpr (Or.inr hmem), by simp⟩
  simp only [candidateUniverse, List.mem_toFinset,
    candidateTypes, List.mem_append]
  exact Or.inl (Or.inr href)

theorem type_constructor_output_mem_candidateUniverse
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (dt : SpecTec.deftype) (hget : c.TYPES[x]? = some dt) :
    SpecTec.valtype.RefT (.«% %» .NoNull (.DefHT dt)) ∈
      candidateUniverse c := by
  have hmem : dt ∈ c.TYPES := List.mem_of_getElem? hget
  have href : SpecTec.valtype.RefT
      (.«% %» .NoNull (.DefHT dt)) ∈
      internalRefCandidates (c.TYPES ++ c.FUNCS) := by
    simp only [internalRefCandidates, List.mem_flatMap]
    exact ⟨dt, List.mem_append.mpr (Or.inl hmem), by simp⟩
  simp only [candidateUniverse, List.mem_toFinset,
    candidateTypes, List.mem_append]
  exact Or.inl (Or.inr href)

theorem global_output_mem_candidateUniverse
    (c : SpecTec.context) (x : SpecTec.globalidx)
    (m : SpecTec.«mut») (t : SpecTec.valtype)
    (hget : c.GLOBALS[x]? = some (.GlobalT m t)) :
    t ∈ candidateUniverse c := by
  have hmem : SpecTec.globaltype.GlobalT m t ∈ c.GLOBALS :=
    List.mem_of_getElem? hget
  have hmap : t ∈ (c.GLOBALS.map fun gt =>
      match gt with
      | .GlobalT _ ty => ty) := by
    exact List.mem_map.mpr ⟨.GlobalT m t, hmem, rfl⟩
  simp only [candidateUniverse, List.mem_toFinset,
    candidateTypes, List.mem_append]
  exact Or.inr hmap

theorem const_ok_global_output_mem_candidateUniverse
    (c : SpecTec.context) (target : SpecTec.valtype)
    (xs : SpecTec.const) (x : SpecTec.globalidx)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok c target xs⟩)
      n (.success (.of ())) finalSupply)
    (hmem : SpecTec.instr.«GLOBAL.GET» x ∈ xs) :
    ∃ t : SpecTec.valtype,
      c.GLOBALS[x]? = some (.GlobalT .Cons t) ∧
        t ∈ candidateUniverse c := by
  obtain ⟨t, hget⟩ :=
    ConstGlobalGetValidation.const_ok_global_get_immutable
      c target xs x n finalSupply hcall hmem
  exact ⟨t, hget,
    global_output_mem_candidateUniverse c x .Cons t hget⟩

end properties.wasm_module_ok.FiniteValidTypes
