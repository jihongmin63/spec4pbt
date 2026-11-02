import properties.wasm_module_ok.ConstructiveTypeHistory

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveHistoryState
open SpecTec properties.wasm_module_ok
open ConstructiveTypeCopy ConstructiveTypeCopySemantics ConstructiveTypeEnvironment ConstructiveTypeHistory

def weaken (c d : context) (tail : List deftype) (he : d.TYPES = c.TYPES ++ tail)
    (s : Stored c) : Stored d where
  base := s.base
  source := s.source
  within := by rw [he,List.length_append]; exact Nat.le_trans s.within (Nat.le_add_right _ _)
  bound := s.bound
  provenance := by
    obtain ⟨before,after,start,finish,oldTail,hbefore,hrect,hprefix,hbase⟩ := s.provenance
    exact ⟨before,after,start,finish,oldTail++tail,hbefore,hrect,
      by rw [he,hprefix,List.append_assoc],hbase⟩

theorem closed_weaken (c d : context) (tail : List deftype) (he : d.TYPES = c.TYPES ++ tail)
    (s : Stored c) : closed d (weaken c d tail he s) = closed c s := by
  obtain ⟨before,after,start,finish,oldTail,hbefore,hrect,hprefix,hbase⟩ := s.provenance
  have hle : before.TYPES.length ≤ c.TYPES.length := hbase ▸ s.within
  have hle' : before.TYPES.length ≤ d.TYPES.length := by
    rw [he,List.length_append]; exact Nat.le_trans hle (Nat.le_add_right _ _)
  have hb : GroupBound (before.TYPES.length+s.source.length) s.source := hbase ▸ s.bound
  have hc := ConstructiveTypeCopyCompleteness.stored_closure before after c s.source
    start finish oldTail hrect hprefix hle hb
  have hd := ConstructiveTypeCopyCompleteness.stored_closure before after d s.source
    start finish (oldTail++tail) hrect (by rw [he,hprefix,List.append_assoc]) hle' hb
  have hv := Option.some.inj (hd.symm.trans hc)
  simpa only [closed,weaken,hbase] using hv

def record (c : context) (sts : List SpecTec.subtype)
    (hb : GroupBound (c.TYPES.length+sts.length) sts)
    (hc : ValidatedTypeChain.ValidatedTypes c) (n : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      n (.success (.of (extended c sts hb))) n) : Stored (extended c sts hb) where
  base := c.TYPES.length
  source := sts
  within := by simp [extended,definitions]
  bound := hb
  provenance := ⟨c,extended c sts hb,n,n,[],hc,hrect,by simp,rfl⟩

theorem record_closed (c : context) (sts : List SpecTec.subtype)
    (hb : GroupBound (c.TYPES.length+sts.length) sts)
    (hc : ValidatedTypeChain.ValidatedTypes c) (n : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      n (.success (.of (extended c sts hb))) n) :
    closed (extended c sts hb) (record c sts hb hc n hrect) =
      groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts hb := by
  have ht := ConstructiveTypeCopyCompleteness.stored_closure c (extended c sts hb)
    (extended c sts hb) sts n n [] hrect (by simp)
    (by simp [extended,definitions]) hb
  have hv : CandidateRectypeTable.transformed c sts =
      some (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts hb) := by
    simpa [CandidateRectypeTable.transformed,Nat.add_comm] using
      group_value_correct c.TYPES c.TYPES.length (Nat.le_refl _) sts hb
  exact Option.some.inj (ht.symm.trans hv)

def next (c : context) (sts : List SpecTec.subtype)
    (hb : GroupBound (c.TYPES.length+sts.length) sts)
    (hc : ValidatedTypeChain.ValidatedTypes c) (n : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      n (.success (.of (extended c sts hb))) n) (history : List (Stored c)) :
    List (Stored (extended c sts hb)) :=
  history.map (weaken c (extended c sts hb) _ rfl) ++ [record c sts hb hc n hrect]

/-- Recording an actually constructed group preserves coverage of every
definition, including repetitions and zero-length groups. -/
theorem next_covers (c : context) (sts : List SpecTec.subtype)
    (hb : GroupBound (c.TYPES.length+sts.length) sts)
    (hc : ValidatedTypeChain.ValidatedTypes c) (n : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      n (.success (.of (extended c sts hb))) n) (history : List (Stored c))
    (hh : Covers c history) : Covers (extended c sts hb) (next c sts hb hc n hrect history) := by
  intro p dt hget
  by_cases hold : p < c.TYPES.length
  · have hget' : c.TYPES[p]? = some dt := by
      simpa [extended,List.getElem?_append_left hold] using hget
    obtain ⟨s,hs,i,heq⟩ := hh p dt hget'
    refine ⟨weaken c (extended c sts hb) _ rfl s,?_,i,?_⟩
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨s,hs,rfl⟩)
    · rw [closed_weaken]
      exact heq
  · have hplen := (List.getElem?_eq_some_iff.mp hget).1
    have hi : p-c.TYPES.length < sts.length := by
      simp only [extended,List.length_append,definitions,List.length_map,List.length_range] at hplen
      omega
    have hpos : c.TYPES.length+(p-c.TYPES.length) = p := Nat.add_sub_cancel' (by omega)
    have hnew := definition_lookup c.TYPES
      (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts hb) sts.length (p-c.TYPES.length) hi
    have heq : dt = .DefT (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts hb)
        (p-c.TYPES.length) := Option.some.inj (hget.symm.trans (by simpa [extended,hpos] using hnew))
    refine ⟨record c sts hb hc n hrect,by simp [next],p-c.TYPES.length,?_⟩
    rw [record_closed]
    exact heq

end properties.wasm_module_ok.ConstructiveHistoryState
