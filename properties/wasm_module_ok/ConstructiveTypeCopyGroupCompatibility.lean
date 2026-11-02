import properties.wasm_module_ok.ConstructiveTypeCopyCompatibility
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyGroupCompatibility
open SpecTec properties.wasm_module_ok
open ConstructiveTypeCopy
open properties.wasm_module_ok.ConstructiveTypeCopyCompatibility properties.wasm_module_ok.ConstructiveTypeCopyRealization

theorem static_list_preserved (c : context) (base w pos : Nat) (r : rectype)
    (hle : base≤c.TYPES.length) (hgroup : ∀ i<w,c.TYPES[base+i]?=some (.DefT r i))
    (hr : CandidateTypeReady.Ready c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (src out : strtype) (hs : StrBound (base+w) src)
    (hgs : Gen.support (str c.TYPES base w hle src hs) out)
    (hts hos : List heaptype) (hh : ∀ h∈hts,HeapBound (base+w) h)
    (hgh : Gen.support (each (HeapBound (base+w)) (heap c.TYPES base w hle) hts hh) hos)
    (hcheck : CandidateStaticSuperList.staticSuperChecks c (base+pos) src hts=true) :
    CandidateStaticSuperList.staticSuperChecks (extend c w r) (c.TYPES.length+pos) out hos=true := by
  have hrel := (each_support _ _ _ _ _).1 hgh
  clear hgh hh
  induction hrel with
  | nil => rfl
  | @cons h ho hs hos hhead htail ih =>
    have hchecks : CandidateStaticSuperCheck.staticSuperCheck c (base+pos) src h=true ∧
        CandidateStaticSuperList.staticSuperChecks c (base+pos) src hs=true := by
      simpa [CandidateStaticSuperList.staticSuperChecks] using hcheck
    obtain ⟨hb,hg⟩ := hhead
    have hhead' := static_check_preserved c base w pos r hle hgroup hr hn
      src out _ hgs h ho hb hg hchecks.1
    simpa [CandidateStaticSuperList.staticSuperChecks,hhead'] using ih hchecks.2

/-- Preserve the original closing pass in its exact index and rule order. -/
theorem paired_preserved (c : context) (base w : Nat) (r : rectype)
    (hle : base≤c.TYPES.length) (hgroup : ∀ i<w,c.TYPES[base+i]?=some (.DefT r i))
    (hr : CandidateTypeReady.Ready c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (ns : List Nat) (sts outs : List SpecTec.subtype)
    (hb : ∀ s∈sts,SubBound (base+w) s)
    (hg : Gen.support (each (SubBound (base+w)) (sub c.TYPES base w hle) sts hb) outs)
    (hcheck : CandidateGroupSuperChecks.pairedChecks c base ns sts=true) :
    CandidateGroupSuperChecks.pairedChecks (extend c w r) c.TYPES.length ns outs=true := by
  have hrel := (each_support _ _ _ _ _).1 hg
  clear hg hb
  induction hrel generalizing ns with
  | nil => cases ns <;> simpa [CandidateGroupSuperChecks.pairedChecks] using hcheck
  | @cons st out sts outs hhead htail ih =>
    cases ns with
    | nil => simp [CandidateGroupSuperChecks.pairedChecks] at hcheck
    | cons i ns =>
      rcases st with ⟨fin,hs,st⟩
      obtain ⟨hb,hg⟩ := hhead
      simp only [sub,Gen.Support.support_bind,Gen.Support.support_pure] at hg
      obtain ⟨ho,hh,so,hst,rfl⟩ := hg
      have hchecks : CandidateStaticSuperList.staticSuperChecks c (base+i) st hs=true ∧
          CandidateGroupSuperChecks.pairedChecks c base ns sts=true := by
        simpa [CandidateGroupSuperChecks.pairedChecks] using hcheck
      have hhead' := static_list_preserved c base w i r hle hgroup hr hn
        st so hb.2 hst hs ho hb.1 hh hchecks.1
      simpa [CandidateGroupSuperChecks.pairedChecks,hhead'] using ih ns hchecks.2

#print axioms paired_preserved
end properties.wasm_module_ok.ConstructiveTypeCopyGroupCompatibility
