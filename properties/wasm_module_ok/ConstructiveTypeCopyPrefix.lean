import properties.wasm_module_ok.ConstructiveTypeCopyGroupCompatibility
import properties.wasm_module_ok.SourceReferenceLookup
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyPrefix
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open properties.wasm_module_ok.ConstructiveTypeCopyHeapMatch properties.wasm_module_ok.ConstructiveTypeCopyRelations
open properties.wasm_module_ok.ConstructiveTypeCopyRealization properties.wasm_module_ok.ConstructiveTypeCopyCompatibility

private theorem lookup_prefix (c d : context) (tail : List deftype)
    (he : d.TYPES=c.TYPES++tail) (p : Nat) (dt : deftype) (hp : c.TYPES[p]?=some dt) :
    d.TYPES[p]?=some dt := by
  rw [he,List.getElem?_append_left (List.getElem?_eq_some_iff.1 hp).1]
  exact hp

theorem resolves_prefix (c d : context) (tail : List deftype)
    (he : d.TYPES=c.TYPES++tail) (a v : heaptype) (h : Resolves c a v) : Resolves d a v := by
  cases h with
  | base ht hb => exact .base _ hb
  | stat p dt hp => exact .stat p dt (lookup_prefix c d tail he p dt hp)
  | closed p dt hp => exact .closed p dt (lookup_prefix c d tail he p dt hp)

theorem structural_prefix (c d : context) (tail : List deftype)
    (he : d.TYPES=c.TYPES++tail)
    (hc : CandidateTypeReady.Ready c) (hd : CandidateTypeReady.Ready d)
    (src target : strtype)
    (hs : ∀ h∈ReadyMatchReachability.sourceHeaptypes src,∃v,Resolves c h v)
    (ht : ∀ h∈ReadyMatchReachability.sourceHeaptypes target,∃v,Resolves c h v) :
    MatchStrtypeConditional.strMatch (fun a b => (ReadyHeapMatch.readyHeapMatch d a b).getD false) src target =
      MatchStrtypeConditional.strMatch (fun a b => (ReadyHeapMatch.readyHeapMatch c a b).getD false) src target := by
  have rel : ∀ h,(∃v,Resolves c h v) → HeapRel c d h h := by
    rintro h ⟨v,hv⟩
    exact ⟨v,hv,resolves_prefix c d tail he h v hv⟩
  apply str_match (HeapRel c d) _ _ _ src src target target
    (str_refl _ src (fun h hm => rel h (hs h hm)))
    (str_refl _ target (fun h hm => rel h (ht h hm)))
  rintro a a' b b' ⟨av,ha,hao⟩ ⟨bv,hb,hbo⟩
  exact congrArg (fun x : Option Bool => x.getD false)
    (transfer c d tail he hc hd a b a' b' av bv ha hb hao hbo)

theorem static_prefix (c d : context) (tail : List deftype)
    (he : d.TYPES=c.TYPES++tail)
    (hc : CandidateTypeReady.Ready c) (hd : CandidateTypeReady.Ready d)
    (hn : CandidateNestedReady.nestedTableReady c=true)
    (x : Nat) (fin : SpecTec.final) (hs : List heaptype) (st : strtype)
    (hv : SubtypeValidation.subtypeValid c (.SubT fin hs st)=true) (ht : heaptype)
    (hcheck : CandidateStaticSuperCheck.staticSuperCheck c x st ht=true) :
    CandidateStaticSuperCheck.staticSuperCheck d x st ht=true := by
  cases ht <;> simp only [CandidateStaticSuperCheck.staticSuperCheck,Bool.false_eq_true] at hcheck
  case VarHT tv =>
    cases tv with
    | RecX i => simp [CandidateStaticSuperCheck.staticSuperCheck] at hcheck
    | StatX i =>
      cases hi : c.TYPES[i]? with
      | none => simp [hi] at hcheck
      | some dt =>
        cases hu : unrollDeftypeResult dt with
        | none => simp [hi,ReadyStaticSubtypeMatch.staticSuperMatch,hu] at hcheck
        | some sub =>
          rcases sub with ⟨fin',hs',target⟩
          have hsraw : ∀ h∈ReadyMatchReachability.sourceHeaptypes st,∃v,Resolves c h v := by
            intro h hm
            rcases SourceReferenceLookup.source_heaptype_base_or_lookup_of_subtype_success
              c fin hs st h 0 0
              ((SubtypeValidation.subtype_success_iff_valid c _ 0 0).2 ⟨hv,rfl⟩) hm
              with hb | ⟨p,dt,hp,rfl⟩
            · exact ⟨h,.base h hb⟩
            · exact ⟨.DefHT dt,.stat p dt hp⟩
          have htclosed : ∀ h∈ReadyMatchReachability.sourceHeaptypes target,∃v,Resolves c h v := by
            obtain ⟨dt0,f0,hs0,st0,hi0,hu0,hrefs⟩ :=
              (CandidateNestedReady.nestedTableReady_true_iff c).1 hn i
                (List.getElem?_eq_some_iff.1 hi).1
            have hedt : dt0=dt := Option.some.inj (hi0.symm.trans hi)
            subst dt0
            have hest := SpecTec.subtype.SubT.inj (Option.some.inj (hu0.symm.trans hu))
            rcases hest with ⟨rfl,rfl,rfl⟩
            intro h hm
            rcases hrefs h hm with hb | ⟨p,dt,hp,rfl⟩
            · exact ⟨h,.base h hb⟩
            · exact ⟨.DefHT dt,.closed p dt hp⟩
          have hm := structural_prefix c d tail he hc hd st target hsraw htclosed
          simpa [CandidateStaticSuperCheck.staticSuperCheck,lookup_prefix c d tail he i dt hi,
            ReadyStaticSubtypeMatch.staticSuperMatch,hi,hu,hm] using hcheck

private theorem static_list_prefix (c d : context) (tail : List deftype)
    (he : d.TYPES=c.TYPES++tail)
    (hc : CandidateTypeReady.Ready c) (hd : CandidateTypeReady.Ready d)
    (hn : CandidateNestedReady.nestedTableReady c=true)
    (x : Nat) (fin : SpecTec.final) (hs : List heaptype) (st : strtype)
    (hv : SubtypeValidation.subtypeValid c (.SubT fin hs st)=true)
    (ts : List heaptype) (ht : CandidateStaticSuperList.staticSuperChecks c x st ts=true) :
    CandidateStaticSuperList.staticSuperChecks d x st ts=true := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hh : CandidateStaticSuperCheck.staticSuperCheck c x st t=true ∧
        CandidateStaticSuperList.staticSuperChecks c x st ts=true := by
      simpa [CandidateStaticSuperList.staticSuperChecks] using ht
    simp [CandidateStaticSuperList.staticSuperChecks,
      static_prefix c d tail he hc hd hn x fin hs st hv t hh.1,ih hh.2]

theorem paired_prefix (c d : context) (tail : List deftype)
    (he : d.TYPES=c.TYPES++tail)
    (hc : CandidateTypeReady.Ready c) (hd : CandidateTypeReady.Ready d)
    (hn : CandidateNestedReady.nestedTableReady c=true)
    (base : Nat) (ns : List Nat) (sts : List SpecTec.subtype)
    (hv : CandidateSourceChecks.sourceChecks c sts=true)
    (hp : CandidateGroupSuperChecks.pairedChecks c base ns sts=true) :
    CandidateGroupSuperChecks.pairedChecks d base ns sts=true := by
  induction sts generalizing ns with
  | nil => cases ns <;> simpa [CandidateGroupSuperChecks.pairedChecks] using hp
  | cons st sts ih =>
    cases ns with
    | nil => simp [CandidateGroupSuperChecks.pairedChecks] at hp
    | cons i ns =>
      rcases st with ⟨fin,hs,st⟩
      have hv' : SubtypeValidation.subtypeValid c (.SubT fin hs st)=true ∧
          CandidateSourceChecks.sourceChecks c sts=true := by simpa [CandidateSourceChecks.sourceChecks] using hv
      have hp' : CandidateStaticSuperList.staticSuperChecks c (base+i) st hs=true ∧
          CandidateGroupSuperChecks.pairedChecks c base ns sts=true := by
        simpa [CandidateGroupSuperChecks.pairedChecks] using hp
      simp [CandidateGroupSuperChecks.pairedChecks,
        static_list_prefix c d tail he hc hd hn (base+i) fin hs st hv'.1 hs hp'.1,
        ih ns hv'.2 hp'.2]

#print axioms paired_prefix
end properties.wasm_module_ok.ConstructiveTypeCopyPrefix
