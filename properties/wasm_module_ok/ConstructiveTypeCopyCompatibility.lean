import properties.wasm_module_ok.ConstructiveTypeCopyRealization
import properties.wasm_module_ok.CandidateGroupSuperChecks
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyCompatibility
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeCopy ConstructiveTypeCopyOrder
open properties.wasm_module_ok.ConstructiveTypeCopyHeapMatch properties.wasm_module_ok.ConstructiveTypeCopyRelations properties.wasm_module_ok.ConstructiveTypeCopyRealization

/-- Reifier state already contains every definition which will be appended. -/
theorem defs_old (c : context) (base w : Nat) (r : rectype)
    (hgroup : ∀ i<w,c.TYPES[base+i]?=some (.DefT r i)) :
    ∀ dt∈defs w r,dt∈c.TYPES := by
  intro dt hdt
  obtain ⟨i,hi,rfl⟩ := List.mem_map.1 hdt
  exact List.mem_iff_getElem?.2 ⟨base+i,hgroup i (List.mem_range.1 hi)⟩

theorem copied_ready (c : context) (base w : Nat) (r : rectype)
    (hgroup : ∀ i<w,c.TYPES[base+i]?=some (.DefT r i))
    (hr : CandidateTypeReady.Ready c) : CandidateTypeReady.Ready (extend c w r) :=
  ConstructiveTypeCopyReady.ready_duplicates c (defs w r) hr (defs_old c base w r hgroup)

theorem copied_nested (c : context) (base w : Nat) (r : rectype)
    (hgroup : ∀ i<w,c.TYPES[base+i]?=some (.DefT r i))
    (hn : CandidateNestedReady.nestedTableReady c=true) :
    CandidateNestedReady.nestedTableReady (extend c w r)=true :=
  ConstructiveTypeCopyReady.nested_duplicates c (defs w r) hn (defs_old c base w r hgroup)

theorem canonical_refl (c : context) (w : Nat) (r : rectype) (ht : heaptype)
    (hh : Canonical c ht) : HeapRel c (extend c w r) ht ht := by
  rcases hh with hb | ⟨p,dt,hp,rfl⟩
  · exact ⟨ht,.base ht hb,.base ht hb⟩
  · exact ⟨.DefHT dt,.closed p dt hp,.closed p dt (old_lookup c w r p dt hp)⟩

private theorem vals_refl (H : heaptype → heaptype → Prop) (v : valtype)
    (hh : ∀ ht∈ReadyMatchReachability.sourceValHeaptypes v,H ht ht) : ValRel H v v := by
  cases v with
  | NumT n => exact .num n
  | VecT v => exact .vec v
  | BotT => exact .bot
  | RefT r =>
    rcases r with ⟨nu,ht⟩
    exact .ref _ _ (.mk nu ht ht (hh ht (by simp [ReadyMatchReachability.sourceValHeaptypes])))

private theorem storage_refl (H : heaptype → heaptype → Prop) (s : storagetype)
    (hh : ∀ ht∈ReadyMatchReachability.sourceStorageHeaptypes s,H ht ht) : StorageRel H s s := by
  cases s with
  | ValStorageT v => exact .val v v (vals_refl H v hh)
  | PackStorageT p => exact .pack p

private theorem field_refl (H : heaptype → heaptype → Prop) (f : fieldtype)
    (hh : ∀ ht∈ReadyMatchReachability.sourceFieldHeaptypes f,H ht ht) : FieldRel H f f := by
  rcases f with ⟨mu,s⟩
  exact .mk mu s s (storage_refl H s hh)

private theorem list_refl {α : Type} (R : α → α → Prop) (xs : List α)
    (h : ∀ x∈xs,R x x) : List.Forall₂ R xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem str_refl (H : heaptype → heaptype → Prop) (st : strtype)
    (hh : ∀ ht∈ReadyMatchReachability.sourceHeaptypes st,H ht ht) : StrRel H st st := by
  cases st with
  | DefStructT st =>
    rcases st with ⟨fs⟩
    exact .struct fs fs (list_refl _ fs (fun f hf => field_refl H f
      (fun ht hht => hh ht (List.mem_flatMap.2 ⟨f,hf,hht⟩))))
  | DefArrayT ar =>
    rcases ar with ⟨f⟩
    exact .array f f (field_refl H f hh)
  | DefFuncT ft =>
    rcases ft with ⟨ins,outs⟩
    exact .func ins ins outs outs
      (list_refl _ ins (fun v hv => vals_refl H v (fun ht hht => hh ht
        (List.mem_flatMap.2 ⟨v,List.mem_append_left outs hv,hht⟩))))
      (list_refl _ outs (fun v hv => vals_refl H v (fun ht hht => hh ht
        (List.mem_flatMap.2 ⟨v,List.mem_append_right ins hv,hht⟩))))

theorem copied_str_match (c : context) (base w : Nat) (r : rectype) (hle : base≤c.TYPES.length)
    (hgroup : ∀ i<w,c.TYPES[base+i]?=some (.DefT r i))
    (hr : CandidateTypeReady.Ready c)
    (src out target : strtype) (hs : StrBound (base+w) src)
    (hg : Gen.support (str c.TYPES base w hle src hs) out)
    (ht : ∀ h∈ReadyMatchReachability.sourceHeaptypes target,Canonical c h) :
    MatchStrtypeConditional.strMatch
      (fun a b => (ReadyHeapMatch.readyHeapMatch (extend c w r) a b).getD false) out target =
    MatchStrtypeConditional.strMatch
      (fun a b => (ReadyHeapMatch.readyHeapMatch c a b).getD false) src target := by
  apply str_match (HeapRel c (extend c w r)) _ _ _ src out target target
    (str_realizes c base w r hle hgroup src out hs hg)
    (str_refl _ target (fun h hm => canonical_refl c w r h (ht h hm)))
  intro a a' b b' ha hb
  obtain ⟨av,ha,hao⟩ := ha
  obtain ⟨bv,hb,hbo⟩ := hb
  exact congrArg (fun x : Option Bool => x.getD false)
    (transfer c (extend c w r) (defs w r) rfl hr (copied_ready c base w r hgroup hr)
      a b a' b' av bv ha hb hao hbo)

theorem resolves_stat (c : context) (i : Nat) (v : heaptype)
    (h : Resolves c (.VarHT (.StatX i)) v) :
    ∃ dt,c.TYPES[i]?=some dt ∧ v=.DefHT dt := by
  cases h with
  | base _ hb => simp [HeaptypeValidation.baseHeaptypes] at hb
  | stat i dt hp => exact ⟨dt,hp,rfl⟩

/-- A successful original static-parent obligation is retained for every
actual generated reference and structural field/signature choice. -/
theorem static_check_preserved (c : context) (base w pos : Nat) (r : rectype)
    (hle : base≤c.TYPES.length)
    (hgroup : ∀ i<w,c.TYPES[base+i]?=some (.DefT r i))
    (hr : CandidateTypeReady.Ready c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (src out : strtype) (hs : StrBound (base+w) src)
    (hgs : Gen.support (str c.TYPES base w hle src hs) out)
    (ht ho : heaptype) (hh : HeapBound (base+w) ht)
    (hgh : Gen.support (heap c.TYPES base w hle ht hh) ho)
    (hcheck : CandidateStaticSuperCheck.staticSuperCheck c (base+pos) src ht=true) :
    CandidateStaticSuperCheck.staticSuperCheck (extend c w r) (c.TYPES.length+pos) out ho=true := by
  cases ht <;> simp only [CandidateStaticSuperCheck.staticSuperCheck,Bool.false_eq_true] at hcheck
  case VarHT tv =>
    cases tv with
    | RecX x => simp [CandidateStaticSuperCheck.staticSuperCheck] at hcheck
    | StatX i =>
      cases hlookup : c.TYPES[i]? with
      | none => simp [hlookup] at hcheck
      | some dt =>
        cases hu : unrollDeftypeResult dt with
        | none => simp [hlookup,ReadyStaticSubtypeMatch.staticSuperMatch,hu] at hcheck
        | some sub =>
          rcases sub with ⟨fin,hts,target⟩
          have hp : (i<base+pos ∧ fin=.NoFinal) ∧
              MatchStrtypeConditional.strMatch
                (fun a b => (ReadyHeapMatch.readyHeapMatch c a b).getD false) src target=true := by
            simpa [hlookup,ReadyStaticSubtypeMatch.staticSuperMatch,hu] using hcheck
          have hrel := heap_realizes c base w r hle hgroup _ ho hh hgh
          simp only [heap,Gen.Support.support_map] at hgh
          obtain ⟨j,hj,rfl⟩ := hgh
          have hjlt := relocate_before c.TYPES base w pos hle ⟨i,hh⟩ j hp.1.1 hj
          obtain ⟨v,hv,hv'⟩ := hrel
          obtain ⟨dt0,hi0,he0⟩ := resolves_stat c i v hv
          have hd0 : dt0=dt := Option.some.inj (hi0.symm.trans hlookup)
          subst dt0
          obtain ⟨dt1,hj1,he1⟩ := resolves_stat (extend c w r) j v hv'
          have hd1 : dt1=dt := heaptype.DefHT.inj (he1.symm.trans he0)
          subst dt1
          have htarget : ∀ h∈ReadyMatchReachability.sourceHeaptypes target,Canonical c h := by
            obtain ⟨dt',fin',hs',st',hi',hu',hrefs⟩ :=
              (CandidateNestedReady.nestedTableReady_true_iff c).1 hn i
                (List.getElem?_eq_some_iff.1 hlookup).1
            have hdt : dt'=dt := Option.some.inj (hi'.symm.trans hlookup)
            subst dt'
            have hst := SpecTec.subtype.SubT.inj (Option.some.inj (hu'.symm.trans hu))
            rcases hst with ⟨rfl,rfl,rfl⟩
            exact hrefs
          have hm := copied_str_match c base w r hle hgroup hr src out target hs hgs htarget
          simp [CandidateStaticSuperCheck.staticSuperCheck,hj1,ReadyStaticSubtypeMatch.staticSuperMatch,
            hu,hjlt,hp.1.2,hm,hp.2]

#print axioms static_check_preserved
end properties.wasm_module_ok.ConstructiveTypeCopyCompatibility
