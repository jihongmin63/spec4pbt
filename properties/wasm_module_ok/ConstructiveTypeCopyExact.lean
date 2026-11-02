import properties.wasm_module_ok.ConstructiveTypeCopySemantics
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyExact
open SpecTec
open properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open properties.wasm_module_ok.ConstructiveTypeCopy properties.wasm_module_ok.ConstructiveTypeCopySemantics

theorem ref_exact_value (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (rt : reftype) (h : RefBound (base+width) rt) (out : reftype) :
    Gen.support (ref table base width hle rt h) out ↔
      ∃ ho : RefBound (table.length+width) out,
        refValue table table.length width (Nat.le_refl _) out ho =
          refValue table base width hle rt h := by
  rcases rt with ⟨nu,ht⟩
  rcases out with ⟨nu',ht'⟩
  simp only [ref,Gen.Support.support_map]
  constructor
  · rintro ⟨v,hv,he⟩
    rcases reftype.«% %».inj he with ⟨rfl,rfl⟩
    obtain ⟨ho,he⟩ := (heap_exact_value table base width hle ht h _).1 hv
    exact ⟨ho,congrArg (reftype.«% %» nu') he⟩
  · rintro ⟨ho,he⟩
    have hh := reftype.«% %».inj he
    rcases hh with ⟨rfl,he⟩
    exact ⟨ht', (heap_exact_value table base width hle ht h ht').2 ⟨ho,he⟩,rfl⟩

theorem val_exact_value (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (vt : valtype) (h : ValBound (base+width) vt) (out : valtype) :
    Gen.support (val table base width hle vt h) out ↔
      ∃ ho : ValBound (table.length+width) out,
        valValue table table.length width (Nat.le_refl _) out ho =
          valValue table base width hle vt h := by
  cases vt <;> cases out <;> simp [val,valValue,ValBound,ref_exact_value]

theorem storage_exact_value (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : storagetype) (h : StorageBound (base+width) st) (out : storagetype) :
    Gen.support (storage table base width hle st h) out ↔
      ∃ ho : StorageBound (table.length+width) out,
        storageValue table table.length width (Nat.le_refl _) out ho =
          storageValue table base width hle st h := by
  cases st <;> cases out <;> simp [storage,storageValue,StorageBound,val_exact_value]

theorem field_exact_value (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ft : fieldtype) (h : FieldBound (base+width) ft) (out : fieldtype) :
    Gen.support (field table base width hle ft h) out ↔
      ∃ ho : FieldBound (table.length+width) out,
        fieldValue table table.length width (Nat.le_refl _) out ho =
          fieldValue table base width hle ft h := by
  rcases ft with ⟨mu,st⟩
  rcases out with ⟨mu',st'⟩
  simp only [field,Gen.Support.support_map]
  constructor
  · rintro ⟨v,hv,he⟩
    rcases fieldtype.FieldT.inj he with ⟨rfl,rfl⟩
    obtain ⟨ho,he⟩ := (storage_exact_value table base width hle st h _).1 hv
    exact ⟨ho,congrArg (fieldtype.FieldT mu') he⟩
  · rintro ⟨ho,he⟩
    have hh := fieldtype.FieldT.inj he
    rcases hh with ⟨rfl,he⟩
    exact ⟨st', (storage_exact_value table base width hle st h st').2 ⟨ho,he⟩,rfl⟩

theorem str_exact_value (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : strtype) (h : StrBound (base+width) st) (out : strtype) :
    Gen.support (str table base width hle st h) out ↔
      ∃ ho : StrBound (table.length+width) out,
        strValue table table.length width (Nat.le_refl _) out ho =
          strValue table base width hle st h := by
  cases st with
  | DefStructT st =>
    rcases st with ⟨fs⟩
    cases out with
    | DefStructT st =>
      rcases st with ⟨fs'⟩
      simpa [str,strValue,StrBound] using
        each_exact_value (FieldBound (base+width)) (FieldBound (table.length+width))
          (field table base width hle) (fieldValue table base width hle)
          (fieldValue table table.length width (Nat.le_refl _))
          (field_exact_value table base width hle) fs h fs'
    | DefArrayT ar => cases ar; simp [str,strValue]
    | DefFuncT ft => cases ft; simp [str,strValue]
  | DefArrayT ar =>
    rcases ar with ⟨f⟩
    cases out with
    | DefStructT st => cases st; simp [str,strValue]
    | DefArrayT ar =>
      rcases ar with ⟨f'⟩
      simpa [str,strValue,StrBound] using field_exact_value table base width hle f h f'
    | DefFuncT ft => cases ft; simp [str,strValue]
  | DefFuncT ft =>
    rcases ft with ⟨ins,outs⟩
    cases out with
    | DefStructT st => cases st; simp [str,strValue]
    | DefArrayT ar => cases ar; simp [str,strValue]
    | DefFuncT ft =>
      rcases ft with ⟨ins',outs'⟩
      have hi := each_exact_value (ValBound (base+width)) (ValBound (table.length+width))
        (val table base width hle) (valValue table base width hle)
        (valValue table table.length width (Nat.le_refl _))
        (val_exact_value table base width hle) ins h.1 ins'
      have ho := each_exact_value (ValBound (base+width)) (ValBound (table.length+width))
        (val table base width hle) (valValue table base width hle)
        (valValue table table.length width (Nat.le_refl _))
        (val_exact_value table base width hle) outs h.2 outs'
      simp only [str,Gen.Support.support_bind,Gen.Support.support_pure]
      constructor
      · rintro ⟨is,his,os,hos,he⟩
        have hp := functype.FuncT.inj (strtype.DefFuncT.inj he)
        rw [←hp.1] at his
        rw [←hp.2] at hos
        obtain ⟨hI,hEI⟩ := hi.1 his
        obtain ⟨hO,hEO⟩ := ho.1 hos
        exact ⟨⟨hI,hO⟩,congrArg strtype.DefFuncT (congrArg₂ functype.FuncT hEI hEO)⟩
      · rintro ⟨hb,he⟩
        have hp := functype.FuncT.inj (strtype.DefFuncT.inj he)
        exact ⟨ins',hi.2 ⟨hb.1,hp.1⟩,outs',ho.2 ⟨hb.2,hp.2⟩,rfl⟩

theorem sub_exact_value (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : SpecTec.subtype) (h : SubBound (base+width) st) (out : SpecTec.subtype) :
    Gen.support (sub table base width hle st h) out ↔
      ∃ ho : SubBound (table.length+width) out,
        subValue table table.length width (Nat.le_refl _) out ho =
          subValue table base width hle st h := by
  rcases st with ⟨fin,hs,st⟩
  rcases out with ⟨fin',hs',st'⟩
  have hh := each_exact_value (HeapBound (base+width)) (HeapBound (table.length+width))
    (heap table base width hle) (heapValue table base width hle)
    (heapValue table table.length width (Nat.le_refl _))
    (heap_exact_value table base width hle) hs h.1 hs'
  have hhst := str_exact_value table base width hle st h.2 st'
  simp only [sub,Gen.Support.support_bind,Gen.Support.support_pure]
  constructor
  · rintro ⟨hsO,hhO,stO,hstO,he⟩
    have hp := SpecTec.subtype.SubT.inj he
    rw [←hp.2.1] at hhO
    rw [←hp.2.2] at hstO
    obtain ⟨hH,hEH⟩ := hh.1 hhO
    obtain ⟨hS,hES⟩ := hhst.1 hstO
    refine ⟨⟨hH,hS⟩,?_⟩
    simp only [subValue]
    rw [hp.1,hEH,hES]
  · rintro ⟨hb,he⟩
    have hp := SpecTec.subtype.SubT.inj he
    refine ⟨hs',hh.2 ⟨hb.1,hp.2.1⟩,st',hhst.2 ⟨hb.2,hp.2.2⟩,?_⟩
    rw [hp.1]

/-- Full finite reifier support, before exposing original transformation names. -/
theorem group_exact_value (table : List deftype) (base : Nat) (hle : base ≤ table.length)
    (sts : List SpecTec.subtype) (h : GroupBound (base+sts.length) sts)
    (outs : List SpecTec.subtype) :
    Gen.support (group table base hle sts h) (.RecT outs) ↔
      ∃ ho : GroupBound (table.length+sts.length) outs,
        mapP (SubBound (table.length+sts.length))
          (subValue table table.length sts.length (Nat.le_refl _)) outs ho =
        mapP (SubBound (base+sts.length)) (subValue table base sts.length hle) sts h := by
  simpa [group,GroupBound] using
    each_exact_value (SubBound (base+sts.length)) (SubBound (table.length+sts.length))
      (sub table base sts.length hle) (subValue table base sts.length hle)
      (subValue table table.length sts.length (Nat.le_refl _))
      (sub_exact_value table base sts.length hle) sts h outs

private theorem subvalues_width (table : List deftype) (base : Nat) (hle : base ≤ table.length)
    (a b : Nat) (heq : a = b) (xs : List SpecTec.subtype)
    (ha : GroupBound (base+a) xs) (hb : GroupBound (base+b) xs) :
    mapP (SubBound (base+a)) (subValue table base a hle) xs ha =
      mapP (SubBound (base+b)) (subValue table base b hle) xs hb := by
  subst b
  rfl

/-- Exact inverse of the original whole-group roll/substitution. The domain
retains every bounded raw AST with this closed group, not a normalized AST. -/
theorem group_exact_original (c : context) (base : Nat) (hle : base ≤ c.TYPES.length)
    (sts : List SpecTec.subtype) (h : GroupBound (base+sts.length) sts)
    (outs : List SpecTec.subtype) :
    Gen.support (group c.TYPES base hle sts h) (.RecT outs) ↔
      outs.length = sts.length ∧ GroupBound (c.TYPES.length+outs.length) outs ∧
      CandidateRectypeTable.transformed c outs = some (groupValue c.TYPES base hle sts h) := by
  rw [group_exact_value]
  constructor
  · rintro ⟨ho,he⟩
    have hlen : outs.length = sts.length := by
      simpa only [mapP_length] using congrArg List.length he
    have ho' : GroupBound (c.TYPES.length+outs.length) outs := by simpa [hlen] using ho
    refine ⟨hlen,ho',?_⟩
    have hv := group_value_correct c.TYPES c.TYPES.length (Nat.le_refl _) outs ho'
    have heq : groupValue c.TYPES c.TYPES.length (Nat.le_refl _) outs ho' =
        groupValue c.TYPES base hle sts h := by
      unfold groupValue
      exact congrArg rectype.RecT
        ((subvalues_width c.TYPES c.TYPES.length (Nat.le_refl _)
          outs.length sts.length hlen outs ho' ho).trans he)
    simpa only [CandidateRectypeTable.transformed,Nat.add_comm,heq] using hv
  · rintro ⟨hlen,ho,he⟩
    have ho' : GroupBound (c.TYPES.length+sts.length) outs := by simpa [hlen] using ho
    refine ⟨ho',?_⟩
    have hv := group_value_correct c.TYPES c.TYPES.length (Nat.le_refl _) outs ho
    have he' :
        substRectypeResult (.RecT (rollSubtypes outs c.TYPES.length (c.TYPES.length+outs.length))) c.TYPES =
          some (groupValue c.TYPES base hle sts h) := by
      simpa only [CandidateRectypeTable.transformed,Nat.add_comm] using he
    have heq := rectype.RecT.inj (Option.some.inj (hv.symm.trans he'))
    exact (subvalues_width c.TYPES c.TYPES.length (Nat.le_refl _)
      outs.length sts.length hlen outs ho ho').symm.trans heq

#print axioms group_exact_original
end properties.wasm_module_ok.ConstructiveTypeCopyExact
