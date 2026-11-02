import properties.wasm_module_ok.ConstructiveBodyMemoryProductions
import properties.wasm_module_ok.ConstructiveBodyProductionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryMembers
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyMemoryChoices ConstructiveBodyMemoryBounds ConstructiveBodyMemoryOperands ConstructiveBodyMemoryProductions ConstructiveBodyIndexedTypes ConstructiveBodyProductionCoverage ConstructiveConstTableCore

theorem of_forMemory (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c)
    (p : ConstructiveBodyProductions.Production c stack) (hp : p∈forMemory c stack env hd mem) : p∈all c stack env := by
  unfold all
  rw [head_complete c hd]
  exact List.mem_flatMap.mpr ⟨mem,memories_complete c mem,hp⟩

theorem loadNone_mem (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) :
    loadNone c stack env hd mem ty∈all c stack env := by
  apply of_forMemory c stack env hd mem
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨ty,numtypes_complete ty,?_⟩
  apply List.mem_append_left
  simp

theorem loadNone_produces (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype)
    (align offset : Nat) (ha : align≤numLog ty) (ho : OffsetBound hd.addr offset) :
    Produces (loadNone c stack env hd mem ty) (.«LOAD» mem.index { TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none }) := by
  unfold Produces loadNone ConstructiveBodySimpleAtoms.unchanged
  simp only [Audited.map,Audited.bind,Gen.Support.support_map,Gen.Support.support_bind]
  let im : ConstructiveBodyMemoryImmediates.Immediate hd.addr (numLog ty) := ⟨(align,offset),ha,ho⟩
  exact ⟨_,⟨im,ConstructiveBodyMemoryImmediates.complete _ _ im,rfl⟩,rfl⟩

theorem loadSome_mem (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) (pt : Pack ty) (ext : extension) :
    loadSome c stack env hd mem ty pt ext∈all c stack env := by
  apply of_forMemory c stack env hd mem
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨ty,numtypes_complete ty,?_⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨pt,packs_complete ty pt,?_⟩
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨ext,ConstructiveBodyOperatorEnums.domain_extension.complete ext,rfl⟩

theorem loadSome_produces (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) (pt : Pack ty) (ext : extension)
    (align offset : Nat) (ha : align≤packLog pt.val) (ho : OffsetBound hd.addr offset) :
    Produces (loadSome c stack env hd mem ty pt ext) (.«LOAD» mem.index { TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt.val,ext) }) := by
  unfold Produces loadSome ConstructiveBodySimpleAtoms.unchanged
  simp only [Audited.map,Audited.bind,Gen.Support.support_map,Gen.Support.support_bind]
  let im : ConstructiveBodyMemoryImmediates.Immediate hd.addr (packLog pt.val) := ⟨(align,offset),ha,ho⟩
  exact ⟨_,⟨im,ConstructiveBodyMemoryImmediates.complete _ _ im,rfl⟩,rfl⟩

theorem storeNone_mem (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) :
    storeNone c stack env hd mem ty∈all c stack env := by
  apply of_forMemory c stack env hd mem
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨ty,numtypes_complete ty,?_⟩
  apply List.mem_append_left
  simp

theorem storeNone_produces (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype)
    (align offset : Nat) (ha : align≤numLog ty) (ho : OffsetBound hd.addr offset) :
    Produces (storeNone c stack env hd mem ty) (.«STORE» mem.index { TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none }) := by
  unfold Produces storeNone ConstructiveBodySimpleAtoms.unchanged
  simp only [Audited.map,Audited.bind,Gen.Support.support_map,Gen.Support.support_bind]
  let im : ConstructiveBodyMemoryImmediates.Immediate hd.addr (numLog ty) := ⟨(align,offset),ha,ho⟩
  exact ⟨_,⟨im,ConstructiveBodyMemoryImmediates.complete _ _ im,rfl⟩,rfl⟩

theorem storeSome_mem (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) (pt : Pack ty) :
    storeSome c stack env hd mem ty pt∈all c stack env := by
  apply of_forMemory c stack env hd mem
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨ty,numtypes_complete ty,?_⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨pt,packs_complete ty pt,?_⟩
  apply List.mem_append_left
  exact List.mem_singleton_self _

theorem storeSome_produces (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) (pt : Pack ty)
    (align offset : Nat) (ha : align≤packLog pt.val) (ho : OffsetBound hd.addr offset) :
    Produces (storeSome c stack env hd mem ty pt) (.«STORE» mem.index { TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some pt.val }) := by
  unfold Produces storeSome ConstructiveBodySimpleAtoms.unchanged
  simp only [Audited.map,Audited.bind,Gen.Support.support_map,Gen.Support.support_bind]
  let im : ConstructiveBodyMemoryImmediates.Immediate hd.addr (packLog pt.val) := ⟨(align,offset),ha,ho⟩
  exact ⟨_,⟨im,ConstructiveBodyMemoryImmediates.complete _ _ im,rfl⟩,rfl⟩

theorem vloadNone_mem (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) :
    vloadNone c stack env hd mem∈all c stack env := by
  apply of_forMemory c stack env hd mem
  apply List.mem_append_left
  apply List.mem_append_right
  simp

theorem vloadNone_produces (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c)
    (align offset : Nat) (ha : align≤4) (ho : OffsetBound hd.addr offset) :
    Produces (vloadNone c stack env hd mem) (.«VEC.LOAD» mem.index { TYPE:=.V128T,ALIGN:=align,OFFSET:=offset,PACK:=none }) := by
  unfold Produces vloadNone ConstructiveBodySimpleAtoms.unchanged
  simp only [Audited.map,Audited.bind,Gen.Support.support_map,Gen.Support.support_bind]
  let im : ConstructiveBodyMemoryImmediates.Immediate hd.addr (4) := ⟨(align,offset),ha,ho⟩
  exact ⟨_,⟨im,ConstructiveBodyMemoryImmediates.complete _ _ im,rfl⟩,rfl⟩

theorem vloadSome_mem (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (pt : packtype) (ext : vextension) :
    vloadSome c stack env hd mem pt ext∈all c stack env := by
  apply of_forMemory c stack env hd mem
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨pt,ConstructiveBodyOperatorEnums.domain_packtype.complete pt,?_⟩
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨ext,vextensions.complete ext,rfl⟩

theorem vloadSome_produces (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (pt : packtype) (ext : vextension)
    (align offset : Nat) (ha : align≤packLog pt) (ho : OffsetBound hd.addr offset) :
    Produces (vloadSome c stack env hd mem pt ext) (.«VEC.LOAD» mem.index { TYPE:=.V128T,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) }) := by
  unfold Produces vloadSome ConstructiveBodySimpleAtoms.unchanged
  simp only [Audited.map,Audited.bind,Gen.Support.support_map,Gen.Support.support_bind]
  let im : ConstructiveBodyMemoryImmediates.Immediate hd.addr (packLog pt) := ⟨(align,offset),ha,ho⟩
  exact ⟨_,⟨im,ConstructiveBodyMemoryImmediates.complete _ _ im,rfl⟩,rfl⟩

theorem vstore_mem (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) :
    vstore c stack env hd mem∈all c stack env := by
  apply of_forMemory c stack env hd mem
  apply List.mem_append_left
  apply List.mem_append_right
  simp

theorem vstore_produces (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c)
    (align offset : Nat) (ha : align≤4) (ho : OffsetBound hd.addr offset) :
    Produces (vstore c stack env hd mem) (.«VEC.STORE» mem.index { TYPE:=.V128T,ALIGN:=align,OFFSET:=offset,PACK:=.VOID }) := by
  unfold Produces vstore ConstructiveBodySimpleAtoms.unchanged
  simp only [Audited.map,Audited.bind,Gen.Support.support_map,Gen.Support.support_bind]
  let im : ConstructiveBodyMemoryImmediates.Immediate hd.addr (4) := ⟨(align,offset),ha,ho⟩
  exact ⟨_,⟨im,ConstructiveBodyMemoryImmediates.complete _ _ im,rfl⟩,rfl⟩

theorem laneLoad_mem (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (pt : packtype) :
    laneLoad c stack env hd mem pt∈all c stack env := by
  apply of_forMemory c stack env hd mem
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨pt,ConstructiveBodyOperatorEnums.domain_packtype.complete pt,?_⟩
  apply List.mem_append_left
  simp

theorem laneLoad_produces (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (pt : packtype)
    (align offset : Nat) (ha : align≤packLog pt) (ho : OffsetBound hd.addr offset) (index : Int) (hi : index<Int.ofNat (laneBound pt)) :
    Produces (laneLoad c stack env hd mem pt) (.«VEC.LOAD_LANE» mem.index { TYPE:=.V128T,ALIGN:=align,OFFSET:=offset,PACK:=pt } index) := by
  unfold Produces laneLoad ConstructiveBodySimpleAtoms.unchanged
  simp only [Audited.map,Audited.bind,Gen.Support.support_map,Gen.Support.support_bind]
  let im : ConstructiveBodyMemoryImmediates.Immediate hd.addr (packLog pt) := ⟨(align,offset),ha,ho⟩
  exact ⟨_,⟨im,ConstructiveBodyMemoryImmediates.complete _ _ im,⟨⟨index,hi⟩,ConstructiveBodyMemoryBounds.lane_complete _ _ _,rfl⟩⟩,rfl⟩

theorem laneStore_mem (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (pt : packtype) :
    laneStore c stack env hd mem pt∈all c stack env := by
  apply of_forMemory c stack env hd mem
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨pt,ConstructiveBodyOperatorEnums.domain_packtype.complete pt,?_⟩
  apply List.mem_append_left
  simp

theorem laneStore_produces (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (pt : packtype)
    (align offset : Nat) (ha : align≤packLog pt) (ho : OffsetBound hd.addr offset) (index : Int) (hi : index<Int.ofNat (laneBound pt)) :
    Produces (laneStore c stack env hd mem pt) (.«VEC.STORE_LANE» mem.index { TYPE:=.V128T,ALIGN:=align,OFFSET:=offset,PACK:=pt } index) := by
  unfold Produces laneStore ConstructiveBodySimpleAtoms.unchanged
  simp only [Audited.map,Audited.bind,Gen.Support.support_map,Gen.Support.support_bind]
  let im : ConstructiveBodyMemoryImmediates.Immediate hd.addr (packLog pt) := ⟨(align,offset),ha,ho⟩
  exact ⟨_,⟨im,ConstructiveBodyMemoryImmediates.complete _ _ im,⟨⟨index,hi⟩,ConstructiveBodyMemoryBounds.lane_complete _ _ _,rfl⟩⟩,rfl⟩

#print axioms laneStore_produces
end properties.wasm_module_ok.ConstructiveBodyMemoryMembers
