import properties.wasm_module_ok.ConstructiveBodyMemoryImmediates
import properties.wasm_module_ok.ConstructiveBodyIndexedProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryProductions
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyMemoryChoices ConstructiveBodyMemoryBounds ConstructiveBodyMemoryOperands ConstructiveBodyIndexedTypes ConstructiveBodyIndexedProductions ConstructiveConstTableCore

theorem vec_backed (c : context) (ty : vectype) : CandidateValMatch.InTableVal c (.VecT ty) := by
  intro heap h; cases h

def laneBound : packtype → Nat
  | .I8 => 16 | .I16 => 8 | .I32 => 4 | .I64 => 2

theorem laneBound_eq (pt : packtype) : Int.ofNat (laneBound pt)=Int.tdiv 16 (ConstructiveBodyScalarSizes.packSize pt) := by
  cases pt <;> rfl

theorem laneBound_pos (pt : packtype) : 0<laneBound pt := by cases pt <;> decide

def loadNone (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr)]) (.NoEllipses,[.NumT ty])
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (num_backed c ty) (nil_backed c .NoEllipses))
    ((ConstructiveBodyMemoryImmediates.generate hd.addr (numLog ty)).map fun im =>
      ⟨(.«LOAD» mem.index { TYPE:=ty,ALIGN:=im.val.1,OFFSET:=im.val.2,PACK:=none }),by
        intro n
        apply ConstructiveBodyMemoryCalls.load c stack mem.index mem.addr mem.lim _ ty mem.lookup
        · intro start
          exact ConstructiveBodyMemoryOperands.loadop_ok_none c ty im.val.1 im.val.2 hd.addr hd.lim hd.lookup im.property.2 im.property.1 start
      ⟩)

def loadSome (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) (pt : Pack ty) (ext : extension) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr)]) (.NoEllipses,[.NumT ty])
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (num_backed c ty) (nil_backed c .NoEllipses))
    ((ConstructiveBodyMemoryImmediates.generate hd.addr (packLog pt.val)).map fun im =>
      ⟨(.«LOAD» mem.index { TYPE:=ty,ALIGN:=im.val.1,OFFSET:=im.val.2,PACK:=some (pt.val,ext) }),by
        intro n
        apply ConstructiveBodyMemoryCalls.load c stack mem.index mem.addr mem.lim _ ty mem.lookup
        · intro start
          exact ConstructiveBodyMemoryOperands.loadop_ok_some c ty im.val.1 im.val.2 pt.val ext hd.addr hd.lim hd.lookup im.property.2 pt.property im.property.1 start
      ⟩)

def storeNone (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr),.NumT ty]) (.NoEllipses,[])
    (cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (num_backed c ty) (nil_backed c .NoEllipses)))
    (nil_backed c .NoEllipses)
    ((ConstructiveBodyMemoryImmediates.generate hd.addr (numLog ty)).map fun im =>
      ⟨(.«STORE» mem.index { TYPE:=ty,ALIGN:=im.val.1,OFFSET:=im.val.2,PACK:=none }),by
        intro n
        apply ConstructiveBodyMemoryCalls.store c stack mem.index mem.addr mem.lim _ ty mem.lookup
        · intro start
          exact ConstructiveBodyMemoryOperands.storeop_ok_none c ty im.val.1 im.val.2 hd.addr hd.lim hd.lookup im.property.2 im.property.1 start
      ⟩)

def storeSome (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (ty : numtype) (pt : Pack ty) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr),.NumT ty]) (.NoEllipses,[])
    (cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (num_backed c ty) (nil_backed c .NoEllipses)))
    (nil_backed c .NoEllipses)
    ((ConstructiveBodyMemoryImmediates.generate hd.addr (packLog pt.val)).map fun im =>
      ⟨(.«STORE» mem.index { TYPE:=ty,ALIGN:=im.val.1,OFFSET:=im.val.2,PACK:=some pt.val }),by
        intro n
        apply ConstructiveBodyMemoryCalls.store c stack mem.index mem.addr mem.lim _ ty mem.lookup
        · intro start
          exact ConstructiveBodyMemoryOperands.storeop_ok_some c ty im.val.1 im.val.2 pt.val hd.addr hd.lim hd.lookup im.property.2 pt.property im.property.1 start
      ⟩)

def vloadNone (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr)]) (.NoEllipses,[.VecT .V128T])
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (vec_backed c .V128T) (nil_backed c .NoEllipses))
    ((ConstructiveBodyMemoryImmediates.generate hd.addr (4)).map fun im =>
      ⟨(.«VEC.LOAD» mem.index { TYPE:=.V128T,ALIGN:=im.val.1,OFFSET:=im.val.2,PACK:=none }),by
        intro n
        apply ConstructiveBodyMemoryCalls.vload c stack mem.index mem.addr mem.lim _ .V128T mem.lookup
        · intro start
          exact ConstructiveBodyMemoryOperands.vloadop_ok_none c .V128T im.val.1 im.val.2 hd.addr hd.lim hd.lookup im.property.2 im.property.1 start
      ⟩)

def vloadSome (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (pt : packtype) (ext : vextension) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr)]) (.NoEllipses,[.VecT .V128T])
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (vec_backed c .V128T) (nil_backed c .NoEllipses))
    ((ConstructiveBodyMemoryImmediates.generate hd.addr (packLog pt)).map fun im =>
      ⟨(.«VEC.LOAD» mem.index { TYPE:=.V128T,ALIGN:=im.val.1,OFFSET:=im.val.2,PACK:=some (pt,ext) }),by
        intro n
        apply ConstructiveBodyMemoryCalls.vload c stack mem.index mem.addr mem.lim _ .V128T mem.lookup
        · intro start
          exact ConstructiveBodyMemoryOperands.vloadop_ok_some c .V128T im.val.1 im.val.2 pt ext hd.addr hd.lim hd.lookup im.property.2 (by cases pt <;> decide) im.property.1 start
      ⟩)

def vstore (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr),.VecT .V128T]) (.NoEllipses,[])
    (cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (vec_backed c .V128T) (nil_backed c .NoEllipses)))
    (nil_backed c .NoEllipses)
    ((ConstructiveBodyMemoryImmediates.generate hd.addr (4)).map fun im =>
      ⟨(.«VEC.STORE» mem.index { TYPE:=.V128T,ALIGN:=im.val.1,OFFSET:=im.val.2,PACK:=.VOID }),by
        intro n
        apply ConstructiveBodyMemoryCalls.vstore c stack mem.index mem.addr mem.lim _ .V128T mem.lookup
        · intro start
          exact ConstructiveBodyMemoryOperands.vstoreop_ok_void c .V128T im.val.1 im.val.2 hd.addr hd.lim hd.lookup im.property.2 im.property.1 start
      ⟩)

def laneLoad (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (pt : packtype) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr),.VecT .V128T]) (.NoEllipses,[.VecT .V128T])
    (cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (vec_backed c .V128T) (nil_backed c .NoEllipses)))
    (cons_backed .NoEllipses (vec_backed c .V128T) (nil_backed c .NoEllipses))
    ((ConstructiveBodyMemoryImmediates.generate hd.addr (packLog pt)).bind fun im =>
      (ConstructiveBodyMemoryBounds.lane (laneBound pt) (laneBound_pos pt)).map fun index =>
      ⟨(.«VEC.LOAD_LANE» mem.index { TYPE:=.V128T,ALIGN:=im.val.1,OFFSET:=im.val.2,PACK:=pt } index.val),by
        intro n
        apply ConstructiveBodyMemoryCalls.laneLoad c stack mem.index mem.addr mem.lim _ .V128T index.val mem.lookup
        · intro start
          exact ConstructiveBodyMemoryOperands.vlaneop_ok_pack c .V128T im.val.1 im.val.2 pt hd.addr hd.lim hd.lookup im.property.2 (by cases pt <;> decide) im.property.1 start
        · rw [←laneBound_eq]; exact index.property
      ⟩)

def laneStore (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) (pt : packtype) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr),.VecT .V128T]) (.NoEllipses,[])
    (cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (vec_backed c .V128T) (nil_backed c .NoEllipses)))
    (nil_backed c .NoEllipses)
    ((ConstructiveBodyMemoryImmediates.generate hd.addr (packLog pt)).bind fun im =>
      (ConstructiveBodyMemoryBounds.lane (laneBound pt) (laneBound_pos pt)).map fun index =>
      ⟨(.«VEC.STORE_LANE» mem.index { TYPE:=.V128T,ALIGN:=im.val.1,OFFSET:=im.val.2,PACK:=pt } index.val),by
        intro n
        apply ConstructiveBodyMemoryCalls.laneStore c stack mem.index mem.addr mem.lim _ .V128T index.val mem.lookup
        · intro start
          exact ConstructiveBodyMemoryOperands.vlaneop_ok_pack c .V128T im.val.1 im.val.2 pt hd.addr hd.lim hd.lookup im.property.2 (by cases pt <;> decide) im.property.1 start
        · rw [←laneBound_eq]; exact index.property
      ⟩)

def forMemory (c : context) (stack : inferresulttype) (env : Env c) (hd : Head c) (mem : Memory c) : List (Production c stack) :=
  (numtypes.flatMap fun ty => [loadNone c stack env hd mem ty,storeNone c stack env hd mem ty] ++
    ((packs ty).flatMap fun pt => [storeSome c stack env hd mem ty pt] ++
      ((ConstructiveBodyOperatorEnums.domain_extension.first::ConstructiveBodyOperatorEnums.domain_extension.rest).map fun ext => loadSome c stack env hd mem ty pt ext))) ++
  [vloadNone c stack env hd mem,vstore c stack env hd mem] ++
  ((ConstructiveBodyOperatorEnums.domain_packtype.first::ConstructiveBodyOperatorEnums.domain_packtype.rest).flatMap fun pt =>
    [laneLoad c stack env hd mem pt,laneStore c stack env hd mem pt] ++
    ((vextensions.first::vextensions.rest).map fun ext => vloadSome c stack env hd mem pt ext))

def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  match head c with
  | none => []
  | some hd => (ConstructiveBodyIndexedTypes.memories c).flatMap fun mem => forMemory c stack env hd mem

#print axioms laneLoad
end properties.wasm_module_ok.ConstructiveBodyMemoryProductions
