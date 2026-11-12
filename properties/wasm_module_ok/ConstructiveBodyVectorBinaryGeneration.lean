import properties.wasm_module_ok.ConstructiveBodyVectorBinaryRules
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyVectorBinaryGeneration
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore
open ConstructiveBodyVectorBinaryRules ConstructiveBodyEnvironment ConstructiveBodyProductions

def simple : vibinop → Bool
  | .Shuffle _ => false
  | _ => true

def plainTail : List vibinop := [.Sub,.Mul,.MinS,.MinU,.MaxS,.MaxU,.AvgrU,.AddSatS,.AddSatU,.SubSatS,.SubSatU,.DotS,.Q15MulRSatS,.ExtMulLowS,.ExtMulHighS,.ExtMulLowU,.ExtMulHighU,.Swizzle,.NarrowS,.NarrowU,.RelaxedSwizzle,.RelaxedQ15MulRS,.RelaxedDot]

theorem plain_valid (op : vibinop) (h : op∈.Add::plainTail) : simple op=true := by
  simp only [plainTail,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

def plains : Audited {op : vibinop // simple op=true} :=
  ConstructiveBodyCertifiedChoice.choose .Add plainTail plain_valid

theorem plain_complete (op : vibinop) (h : simple op=true) : Gen.support plains.generator ⟨op,h⟩ := by
  apply ConstructiveBodyCertifiedChoice.complete
  change op∈.Add::plainTail
  cases op <;> simp_all [plainTail,simple]

def natLists : Audited (List Nat) :=
  ⟨ConstructiveLists.all Gen.arbNat,ConstructiveLists.all_audit _ ConstructiveGenAudit.arbNat_audit⟩

theorem natLists_complete (xs : List Nat) : Gen.support natLists.generator xs := by
  simp [natLists]

def integers : Audited vibinop :=
  ConstructiveBodyChoice.branches (plains.map Subtype.val) [natLists.map .Shuffle]

theorem integers_complete (op : vibinop) : Gen.support integers.generator op := by
  apply (ConstructiveBodyChoice.branches_support _ _ _).2
  cases op with
  | Add =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.Add,rfl⟩,plain_complete .Add rfl,rfl⟩
  | Sub =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.Sub,rfl⟩,plain_complete .Sub rfl,rfl⟩
  | Mul =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.Mul,rfl⟩,plain_complete .Mul rfl,rfl⟩
  | MinS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.MinS,rfl⟩,plain_complete .MinS rfl,rfl⟩
  | MinU =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.MinU,rfl⟩,plain_complete .MinU rfl,rfl⟩
  | MaxS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.MaxS,rfl⟩,plain_complete .MaxS rfl,rfl⟩
  | MaxU =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.MaxU,rfl⟩,plain_complete .MaxU rfl,rfl⟩
  | AvgrU =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.AvgrU,rfl⟩,plain_complete .AvgrU rfl,rfl⟩
  | AddSatS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.AddSatS,rfl⟩,plain_complete .AddSatS rfl,rfl⟩
  | AddSatU =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.AddSatU,rfl⟩,plain_complete .AddSatU rfl,rfl⟩
  | SubSatS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.SubSatS,rfl⟩,plain_complete .SubSatS rfl,rfl⟩
  | SubSatU =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.SubSatU,rfl⟩,plain_complete .SubSatU rfl,rfl⟩
  | DotS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.DotS,rfl⟩,plain_complete .DotS rfl,rfl⟩
  | Q15MulRSatS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.Q15MulRSatS,rfl⟩,plain_complete .Q15MulRSatS rfl,rfl⟩
  | ExtMulLowS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.ExtMulLowS,rfl⟩,plain_complete .ExtMulLowS rfl,rfl⟩
  | ExtMulHighS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.ExtMulHighS,rfl⟩,plain_complete .ExtMulHighS rfl,rfl⟩
  | ExtMulLowU =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.ExtMulLowU,rfl⟩,plain_complete .ExtMulLowU rfl,rfl⟩
  | ExtMulHighU =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.ExtMulHighU,rfl⟩,plain_complete .ExtMulHighU rfl,rfl⟩
  | Swizzle =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.Swizzle,rfl⟩,plain_complete .Swizzle rfl,rfl⟩
  | Shuffle xs =>
    refine ⟨natLists.map .Shuffle,by simp,?_⟩
    exact ⟨xs,natLists_complete xs,rfl⟩
  | NarrowS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.NarrowS,rfl⟩,plain_complete .NarrowS rfl,rfl⟩
  | NarrowU =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.NarrowU,rfl⟩,plain_complete .NarrowU rfl,rfl⟩
  | RelaxedSwizzle =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.RelaxedSwizzle,rfl⟩,plain_complete .RelaxedSwizzle rfl,rfl⟩
  | RelaxedQ15MulRS =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.RelaxedQ15MulRS,rfl⟩,plain_complete .RelaxedQ15MulRS rfl,rfl⟩
  | RelaxedDot =>
    refine ⟨plains.map Subtype.val,List.mem_cons_self,?_⟩
    exact ⟨⟨.RelaxedDot,rfl⟩,plain_complete .RelaxedDot rfl,rfl⟩

theorem plain_i8_legal (op : vibinop) (h : simple op=true) : legal (.V128 (.I8x16 op))=true := by
  cases op <;> simp_all [simple,legal]

def i8 : Audited {op : vbinop_ // legal op=true} :=
  ConstructiveBodyChoice.branches
    (plains.map fun op => ⟨.V128 (.I8x16 op.val),plain_i8_legal op.val op.property⟩)
    [ConstructiveBodyShuffle.indices.map fun xs => ⟨.V128 (.I8x16 (.Shuffle xs.val)),by
      exact List.all_eq_true.mpr (by intro x hx; exact decide_eq_true (xs.property x hx))⟩]

theorem i8_complete (op : vibinop) (h : legal (.V128 (.I8x16 op))=true) :
    Gen.support i8.generator ⟨.V128 (.I8x16 op),h⟩ := by
  apply (ConstructiveBodyChoice.branches_support _ _ _).2
  by_cases hs : simple op=true
  · refine ⟨_,List.mem_cons_self,?_⟩
    exact ⟨⟨op,hs⟩,plain_complete op hs,rfl⟩
  · cases op <;> simp only [simple,Bool.true_eq,not_true_eq_false] at hs
    rename_i xs
    have hx : ∀x∈xs,x<32 := by simpa [legal,List.all_eq_true] using h
    refine ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,?_⟩
    exact ⟨⟨xs,hx⟩,ConstructiveBodyShuffle.indices_complete xs hx,rfl⟩

def otherInteger (make : vibinop → vbinop_) (good : ∀op,legal (make op)=true) :
    Audited {op : vbinop_ // legal op=true} := integers.map fun op => ⟨make op,good op⟩
def otherFloat (make : vfbinop → vbinop_) (good : ∀op,legal (make op)=true) :
    Audited {op : vbinop_ // legal op=true} :=
  (ConstructiveBodyOperatorEnums.generate ConstructiveBodyOperatorEnums.domain_vfbinop).map fun op => ⟨make op,good op⟩

def payloads : Audited {op : vbinop_ // legal op=true} :=
  ConstructiveBodyChoice.branches i8
    [otherInteger (fun op => .V128 (.I16x8 op)) (fun _ => rfl),
     otherInteger (fun op => .V128 (.I32x4 op)) (fun _ => rfl),
     otherInteger (fun op => .V128 (.I64x2 op)) (fun _ => rfl),
     otherFloat (fun op => .V128 (.F32x4 op)) (fun _ => rfl),
     otherFloat (fun op => .V128 (.F64x2 op)) (fun _ => rfl)]

theorem payloads_complete (op : vbinop_) (h : legal op=true) :
    Gen.support payloads.generator ⟨op,h⟩ := by
  apply (ConstructiveBodyChoice.branches_support _ _ _).2
  cases op with | V128 v =>
   cases v with
   | I8x16 v => exact ⟨i8,List.mem_cons_self,i8_complete v h⟩
   | I16x8 v =>
     refine ⟨otherInteger (fun op => .V128 (.I16x8 op)) (fun _ => rfl),by simp,?_⟩
     exact ⟨v,integers_complete v,rfl⟩
   | I32x4 v =>
     refine ⟨otherInteger (fun op => .V128 (.I32x4 op)) (fun _ => rfl),by simp,?_⟩
     exact ⟨v,integers_complete v,rfl⟩
   | I64x2 v =>
     refine ⟨otherInteger (fun op => .V128 (.I64x2 op)) (fun _ => rfl),by simp,?_⟩
     exact ⟨v,integers_complete v,rfl⟩
   | F32x4 v =>
     refine ⟨otherFloat (fun op => .V128 (.F32x4 op)) (fun _ => rfl),by simp,?_⟩
     exact ⟨v,ConstructiveBodyOperatorEnums.generate_support _ v,rfl⟩
   | F64x2 v =>
     refine ⟨otherFloat (fun op => .V128 (.F64x2 op)) (fun _ => rfl),by simp,?_⟩
     exact ⟨v,ConstructiveBodyOperatorEnums.generate_support _ v,rfl⟩

theorem original (c : context) (stack : inferresulttype) (op : vbinop_) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.BINARY» op)⟩)
      n (.success (.of result)) finish) :
    legal op=true ∧ result=ConstructiveBodyControl.effect [.VecT .V128T,.VecT .V128T] [.VecT .V128T] [] ∧ finish=n := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«VEC.BINARY» op) 87 (by decide) rfl (by decide) result n finish).1 h
  have hl : legal op=true := by
    change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:87» c stack (.«VEC.BINARY» op)) n _ finish at hs
    unfold SpecTec.«Instr_ok:clause:87» at hs
    cases hs with | bind_success hg tail =>
     cases hg
     cases tail with | bind_success hu _ => exact ((exact_call op _ _).1 hu).1
  exact ⟨hl,ConstructiveBodyOperatorCalls.effect_unique c stack (.«VEC.BINARY» op) _ result n finish (binary c stack op n hl) h⟩

def production (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  ConstructiveBodyOperatorProductions.production c stack env [.VecT .V128T,.VecT .V128T] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> rfl)
    (by intro t ht; rcases List.mem_singleton.mp ht with rfl; rfl)
    payloads (fun op => .«VEC.BINARY» op.val) (fun op n => binary c stack op.val n op.property)

#print axioms payloads_complete
#print axioms original
end properties.wasm_module_ok.ConstructiveBodyVectorBinaryGeneration
