import properties.wasm_module_ok.ConstructiveBodyConversionTypes
import properties.wasm_module_ok.ConstructiveBodyCertifiedChoice
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyConversionGeneration
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore
open ConstructiveBodyConversionTypes ConstructiveBodyEnvironment ConstructiveBodyProductions

inductive Group where
  | g0
  | g1
  | g2
  | g3
  | g4
  | g5
  | g6
  | g7
  | g8
  | g9
  | g10
  | g11
  deriving DecidableEq

def types : Group → numtype × numtype
  | .g0 => (.I64T,.I32T)
  | .g1 => (.F32T,.I32T)
  | .g2 => (.F64T,.I32T)
  | .g3 => (.I32T,.I64T)
  | .g4 => (.F32T,.I64T)
  | .g5 => (.F64T,.I64T)
  | .g6 => (.I32T,.F32T)
  | .g7 => (.I64T,.F32T)
  | .g8 => (.F64T,.F32T)
  | .g9 => (.I32T,.F64T)
  | .g10 => (.I64T,.F64T)
  | .g11 => (.F32T,.F64T)

def first : Group → cvtop_
  | .g0 => .I32 .WrapI64
  | .g1 => .I32 .TruncSF32
  | .g2 => .I32 .TruncSF64
  | .g3 => .I64 .ExtendSI32
  | .g4 => .I64 .TruncSF32
  | .g5 => .I64 .TruncSF64
  | .g6 => .F32 .ConvertSI32
  | .g7 => .F32 .ConvertSI64
  | .g8 => .F32 .DemoteF64
  | .g9 => .F64 .ConvertSI32
  | .g10 => .F64 .ConvertSI64
  | .g11 => .F64 .PromoteF32

def rest : Group → List cvtop_
  | .g0 => []
  | .g1 => [.I32 .TruncUF32,.I32 .TruncSatSF32,.I32 .TruncSatUF32,.I32 .ReinterpretFloat]
  | .g2 => [.I32 .TruncUF64,.I32 .TruncSatSF64,.I32 .TruncSatUF64]
  | .g3 => [.I64 .ExtendUI32]
  | .g4 => [.I64 .TruncUF32,.I64 .TruncSatSF32,.I64 .TruncSatUF32]
  | .g5 => [.I64 .TruncUF64,.I64 .TruncSatSF64,.I64 .TruncSatUF64,.I64 .ReinterpretFloat]
  | .g6 => [.F32 .ConvertUI32,.F32 .ReinterpretInt]
  | .g7 => [.F32 .ConvertUI64]
  | .g8 => []
  | .g9 => [.F64 .ConvertUI32]
  | .g10 => [.F64 .ConvertUI64,.F64 .ReinterpretInt]
  | .g11 => []

theorem valid (g : Group) (op : cvtop_) (h : op∈first g::rest g) : typeOf op=some (types g) := by
  cases g with
  | g0 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl <;> rfl
  | g1 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl <;> rfl
  | g2 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> rfl
  | g3 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> rfl
  | g4 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> rfl
  | g5 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl <;> rfl
  | g6 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> rfl
  | g7 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> rfl
  | g8 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl <;> rfl
  | g9 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> rfl
  | g10 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> rfl
  | g11 =>
    simp only [first,rest,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl <;> rfl

def payloads (g : Group) : Audited {op : cvtop_ // typeOf op=some (types g)} :=
  ConstructiveBodyCertifiedChoice.choose (first g) (rest g) (valid g)

theorem covered (op : cvtop_) (ts : numtype × numtype) (h : typeOf op=some ts) :
    ∃g,types g=ts ∧ op∈first g::rest g := by
  cases op with
  | I32 op =>
    cases op with
    | ExtendSI32 => cases h
    | ExtendUI32 => cases h
    | WrapI64 => cases h; exact ⟨.g0,rfl,by decide⟩
    | TruncSF32 => cases h; exact ⟨.g1,rfl,by decide⟩
    | TruncUF32 => cases h; exact ⟨.g1,rfl,by decide⟩
    | TruncSF64 => cases h; exact ⟨.g2,rfl,by decide⟩
    | TruncUF64 => cases h; exact ⟨.g2,rfl,by decide⟩
    | TruncSatSF32 => cases h; exact ⟨.g1,rfl,by decide⟩
    | TruncSatUF32 => cases h; exact ⟨.g1,rfl,by decide⟩
    | TruncSatSF64 => cases h; exact ⟨.g2,rfl,by decide⟩
    | TruncSatUF64 => cases h; exact ⟨.g2,rfl,by decide⟩
    | ReinterpretFloat => cases h; exact ⟨.g1,rfl,by decide⟩
  | I64 op =>
    cases op with
    | ExtendSI32 => cases h; exact ⟨.g3,rfl,by decide⟩
    | ExtendUI32 => cases h; exact ⟨.g3,rfl,by decide⟩
    | WrapI64 => cases h
    | TruncSF32 => cases h; exact ⟨.g4,rfl,by decide⟩
    | TruncUF32 => cases h; exact ⟨.g4,rfl,by decide⟩
    | TruncSF64 => cases h; exact ⟨.g5,rfl,by decide⟩
    | TruncUF64 => cases h; exact ⟨.g5,rfl,by decide⟩
    | TruncSatSF32 => cases h; exact ⟨.g4,rfl,by decide⟩
    | TruncSatUF32 => cases h; exact ⟨.g4,rfl,by decide⟩
    | TruncSatSF64 => cases h; exact ⟨.g5,rfl,by decide⟩
    | TruncSatUF64 => cases h; exact ⟨.g5,rfl,by decide⟩
    | ReinterpretFloat => cases h; exact ⟨.g5,rfl,by decide⟩
  | F32 op =>
    cases op with
    | ConvertSI32 => cases h; exact ⟨.g6,rfl,by decide⟩
    | ConvertUI32 => cases h; exact ⟨.g6,rfl,by decide⟩
    | ConvertSI64 => cases h; exact ⟨.g7,rfl,by decide⟩
    | ConvertUI64 => cases h; exact ⟨.g7,rfl,by decide⟩
    | PromoteF32 => cases h
    | DemoteF64 => cases h; exact ⟨.g8,rfl,by decide⟩
    | ReinterpretInt => cases h; exact ⟨.g6,rfl,by decide⟩
  | F64 op =>
    cases op with
    | ConvertSI32 => cases h; exact ⟨.g9,rfl,by decide⟩
    | ConvertUI32 => cases h; exact ⟨.g9,rfl,by decide⟩
    | ConvertSI64 => cases h; exact ⟨.g10,rfl,by decide⟩
    | ConvertUI64 => cases h; exact ⟨.g10,rfl,by decide⟩
    | PromoteF32 => cases h; exact ⟨.g11,rfl,by decide⟩
    | DemoteF64 => cases h
    | ReinterpretInt => cases h; exact ⟨.g10,rfl,by decide⟩

theorem payloads_complete (g : Group) (op : cvtop_) (h : op∈first g::rest g) :
    Gen.support (payloads g).generator ⟨op,valid g op h⟩ :=
  ConstructiveBodyCertifiedChoice.complete _ _ _ _ h

theorem original (c : context) (stack : inferresulttype) (op : cvtop_) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.CONVERT op)⟩)
      n (.success (.of result)) finish) :
    ∃g,op∈first g::rest g ∧
      result=ConstructiveBodyControl.effect [.NumT (types g).1] [.NumT (types g).2] [] ∧ finish=n := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.CONVERT op) 83 (by decide) rfl (by decide) result n finish).1 h
  have ht : ∃ts,typeOf op=some ts := by
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:83» c stack (.CONVERT op)) n _ finish at hs
    unfold SpecTec.«Instr_ok:clause:83» at hs
    cases hs with | bind_success hg tail =>
     cases hg
     cases tail with | bind_success ht _ => exact ⟨_,((type_exact op _ _ _).1 ht).1⟩
  obtain ⟨ts,ht⟩ := ht
  obtain ⟨g,he,hg⟩ := covered op ts ht
  rw [←he] at ht
  exact ⟨g,hg,ConstructiveBodyOperatorCalls.effect_unique c stack (.CONVERT op) _ result n finish (convert c stack op (types g) n ht) h⟩

def production (c : context) (stack : inferresulttype) (env : Env c) (g : Group) : Production c stack :=
  ConstructiveBodyOperatorProductions.production c stack env [.NumT (types g).1] [.NumT (types g).2]
    (by intro t ht; rcases List.mem_singleton.mp ht with rfl; rfl)
    (by intro t ht; rcases List.mem_singleton.mp ht with rfl; rfl)
    (payloads g) (fun op => .CONVERT op.val)
    (fun op n => convert c stack op.val (types g) n op.property)

def groups : List Group := [.g0,.g1,.g2,.g3,.g4,.g5,.g6,.g7,.g8,.g9,.g10,.g11]
theorem mem_groups (g : Group) : g∈groups := by cases g <;> decide

def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  groups.map (production c stack env)

#print axioms original
#print axioms payloads_complete
end properties.wasm_module_ok.ConstructiveBodyConversionGeneration
