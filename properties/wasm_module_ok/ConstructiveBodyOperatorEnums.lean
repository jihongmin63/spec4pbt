import properties.wasm_module_ok.ConstructiveBodyChoice
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyOperatorEnums
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore

structure Domain (α : Type) where
  first : α
  rest : List α
  complete : ∀a,a∈first::rest

def generate {α : Type} (d : Domain α) : Audited α :=
  ConstructiveBodyChoice.branches (Audited.pure d.first) (d.rest.map Audited.pure)

theorem generate_support {α : Type} (d : Domain α) (a : α) : Gen.support (generate d).generator a := by
  apply (ConstructiveBodyChoice.branches_support _ _ _).2
  rcases List.mem_cons.mp (d.complete a) with he|hm
  · subst a; exact ⟨Audited.pure d.first,List.mem_cons_self,rfl⟩
  · exact ⟨Audited.pure a,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,hm,rfl⟩),rfl⟩

def domain_ibinop : Domain ibinop :=
  ⟨.IAdd,[.ISub,.IMul,.IDivS,.IDivU,.IRemS,.IRemU,.IAnd,.IOr,.IXor,.IShl,.IShrS,.IShrU,.IRotl,.IRotr],by intro a; cases a <;> simp⟩

def domain_fbinop : Domain fbinop :=
  ⟨.FAdd,[.FSub,.FMul,.FDiv,.FMin,.FMax,.FCopysign],by intro a; cases a <;> simp⟩

def domain_irelop : Domain irelop :=
  ⟨.Eq,[.Ne,.LtS,.LtU,.GtS,.GtU,.LeS,.LeU,.GeS,.GeU],by intro a; cases a <;> simp⟩

def domain_frelop : Domain frelop :=
  ⟨.Eq,[.Ne,.Lt,.Gt,.Le,.Ge],by intro a; cases a <;> simp⟩

def domain_funop : Domain funop :=
  ⟨.Neg,[.Abs,.Ceil,.Floor,.Trunc,.Nearest,.Sqrt],by intro a; cases a <;> simp⟩

def domain_itestop : Domain itestop :=
  ⟨.Eqz,[],by intro a; cases a <;> simp⟩

def domain_icvtop : Domain icvtop :=
  ⟨.ExtendSI32,[.ExtendUI32,.WrapI64,.TruncSF32,.TruncUF32,.TruncSF64,.TruncUF64,.TruncSatSF32,.TruncSatUF32,.TruncSatSF64,.TruncSatUF64,.ReinterpretFloat],by intro a; cases a <;> simp⟩

def domain_fcvtop : Domain fcvtop :=
  ⟨.ConvertSI32,[.ConvertUI32,.ConvertSI64,.ConvertUI64,.PromoteF32,.DemoteF64,.ReinterpretInt],by intro a; cases a <;> simp⟩

def domain_void : Domain void :=
  ⟨.VOID,[],by intro a; cases a <;> simp⟩

def domain_vitestop : Domain vitestop :=
  ⟨.AllTrue,[],by intro a; cases a <;> simp⟩

def domain_viunop : Domain viunop :=
  ⟨.Abs,[.Neg,.Popcnt],by intro a; cases a <;> simp⟩

def domain_vfunop : Domain vfunop :=
  ⟨.Abs,[.Neg,.Sqrt,.Ceil,.Floor,.Trunc,.Nearest],by intro a; cases a <;> simp⟩

def domain_vfbinop : Domain vfbinop :=
  ⟨.Add,[.Sub,.Mul,.Div,.Min,.Max,.Pmin,.Pmax,.RelaxedMin,.RelaxedMax],by intro a; cases a <;> simp⟩

def domain_viternop : Domain viternop :=
  ⟨.RelaxedLaneselect,[.RelaxedDotAdd],by intro a; cases a <;> simp⟩

def domain_vfternop : Domain vfternop :=
  ⟨.RelaxedMadd,[.RelaxedNmadd],by intro a; cases a <;> simp⟩

def domain_virelop : Domain virelop :=
  ⟨.Eq,[.Ne,.LtS,.LtU,.LeS,.LeU,.GtS,.GtU,.GeS,.GeU],by intro a; cases a <;> simp⟩

def domain_vfrelop : Domain vfrelop :=
  ⟨.Eq,[.Ne,.Lt,.Le,.Gt,.Ge],by intro a; cases a <;> simp⟩

def domain_vicvtop : Domain vicvtop :=
  ⟨.ExtendLowS,[.ExtendLowU,.ExtendHighS,.ExtendHighU,.ExtAddPairwiseS,.ExtAddPairwiseU,.TruncSatSF32x4,.TruncSatUF32x4,.TruncSatSZeroF64x2,.TruncSatUZeroF64x2,.RelaxedTruncSF32x4,.RelaxedTruncUF32x4,.RelaxedTruncSZeroF64x2,.RelaxedTruncUZeroF64x2],by intro a; cases a <;> simp⟩

def domain_vfcvtop : Domain vfcvtop :=
  ⟨.DemoteZeroF64x2,[.PromoteLowF32x4,.ConvertSI32x4,.ConvertUI32x4],by intro a; cases a <;> simp⟩

def domain_vishiftop : Domain vishiftop :=
  ⟨.Shl,[.ShrS,.ShrU],by intro a; cases a <;> simp⟩

def domain_vibitmaskop : Domain vibitmaskop :=
  ⟨.Bitmask,[],by intro a; cases a <;> simp⟩

def domain_vvtestop : Domain vvtestop :=
  ⟨.AnyTrue,[],by intro a; cases a <;> simp⟩

def domain_vvunop : Domain vvunop :=
  ⟨.Not,[],by intro a; cases a <;> simp⟩

def domain_vvbinop : Domain vvbinop :=
  ⟨.And,[.Or,.Xor,.AndNot],by intro a; cases a <;> simp⟩

def domain_vvternop : Domain vvternop :=
  ⟨.Bitselect,[],by intro a; cases a <;> simp⟩

def domain_vnsplatop : Domain vnsplatop :=
  ⟨.Splat,[],by intro a; cases a <;> simp⟩

def domain_extension : Domain extension :=
  ⟨.SX,[.ZX],by intro a; cases a <;> simp⟩

def domain_packtype : Domain packtype :=
  ⟨.I8,[.I16,.I32,.I64],by intro a; cases a <;> simp⟩

def domain_externop_ : Domain externop_ :=
  ⟨.Internalize,[.Externalize],by intro a; cases a <;> simp⟩

def domain_initop_ : Domain initop_ :=
  ⟨.Explicit,[.Implicit],by intro a; cases a <;> simp⟩

def domain_numtype : Domain numtype :=
  ⟨.I32T,[.I64T,.F32T,.F64T],by intro a; cases a <;> simp⟩

def domain_addrtype : Domain addrtype :=
  ⟨.I32AT,[.I64AT],by intro a; cases a <;> simp⟩

#print axioms generate_support
end properties.wasm_module_ok.ConstructiveBodyOperatorEnums
