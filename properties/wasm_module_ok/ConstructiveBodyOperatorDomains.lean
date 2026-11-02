import properties.wasm_module_ok.ConstructiveBodyOperatorEnums
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyOperatorDomains
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore ConstructiveBodyOperatorEnums

def operators {A B C D : Type} (dA : Domain A) (dB : Domain B) (dC : Domain C) (dD : Domain D) : Domain (op A B C D) where
  first := .I32 dA.first
  rest := dA.rest.map (.I32) ++ (dB.first::dB.rest).map (.I64) ++ (dC.first::dC.rest).map (.F32) ++ (dD.first::dD.rest).map (.F64)
  complete := by
    intro a
    cases a with
    | I32 a => simpa using dA.complete a
    | I64 a => simpa using dB.complete a
    | F32 a => simpa using dC.complete a
    | F64 a => simpa using dD.complete a

def lanes {A B C D E F : Type} (dA : Domain A) (dB : Domain B) (dC : Domain C) (dD : Domain D) (dE : Domain E) (dF : Domain F) : Domain (laneop A B C D E F) where
  first := .I8x16 dA.first
  rest := dA.rest.map (.I8x16) ++ (dB.first::dB.rest).map (.I16x8) ++ (dC.first::dC.rest).map (.I32x4) ++ (dD.first::dD.rest).map (.I64x2) ++ (dE.first::dE.rest).map (.F32x4) ++ (dF.first::dF.rest).map (.F64x2)
  complete := by
    intro a
    cases a with
    | I8x16 a => simpa using dA.complete a
    | I16x8 a => simpa using dB.complete a
    | I32x4 a => simpa using dC.complete a
    | I64x2 a => simpa using dD.complete a
    | F32x4 a => simpa using dE.complete a
    | F64x2 a => simpa using dF.complete a

def vectors {A : Type} (d : Domain A) : Domain (vecop A) where
  first := .V128 d.first
  rest := d.rest.map .V128
  complete := by
    intro a; cases a with
    | V128 a => simpa using d.complete a

def tests : Domain testop_ :=
  ⟨.I32 .Eqz,[.I64 .Eqz],by intro a; cases a <;> rename_i v <;> cases v <;> simp⟩
def comparisons : Domain relop_ := operators domain_irelop domain_irelop domain_frelop domain_frelop
def binaries : Domain binop_ := operators domain_ibinop domain_ibinop domain_fbinop domain_fbinop
def vec_tests : Domain vtestop_ := vectors (lanes domain_vitestop domain_vitestop domain_vitestop domain_vitestop domain_void domain_void)
def vec_unaries : Domain vunop_ := vectors (lanes domain_viunop domain_viunop domain_viunop domain_viunop domain_vfunop domain_vfunop)
def vec_ternaries : Domain vternop_ := vectors (lanes domain_viternop domain_viternop domain_viternop domain_viternop domain_vfternop domain_vfternop)
def vec_comparisons : Domain vrelop_ := vectors (lanes domain_virelop domain_virelop domain_virelop domain_virelop domain_vfrelop domain_vfrelop)
def vec_conversions : Domain vcvtop_ := vectors (lanes domain_vicvtop domain_vicvtop domain_vicvtop domain_vicvtop domain_vfcvtop domain_vfcvtop)
def vec_shifts : Domain vshiftop_ := vectors (lanes domain_vishiftop domain_vishiftop domain_vishiftop domain_vishiftop domain_void domain_void)
def vec_bitmasks : Domain vbitmaskop_ := vectors (lanes domain_vibitmaskop domain_vibitmaskop domain_vibitmaskop domain_vibitmaskop domain_void domain_void)
def vec_splats : Domain vsplatop_ := vectors (lanes domain_vnsplatop domain_vnsplatop domain_vnsplatop domain_vnsplatop domain_vnsplatop domain_vnsplatop)
def vvtestops : Domain vvtestop_ := vectors domain_vvtestop
def vvunops : Domain vvunop_ := vectors domain_vvunop
def vvbinops : Domain vvbinop_ := vectors domain_vvbinop
def vvternops : Domain vvternop_ := vectors domain_vvternop

#print axioms lanes
end properties.wasm_module_ok.ConstructiveBodyOperatorDomains
