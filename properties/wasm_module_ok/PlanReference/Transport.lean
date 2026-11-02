import Lean
import «properties».«wasm_module_ok».«PlanReference».«Helpers»

set_option autoImplicit false
set_option linter.unusedVariables false

namespace «properties».«wasm_module_ok».«PlanReference».«ContractTransport»



deriving instance _root_.Lean.ToJson for _root_.SpecTec.«final»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«typevar»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«mut»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«packtype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«numtype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«null»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vectype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«deftype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«heaptype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«reftype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«valtype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«storagetype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«fieldtype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«structtype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«arraytype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«functype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«strtype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«subtype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«rectype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«globaltype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«blocktype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«catch»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«extension»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«memop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«packshape»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vextension»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«void»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«initop_»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«externop_»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«fmag»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«f32»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«f64»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«op»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«itestop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«ftestop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«irelop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«frelop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«iunop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«funop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«ibinop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«fbinop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«icvtop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«fcvtop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vecop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vitestop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«laneop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«viunop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vfunop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vibinop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vfbinop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«viternop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vfternop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«virelop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vfrelop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vicvtop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vfcvtop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vishiftop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vibitmaskop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vvtestop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vvunop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vvbinop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vvternop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vnsplatop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vnextractop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«vnreplaceop»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«instr»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«global»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«addrtype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«limits»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«tabletype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«table»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«memtype»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«memory»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«tag»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«local»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«func»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«start»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«active»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«elemmode»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«elem»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«datamode»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«data»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«importdesc»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«import»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«exportdesc»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«export»
deriving instance _root_.Lean.ToJson for _root_.SpecTec.«module»
private abbrev requiredToJson0 : _root_.Lean.ToJson (_root_.SpecTec.«module») := inferInstance
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«final»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«typevar»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«mut»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«packtype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«numtype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«null»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vectype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«deftype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«heaptype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«reftype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«valtype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«storagetype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«fieldtype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«structtype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«arraytype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«functype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«strtype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«subtype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«rectype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«globaltype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«blocktype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«catch»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«extension»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«memop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«packshape»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vextension»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«void»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«initop_»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«externop_»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«fmag»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«f32»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«f64»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«op»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«itestop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«ftestop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«irelop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«frelop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«iunop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«funop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«ibinop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«fbinop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«icvtop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«fcvtop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vecop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vitestop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«laneop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«viunop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vfunop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vibinop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vfbinop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«viternop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vfternop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«virelop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vfrelop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vicvtop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vfcvtop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vishiftop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vibitmaskop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vvtestop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vvunop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vvbinop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vvternop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vnsplatop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vnextractop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«vnreplaceop»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«instr»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«global»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«addrtype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«limits»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«tabletype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«table»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«memtype»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«memory»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«tag»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«local»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«func»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«start»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«active»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«elemmode»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«elem»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«datamode»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«data»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«importdesc»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«import»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«exportdesc»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«export»
deriving instance _root_.Lean.FromJson for _root_.SpecTec.«module»
private abbrev requiredFromJson0 : _root_.Lean.FromJson (_root_.SpecTec.«module») := inferInstance

abbrev Type0 := _root_.SpecTec.«module»
abbrev Type1 := (_root_.List _root_.SpecTec.«type»)
abbrev Type2 := _root_.SpecTec.«type»
abbrev Type3 := _root_.SpecTec.«rectype»
abbrev Type4 := (_root_.List _root_.SpecTec.«subtype»)
abbrev Type5 := _root_.SpecTec.«subtype»
abbrev Type6 := _root_.SpecTec.«final»
abbrev Type7 := (_root_.List _root_.SpecTec.«heaptype»)
abbrev Type8 := _root_.SpecTec.«heaptype»
abbrev Type9 := _root_.SpecTec.«typevar»
abbrev Type10 := _root_.SpecTec.«typeidx»
abbrev Type11 := _root_.SpecTec.«idx»
abbrev Type12 := _root_.Nat
abbrev Type13 := _root_.SpecTec.«deftype»
abbrev Type14 := _root_.SpecTec.«n»
abbrev Type15 := _root_.SpecTec.«strtype»
abbrev Type16 := _root_.SpecTec.«structtype»
abbrev Type17 := (_root_.List _root_.SpecTec.«fieldtype»)
abbrev Type18 := _root_.SpecTec.«fieldtype»
abbrev Type19 := _root_.SpecTec.«mut»
abbrev Type20 := _root_.SpecTec.«storagetype»
abbrev Type21 := _root_.SpecTec.«valtype»
abbrev Type22 := _root_.SpecTec.«numtype»
abbrev Type23 := _root_.SpecTec.«vectype»
abbrev Type24 := _root_.SpecTec.«reftype»
abbrev Type25 := _root_.SpecTec.«null»
abbrev Type26 := _root_.SpecTec.«packtype»
abbrev Type27 := _root_.SpecTec.«arraytype»
abbrev Type28 := _root_.SpecTec.«functype»
abbrev Type29 := _root_.SpecTec.«resulttype»
abbrev Type30 := (_root_.List _root_.SpecTec.«valtype»)
abbrev Type31 := (_root_.List _root_.SpecTec.«global»)
abbrev Type32 := _root_.SpecTec.«global»
abbrev Type33 := _root_.SpecTec.«globaltype»
abbrev Type34 := _root_.SpecTec.«const»
abbrev Type35 := (_root_.List _root_.SpecTec.«instr»)
abbrev Type36 := _root_.SpecTec.«instr»
abbrev Type37 := (_root_.Option (_root_.List _root_.SpecTec.«valtype»))
abbrev Type38 := _root_.SpecTec.«blocktype»
abbrev Type39 := (_root_.Option _root_.SpecTec.«valtype»)
abbrev Type40 := _root_.SpecTec.«labelidx»
abbrev Type41 := (_root_.List _root_.SpecTec.«labelidx»)
abbrev Type42 := _root_.SpecTec.«funcidx»
abbrev Type43 := _root_.SpecTec.«tableidx»
abbrev Type44 := _root_.SpecTec.«tagidx»
abbrev Type45 := (_root_.List _root_.SpecTec.«catch»)
abbrev Type46 := _root_.SpecTec.«catch»
abbrev Type47 := _root_.SpecTec.«localidx»
abbrev Type48 := _root_.SpecTec.«globalidx»
abbrev Type49 := _root_.SpecTec.«elemidx»
abbrev Type50 := _root_.SpecTec.«memidx»
abbrev Type51 := _root_.SpecTec.«loadop_»
abbrev Type52 := (_root_.SpecTec.«memop» _root_.SpecTec.«numtype» (_root_.Option (_root_.SpecTec.«packtype» × _root_.SpecTec.«extension»)))
abbrev Type53 := (_root_.Option (_root_.SpecTec.«packtype» × _root_.SpecTec.«extension»))
abbrev Type54 := (_root_.SpecTec.«packtype» × _root_.SpecTec.«extension»)
abbrev Type55 := _root_.SpecTec.«extension»
abbrev Type56 := _root_.SpecTec.«u32»
abbrev Type57 := _root_.SpecTec.«u64»
abbrev Type58 := _root_.SpecTec.«storeop_»
abbrev Type59 := (_root_.SpecTec.«memop» _root_.SpecTec.«numtype» (_root_.Option _root_.SpecTec.«packtype»))
abbrev Type60 := (_root_.Option _root_.SpecTec.«packtype»)
abbrev Type61 := _root_.SpecTec.«vloadop_»
abbrev Type62 := (_root_.SpecTec.«memop» _root_.SpecTec.«vectype» (_root_.Option (_root_.SpecTec.«packtype» × _root_.SpecTec.«vextension»)))
abbrev Type63 := (_root_.Option (_root_.SpecTec.«packtype» × _root_.SpecTec.«vextension»))
abbrev Type64 := (_root_.SpecTec.«packtype» × _root_.SpecTec.«vextension»)
abbrev Type65 := _root_.SpecTec.«vextension»
abbrev Type66 := _root_.SpecTec.«packshape»
abbrev Type67 := _root_.SpecTec.«vstoreop_»
abbrev Type68 := (_root_.SpecTec.«memop» _root_.SpecTec.«vectype» _root_.SpecTec.«void»)
abbrev Type69 := _root_.SpecTec.«void»
abbrev Type70 := _root_.SpecTec.«vlaneop_»
abbrev Type71 := (_root_.SpecTec.«memop» _root_.SpecTec.«vectype» _root_.SpecTec.«packtype»)
abbrev Type72 := _root_.Int
abbrev Type73 := _root_.SpecTec.«dataidx»
abbrev Type74 := _root_.SpecTec.«initop_»
abbrev Type75 := (_root_.Option _root_.SpecTec.«extension»)
abbrev Type76 := _root_.SpecTec.«externop_»
abbrev Type77 := _root_.SpecTec.«num_»
abbrev Type78 := (_root_.SpecTec.«op» _root_.SpecTec.«i32» _root_.SpecTec.«i64» _root_.SpecTec.«f32» _root_.SpecTec.«f64»)
abbrev Type79 := _root_.SpecTec.«i32»
abbrev Type80 := _root_.SpecTec.«i64»
abbrev Type81 := _root_.SpecTec.«f32»
abbrev Type82 := _root_.SpecTec.«f32mag»
abbrev Type83 := _root_.SpecTec.«fmag»
abbrev Type84 := _root_.SpecTec.«m»
abbrev Type85 := _root_.SpecTec.«exp»
abbrev Type86 := _root_.SpecTec.«f64»
abbrev Type87 := _root_.SpecTec.«f64mag»
abbrev Type88 := _root_.SpecTec.«testop_»
abbrev Type89 := (_root_.SpecTec.«op» _root_.SpecTec.«itestop» _root_.SpecTec.«itestop» _root_.SpecTec.«ftestop» _root_.SpecTec.«ftestop»)
abbrev Type90 := _root_.SpecTec.«itestop»
abbrev Type91 := _root_.SpecTec.«ftestop»
abbrev Type92 := _root_.SpecTec.«relop_»
abbrev Type93 := (_root_.SpecTec.«op» _root_.SpecTec.«irelop» _root_.SpecTec.«irelop» _root_.SpecTec.«frelop» _root_.SpecTec.«frelop»)
abbrev Type94 := _root_.SpecTec.«irelop»
abbrev Type95 := _root_.SpecTec.«frelop»
abbrev Type96 := _root_.SpecTec.«unop_»
abbrev Type97 := (_root_.SpecTec.«op» _root_.SpecTec.«iunop» _root_.SpecTec.«iunop» _root_.SpecTec.«funop» _root_.SpecTec.«funop»)
abbrev Type98 := _root_.SpecTec.«iunop»
abbrev Type99 := _root_.SpecTec.«funop»
abbrev Type100 := _root_.SpecTec.«binop_»
abbrev Type101 := (_root_.SpecTec.«op» _root_.SpecTec.«ibinop» _root_.SpecTec.«ibinop» _root_.SpecTec.«fbinop» _root_.SpecTec.«fbinop»)
abbrev Type102 := _root_.SpecTec.«ibinop»
abbrev Type103 := _root_.SpecTec.«fbinop»
abbrev Type104 := _root_.SpecTec.«cvtop_»
abbrev Type105 := (_root_.SpecTec.«op» _root_.SpecTec.«icvtop» _root_.SpecTec.«icvtop» _root_.SpecTec.«fcvtop» _root_.SpecTec.«fcvtop»)
abbrev Type106 := _root_.SpecTec.«icvtop»
abbrev Type107 := _root_.SpecTec.«fcvtop»
abbrev Type108 := _root_.SpecTec.«vec_»
abbrev Type109 := (_root_.SpecTec.«vecop» _root_.SpecTec.«v128»)
abbrev Type110 := _root_.SpecTec.«v128»
abbrev Type111 := _root_.SpecTec.«vtestop_»
abbrev Type112 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vtestop»)
abbrev Type113 := _root_.SpecTec.«vtestop»
abbrev Type114 := (_root_.SpecTec.«laneop» _root_.SpecTec.«vitestop» _root_.SpecTec.«vitestop» _root_.SpecTec.«vitestop» _root_.SpecTec.«vitestop» _root_.SpecTec.«void» _root_.SpecTec.«void»)
abbrev Type115 := _root_.SpecTec.«vitestop»
abbrev Type116 := _root_.SpecTec.«vunop_»
abbrev Type117 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vunop»)
abbrev Type118 := _root_.SpecTec.«vunop»
abbrev Type119 := (_root_.SpecTec.«laneop» _root_.SpecTec.«viunop» _root_.SpecTec.«viunop» _root_.SpecTec.«viunop» _root_.SpecTec.«viunop» _root_.SpecTec.«vfunop» _root_.SpecTec.«vfunop»)
abbrev Type120 := _root_.SpecTec.«viunop»
abbrev Type121 := _root_.SpecTec.«vfunop»
abbrev Type122 := _root_.SpecTec.«vbinop_»
abbrev Type123 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vbinop»)
abbrev Type124 := _root_.SpecTec.«vbinop»
abbrev Type125 := (_root_.SpecTec.«laneop» _root_.SpecTec.«vibinop» _root_.SpecTec.«vibinop» _root_.SpecTec.«vibinop» _root_.SpecTec.«vibinop» _root_.SpecTec.«vfbinop» _root_.SpecTec.«vfbinop»)
abbrev Type126 := _root_.SpecTec.«vibinop»
abbrev Type127 := (_root_.List _root_.Nat)
abbrev Type128 := _root_.SpecTec.«vfbinop»
abbrev Type129 := _root_.SpecTec.«vternop_»
abbrev Type130 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vternop»)
abbrev Type131 := _root_.SpecTec.«vternop»
abbrev Type132 := (_root_.SpecTec.«laneop» _root_.SpecTec.«viternop» _root_.SpecTec.«viternop» _root_.SpecTec.«viternop» _root_.SpecTec.«viternop» _root_.SpecTec.«vfternop» _root_.SpecTec.«vfternop»)
abbrev Type133 := _root_.SpecTec.«viternop»
abbrev Type134 := _root_.SpecTec.«vfternop»
abbrev Type135 := _root_.SpecTec.«vrelop_»
abbrev Type136 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vrelop»)
abbrev Type137 := _root_.SpecTec.«vrelop»
abbrev Type138 := (_root_.SpecTec.«laneop» _root_.SpecTec.«virelop» _root_.SpecTec.«virelop» _root_.SpecTec.«virelop» _root_.SpecTec.«virelop» _root_.SpecTec.«vfrelop» _root_.SpecTec.«vfrelop»)
abbrev Type139 := _root_.SpecTec.«virelop»
abbrev Type140 := _root_.SpecTec.«vfrelop»
abbrev Type141 := _root_.SpecTec.«vcvtop_»
abbrev Type142 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vcvtop»)
abbrev Type143 := _root_.SpecTec.«vcvtop»
abbrev Type144 := (_root_.SpecTec.«laneop» _root_.SpecTec.«vicvtop» _root_.SpecTec.«vicvtop» _root_.SpecTec.«vicvtop» _root_.SpecTec.«vicvtop» _root_.SpecTec.«vfcvtop» _root_.SpecTec.«vfcvtop»)
abbrev Type145 := _root_.SpecTec.«vicvtop»
abbrev Type146 := _root_.SpecTec.«vfcvtop»
abbrev Type147 := _root_.SpecTec.«vshiftop_»
abbrev Type148 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vshiftop»)
abbrev Type149 := _root_.SpecTec.«vshiftop»
abbrev Type150 := (_root_.SpecTec.«laneop» _root_.SpecTec.«vishiftop» _root_.SpecTec.«vishiftop» _root_.SpecTec.«vishiftop» _root_.SpecTec.«vishiftop» _root_.SpecTec.«void» _root_.SpecTec.«void»)
abbrev Type151 := _root_.SpecTec.«vishiftop»
abbrev Type152 := _root_.SpecTec.«vbitmaskop_»
abbrev Type153 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vbitmaskop»)
abbrev Type154 := _root_.SpecTec.«vbitmaskop»
abbrev Type155 := (_root_.SpecTec.«laneop» _root_.SpecTec.«vibitmaskop» _root_.SpecTec.«vibitmaskop» _root_.SpecTec.«vibitmaskop» _root_.SpecTec.«vibitmaskop» _root_.SpecTec.«void» _root_.SpecTec.«void»)
abbrev Type156 := _root_.SpecTec.«vibitmaskop»
abbrev Type157 := _root_.SpecTec.«vvtestop_»
abbrev Type158 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vvtestop»)
abbrev Type159 := _root_.SpecTec.«vvtestop»
abbrev Type160 := _root_.SpecTec.«vvunop_»
abbrev Type161 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vvunop»)
abbrev Type162 := _root_.SpecTec.«vvunop»
abbrev Type163 := _root_.SpecTec.«vvbinop_»
abbrev Type164 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vvbinop»)
abbrev Type165 := _root_.SpecTec.«vvbinop»
abbrev Type166 := _root_.SpecTec.«vvternop_»
abbrev Type167 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vvternop»)
abbrev Type168 := _root_.SpecTec.«vvternop»
abbrev Type169 := _root_.SpecTec.«vsplatop_»
abbrev Type170 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vsplatop»)
abbrev Type171 := _root_.SpecTec.«vsplatop»
abbrev Type172 := (_root_.SpecTec.«laneop» _root_.SpecTec.«vnsplatop» _root_.SpecTec.«vnsplatop» _root_.SpecTec.«vnsplatop» _root_.SpecTec.«vnsplatop» _root_.SpecTec.«vnsplatop» _root_.SpecTec.«vnsplatop»)
abbrev Type173 := _root_.SpecTec.«vnsplatop»
abbrev Type174 := _root_.SpecTec.«vextractop_»
abbrev Type175 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vextractop»)
abbrev Type176 := _root_.SpecTec.«vextractop»
abbrev Type177 := (_root_.SpecTec.«laneop» (_root_.SpecTec.«vnextractop» _root_.SpecTec.«extension») (_root_.SpecTec.«vnextractop» _root_.SpecTec.«extension») (_root_.SpecTec.«vnextractop» _root_.SpecTec.«void») (_root_.SpecTec.«vnextractop» _root_.SpecTec.«void») (_root_.SpecTec.«vnextractop» _root_.SpecTec.«void») (_root_.SpecTec.«vnextractop» _root_.SpecTec.«void»))
abbrev Type178 := (_root_.SpecTec.«vnextractop» _root_.SpecTec.«extension»)
abbrev Type179 := (_root_.Nat × _root_.SpecTec.«extension»)
abbrev Type180 := (_root_.SpecTec.«vnextractop» _root_.SpecTec.«void»)
abbrev Type181 := (_root_.Nat × _root_.SpecTec.«void»)
abbrev Type182 := _root_.SpecTec.«vreplaceop_»
abbrev Type183 := (_root_.SpecTec.«vecop» _root_.SpecTec.«vreplaceop»)
abbrev Type184 := _root_.SpecTec.«vreplaceop»
abbrev Type185 := (_root_.SpecTec.«laneop» _root_.SpecTec.«vnreplaceop» _root_.SpecTec.«vnreplaceop» _root_.SpecTec.«vnreplaceop» _root_.SpecTec.«vnreplaceop» _root_.SpecTec.«vnreplaceop» _root_.SpecTec.«vnreplaceop»)
abbrev Type186 := _root_.SpecTec.«vnreplaceop»
abbrev Type187 := (_root_.List _root_.SpecTec.«table»)
abbrev Type188 := _root_.SpecTec.«table»
abbrev Type189 := _root_.SpecTec.«tabletype»
abbrev Type190 := _root_.SpecTec.«addrtype»
abbrev Type191 := _root_.SpecTec.«limits»
abbrev Type192 := (_root_.Option _root_.SpecTec.«u64»)
abbrev Type193 := (_root_.List _root_.SpecTec.«memory»)
abbrev Type194 := _root_.SpecTec.«memory»
abbrev Type195 := _root_.SpecTec.«memtype»
abbrev Type196 := (_root_.List _root_.SpecTec.«tag»)
abbrev Type197 := _root_.SpecTec.«tag»
abbrev Type198 := (_root_.List _root_.SpecTec.«func»)
abbrev Type199 := _root_.SpecTec.«func»
abbrev Type200 := (_root_.List _root_.SpecTec.«local»)
abbrev Type201 := _root_.SpecTec.«local»
abbrev Type202 := (_root_.Option _root_.SpecTec.«start»)
abbrev Type203 := _root_.SpecTec.«start»
abbrev Type204 := (_root_.List _root_.SpecTec.«elem»)
abbrev Type205 := _root_.SpecTec.«elem»
abbrev Type206 := (_root_.List _root_.SpecTec.«const»)
abbrev Type207 := _root_.SpecTec.«elemmode»
abbrev Type208 := _root_.SpecTec.«active»
abbrev Type209 := (_root_.List _root_.SpecTec.«data»)
abbrev Type210 := _root_.SpecTec.«data»
abbrev Type211 := _root_.String
abbrev Type212 := _root_.SpecTec.«datamode»
abbrev Type213 := (_root_.List _root_.SpecTec.«import»)
abbrev Type214 := _root_.SpecTec.«import»
abbrev Type215 := _root_.SpecTec.«name»
abbrev Type216 := (_root_.List _root_.SpecTec.«char»)
abbrev Type217 := _root_.SpecTec.«char»
abbrev Type218 := _root_.SpecTec.«importdesc»
abbrev Type219 := (_root_.List _root_.SpecTec.«export»)
abbrev Type220 := _root_.SpecTec.«export»
abbrev Type221 := _root_.SpecTec.«exportdesc»
abbrev Type222 := _root_.Bool

end «properties».«wasm_module_ok».«PlanReference».«ContractTransport»
