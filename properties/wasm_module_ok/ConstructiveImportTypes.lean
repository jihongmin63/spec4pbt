import properties.wasm_module_ok.ConstructiveLimits
import properties.wasm_module_ok.ImportValidation

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveImportTypes
open SpecTec properties.wasm_module_ok
open ConstructiveTypeAtoms ConstructiveLimits

def globals (c : context) : Gen globaltype := do
  let value ← valtypes c
  Gen.pick (pure (.GlobalT .Cons value)) (pure (.GlobalT .Var value))

theorem globals_support (c : context) (gt : globaltype) :
    Gen.support (globals c) gt ↔ GlobaltypeValidation.globaltypeValid c gt = true := by
  cases gt with
  | GlobalT mu v => cases mu <;> simp [globals,GlobaltypeValidation.globaltypeValid]

theorem globals_finite (c : context) : FiniteConstruction (globals c) :=
  ⟨valtypes_finite c,fun _ => ⟨trivial,trivial⟩⟩

def tables (c : context) : Gen tabletype := do
  let reference ← reftypes c
  Gen.pick
    ((fun lim => tabletype.TableT .I32AT lim reference) <$> limits 4294967295)
    ((fun lim => tabletype.TableT .I64AT lim reference) <$> limits 18446744073709551615)

theorem tables_support (c : context) (tt : tabletype) :
    Gen.support (tables c) tt ↔ TabletypeValidation.tabletypeValid c tt = true := by
  cases tt with
  | TableT addr lim rt =>
    cases addr <;> simp [tables,limits_support,TabletypeValidation.tabletypeValid]
    all_goals
      constructor
      · rintro ⟨a,ha,b,hb,rfl,rfl⟩; exact ⟨ha,hb⟩
      · rintro ⟨hr,hl⟩; exact ⟨rt,hr,lim,hl,rfl,rfl⟩

theorem tables_finite (c : context) : FiniteConstruction (tables c) :=
  ⟨reftypes_finite c,fun _ => ⟨⟨limits_finite _,fun _ => trivial⟩,⟨limits_finite _,fun _ => trivial⟩⟩⟩

/-- Select positions from already stored type metadata, before constructing
an import or function/tag header. No generated AST is checked or discarded. -/
def indices (c : context) (test : deftype → Bool) :
    List {i : Fin c.TYPES.length // test c.TYPES[i.val] = true} :=
  (List.finRange c.TYPES.length).flatMap fun i =>
    if h : test c.TYPES[i.val] = true then [⟨i,h⟩] else []

theorem indices_cover (c : context) (test : deftype → Bool)
    (i : Fin c.TYPES.length) (h : test c.TYPES[i.val] = true) : ⟨i,h⟩ ∈ indices c test := by
  exact List.mem_flatMap.mpr ⟨i,by simp,by simp [h]⟩

abbrev FunctionIndex (c : context) :=
  {i : Fin c.TYPES.length // (UnrollInterface.deftypeFunctype c.TYPES[i.val]).isSome = true}
abbrev TagIndex (c : context) :=
  {i : Fin c.TYPES.length // TagtypeValidation.tagtypeValid (.TagT c.TYPES[i.val]) = true}

def functions (c : context) : List (FunctionIndex c) :=
  indices c (fun dt => (UnrollInterface.deftypeFunctype dt).isSome)

def tags (c : context) : List (TagIndex c) :=
  indices c (fun dt => TagtypeValidation.tagtypeValid (.TagT dt))

theorem function_result (c : context) (i : FunctionIndex c) :
    ImportValidation.funcImportResult c i.val.val =
      some {c with FUNCS := c.FUNCS ++ [c.TYPES[i.val.val]]} := by
  simp [ImportValidation.funcImportResult,List.getElem?_eq_getElem i.val.isLt,i.property]

theorem tag_result (c : context) (i : TagIndex c) :
    ImportValidation.tagImportResult c i.val.val =
      some {c with TAGS := c.TAGS ++ [.TagT c.TYPES[i.val.val]]} := by
  simp [ImportValidation.tagImportResult,List.getElem?_eq_getElem i.val.isLt,i.property]

end properties.wasm_module_ok.ConstructiveImportTypes
