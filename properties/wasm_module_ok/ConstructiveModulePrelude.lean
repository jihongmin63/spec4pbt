import properties.wasm_module_ok.ConstructiveModuleTypesEnvironment
import properties.wasm_module_ok.ConstructiveModuleImportEnvironment
import properties.wasm_module_ok.ConstructiveModuleHeaders
import properties.wasm_module_ok.ConstructiveModuleTags
import properties.wasm_module_ok.ConstructiveModuleGlobalsCompleteness
import properties.wasm_module_ok.ConstructiveModuleTablesCompleteness
import properties.wasm_module_ok.ConstructiveModuleMemories
import properties.wasm_module_ok.ConstructiveModuleElems
import properties.wasm_module_ok.ConstructiveModuleDatas
import properties.wasm_module_ok.ConstructiveModuleRefsBounds
import properties.wasm_module_ok.ConstructiveExports
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModulePrelude
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore

def initial : context := ConstructiveModuleTypesEnvironment.initial properties.wasm_module_not_ok.Rejection.emptyFree

structure Prefix where
  types : ConstructiveTypes.Result initial
  imports : ConstructiveImports.Result types.after
  headers : ConstructiveModuleHeaders.Result imports.after

def prefixGen : Gen Prefix := do
  let ts ← ConstructiveTypes.fromEmpty initial rfl
  let is ← ConstructiveImports.generate ts.after
  let fs ← ConstructiveModuleHeaders.generate is.after
    (ConstructiveModuleImportEnvironment.generated ts.after (ConstructiveModuleTypesEnvironment.generated _ ts) is)
  pure ⟨ts,is,fs⟩

def boundedContext (p : Prefix) : context :=
  {p.headers.after with REFS:=ConstructiveModuleRefsBounds.allFunctions p.headers.after}
def boundedEnv (p : Prefix) : Env (boundedContext p) :=
  ConstructiveModuleEnvironment.withRefs p.headers.after p.headers.env _

abbrev Exports (c : context) := {es : List SpecTec.export //
  Gen.support (ConstructiveExports.exports c (.«`{ % `}» [])) es}
def exports (c : context) : Audited (Exports c) :=
  ⟨ConstructiveAttach.attach (ConstructiveExports.exports c (.«`{ % `}» []))
    (ConstructiveExports.exports_audit c _),ConstructiveAttach.audit _ _⟩

structure Result where
  before : Prefix
  tables : ConstructiveModuleTables.Result (boundedContext before)
  memories : ConstructiveModuleMemories.Result tables.after
  globals : ConstructiveModuleGlobals.Result memories.after
  tags : ConstructiveModuleTags.Result globals.after
  elements : ConstructiveModuleElems.Result tags.after
  data : ConstructiveModuleDatas.Result elements.after
  exports : Exports data.after

def generate : Gen Result := do
  let p ← prefixGen
  let ts ← ConstructiveModuleTables.generate (boundedContext p) (boundedEnv p)
  let ms ← ConstructiveModuleMemories.generate ts.after ts.env
  let gs ← ConstructiveModuleGlobals.generate ms.after ms.env
  let tags ← ConstructiveModuleTags.generate gs.after gs.env
  let es ← ConstructiveModuleElems.generate tags.after tags.env
  let ds ← ConstructiveModuleDatas.generate es.after es.env
  let ex ← (exports ds.after).generator
  pure ⟨p,ts,ms,gs,tags,es,ds,ex⟩

/-- The raw prelude is the exact syntax later completed by function bodies and
START. These two fields are excluded by the original free_module premise. -/
def raw (p : Result) : SpecTec.module where
  TYPES := p.before.types.types
  IMPORTS := p.before.imports.items
  FUNCS := p.before.headers.items
  TABLES := p.tables.items
  MEMS := p.memories.items
  GLOBALS := p.globals.items
  TAGS := p.tags.items
  ELEMS := p.elements.items
  DATAS := p.data.items
  START := none
  EXPORTS := p.exports.val

def finalContext (p : Result) : context :=
  {p.data.after with REFS:=ConstructiveFreeModule.moduleFree (raw p)}
def finalEnv (p : Result) : Env (finalContext p) := ConstructiveModuleEnvironment.withRefs p.data.after p.data.env _

theorem prefix_audit : ConstructiveGenAudit.Structural prefixGen :=
  ⟨ConstructiveTypes.generate_audit _ _,fun ts => ⟨ConstructiveImports.generate_audit _,fun is =>
    ⟨ConstructiveModuleHeaders.generate_audit _ _,fun _ => trivial⟩⟩⟩
theorem generate_audit : ConstructiveGenAudit.Structural generate :=
  ⟨prefix_audit,fun p => ⟨ConstructiveModuleTables.generate_audit _ _,fun ts =>
    ⟨ConstructiveModuleMemories.generate_audit _ _,fun ms => ⟨ConstructiveModuleGlobals.generate_audit _ _,fun gs =>
      ⟨ConstructiveModuleTags.generate_audit _ _,fun tags => ⟨ConstructiveModuleElems.generate_audit _ _,fun es =>
        ⟨ConstructiveModuleDatas.generate_audit _ _,fun ds => ⟨(exports ds.after).audit,fun _ => trivial⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms generate_audit
end properties.wasm_module_ok.ConstructiveModulePrelude
