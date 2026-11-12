import properties.wasm_module_ok.ConstructiveModulePrefixCompleteness
import properties.wasm_module_ok.ConstructiveModuleTraceFields
import properties.wasm_module_ok.ConstructiveModuleElemDataListRefs
import properties.wasm_module_ok.ConstructiveModuleExportsRefs
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModulePrelude
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructivePreludeRefs
open properties.wasm_module_not_ok.Rejection

structure Matches (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) (p : Result) : Prop where
  before : PrefixMatches m tr p.before
  tables : p.tables.items=m.TABLES
  memories : p.memories.items=m.MEMS
  globals : p.globals.items=m.GLOBALS
  tags : p.tags.items=m.TAGS
  elements : p.elements.items=m.ELEMS
  data : p.data.items=m.DATAS
  exports : p.exports.val=m.EXPORTS
  after : p.data.after=replace (ConstructiveModuleRefsBounds.allFunctions tr.c2) tr.c8

theorem complete (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    ∃p : Result,Gen.support generate p ∧ Matches m tr p := by
  obtain ⟨p,hp,hm⟩ := prefix_complete m tr
  let refs := ConstructiveModuleRefsBounds.allFunctions tr.c2
  have hb : boundedContext p=replace refs tr.c2 := by
    simp only [boundedContext,hm.c2,ConstructiveModuleRefsBounds.allFunctions,replace,refs]
  have fields := ConstructiveModuleTraceFields.funcs m tr
  have ht := ConstructiveModuleInitializerRefs.tables_replace refs tr.c2 tr.c3 m.TABLES tr.n5 tr.n6
    (fun t ht x hx => ConstructiveModuleRefsBounds.allFunctions_has tr.c2 x
      (ConstructiveModuleInitializerRefs.tables_bounded _ _ _ _ _ tr.tables_ok t ht x hx)) tr.tables_ok
  rw [←hb] at ht
  obtain ⟨ts,hts,htsyn,htout⟩ := ConstructiveModuleTables.generate_complete (boundedContext p) (replace refs tr.c3)
    (boundedEnv p) m.TABLES tr.n5 tr.n6 ht
  have hmem := ConstructivePreludeRefs.mems_replace refs _ _ _ tr.n6 tr.n7 tr.mems_ok
  rw [←htout] at hmem
  obtain ⟨ms,hms,hmsyn,hmout⟩ := ConstructiveModuleMemories.generate_complete ts.after (replace refs tr.c4)
    ts.env m.MEMS tr.n6 tr.n7 hmem
  have hg := ConstructiveModuleInitializerRefs.globals_replace refs tr.c4 tr.c5 m.GLOBALS tr.n7 tr.n8
    (fun g hg x hx => ConstructiveModuleRefsBounds.allFunctions_has tr.c2 x (by
      have h := ConstructiveModuleInitializerRefs.globals_bounded _ _ _ _ _ tr.globals_ok g hg x hx
      simpa only [fields.2.1] using h)) tr.globals_ok
  rw [←hmout] at hg
  obtain ⟨gs,hgs,hgsyn,hgout⟩ := ConstructiveModuleGlobals.generate_complete ms.after (replace refs tr.c5)
    ms.env m.GLOBALS tr.n7 tr.n8 hg
  have htag := ConstructivePreludeRefs.tags_replace refs _ _ _ tr.n8 tr.n9 tr.tags_ok
  rw [←hgout] at htag
  obtain ⟨tags,htags,htagsyn,htagout⟩ := ConstructiveModuleTags.generate_complete gs.after (replace refs tr.c6)
    gs.env m.TAGS ((TagsValidation.tags_success_iff_result _ _ _ _ _).1 htag).1
  have heBound := ConstructiveModuleElemDataRefs.elems_bounded _ _ _ _ _ tr.elems_ok
  rw [ConstructiveModuleTraceFields.allFunctions_eq _ _ fields.2.2.2.1] at heBound
  have he := ConstructiveModuleElemDataRefs.elems_replace refs tr.c6 tr.c7 m.ELEMS tr.n9 tr.n10 heBound tr.elems_ok
  rw [←htagout] at he
  obtain ⟨es,hes,hesyn,heout⟩ := ConstructiveModuleElems.generate_complete tags.after (replace refs tr.c7)
    tags.env m.ELEMS tr.n9 tr.n10 he
  have hdBound := ConstructiveModuleElemDataRefs.datas_bounded _ _ _ _ _ tr.datas_ok
  rw [ConstructiveModuleTraceFields.allFunctions_eq _ _ fields.2.2.2.2.1] at hdBound
  have hd := ConstructiveModuleElemDataRefs.datas_replace refs tr.c7 tr.c8 m.DATAS tr.n10 tr.n11 hdBound tr.datas_ok
  rw [←heout] at hd
  obtain ⟨ds,hds,hdsyn,hdout⟩ := ConstructiveModuleDatas.generate_complete es.after (replace refs tr.c8)
    es.env m.DATAS tr.n10 tr.n11 hd
  have hex := ConstructiveModuleExportsRefs.exports_replace refs tr.c8 _ tr.names m.EXPORTS tr.n13 tr.n14 tr.exports_ok
  rw [←hdout] at hex
  have hexSupport := ((ConstructiveExports.exports_exact_supply ds.after _ m.EXPORTS tr.n13 tr.n14).1 ⟨tr.names,hex⟩).1
  let ex : Exports ds.after := ⟨m.EXPORTS,hexSupport⟩
  have hexGen : Gen.support (exports ds.after).generator ex := ConstructiveAttach.cover _ _ _ hexSupport
  exact ⟨⟨p,ts,ms,gs,tags,es,ds,ex⟩,
    ⟨p,hp,ts,hts,ms,hms,gs,hgs,tags,htags,es,hes,ds,hds,ex,hexGen,rfl⟩,
    hm,htsyn,hmsyn,hgsyn,htagsyn,hesyn,hdsyn,rfl,hdout⟩
#print axioms complete
end properties.wasm_module_ok.ConstructiveModulePrelude
