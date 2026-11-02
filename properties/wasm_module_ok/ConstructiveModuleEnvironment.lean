import properties.wasm_module_ok.ConstructiveBodyEnvironment
import properties.wasm_module_ok.ConstructiveImports
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleEnvironment
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment

/-- Static stage updates preserve the exact context assumptions required by
constant and body construction. No completed module or body is assumed. -/
theorem withFuncs (c : context) (env : Env c) (fs : List deftype)
    (hf : ∀dt∈fs,dt∈c.TYPES) : Env {c with FUNCS:=fs} := by
  let d : context := {c with FUNCS:=fs}
  have transport (t : valtype) (ht : CandidateValMatch.InTableVal c t) : CandidateValMatch.InTableVal d t :=
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl ht
  refine ⟨⟨env.ready.substitution,env.ready.unrolledPredecessors⟩,
    ⟨hf,?globals⟩,?nested,?locals,?labels,?results,?tables,?elems,env.tags⟩
  case globals => intro gt hm; exact transport _ (env.provenance.globals gt hm)
  case nested => exact (ConstTraceNestedReady.nested_table_ready_of_types_eq c d rfl) ▸ env.nested
  case locals => intro ini t hm; exact transport t (env.locals ini t hm)
  case labels => intro ts hm t ht; exact transport t (env.labels ts hm t ht)
  case results => intro t hm; exact transport t (env.results t hm)
  case tables => intro addr lim rt hm; exact transport _ (env.tables addr lim rt hm)
  case elems => intro rt hm; exact transport _ (env.elems rt hm)

theorem withGlobals (c : context) (env : Env c) (gs : List globaltype)
    (hg : ∀gt∈gs,CandidateValMatch.InTableVal c (match gt with | .GlobalT _ t => t)) : Env {c with GLOBALS:=gs} := by
  let d : context := {c with GLOBALS:=gs}
  have transport (t : valtype) (ht : CandidateValMatch.InTableVal c t) : CandidateValMatch.InTableVal d t :=
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl ht
  refine ⟨⟨env.ready.substitution,env.ready.unrolledPredecessors⟩,
    ⟨env.provenance.funcs,?globals⟩,?nested,?locals,?labels,?results,?tables,?elems,env.tags⟩
  case globals => intro gt hm; exact transport _ (hg gt hm)
  case nested => exact (ConstTraceNestedReady.nested_table_ready_of_types_eq c d rfl) ▸ env.nested
  case locals => intro ini t hm; exact transport t (env.locals ini t hm)
  case labels => intro ts hm t ht; exact transport t (env.labels ts hm t ht)
  case results => intro t hm; exact transport t (env.results t hm)
  case tables => intro addr lim rt hm; exact transport _ (env.tables addr lim rt hm)
  case elems => intro rt hm; exact transport _ (env.elems rt hm)

theorem withTables (c : context) (env : Env c) (ts : List tabletype)
    (ht : ∀addr lim rt,tabletype.TableT addr lim rt∈ts → CandidateValMatch.InTableVal c (.RefT rt)) :
    Env {c with TABLES:=ts} := by
  let d : context := {c with TABLES:=ts}
  have transport (t : valtype) (ht : CandidateValMatch.InTableVal c t) : CandidateValMatch.InTableVal d t :=
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl ht
  refine ⟨⟨env.ready.substitution,env.ready.unrolledPredecessors⟩,
    ⟨env.provenance.funcs,?globals⟩,?nested,?locals,?labels,?results,?tables,?elems,env.tags⟩
  case globals => intro gt hm; exact transport _ (env.provenance.globals gt hm)
  case nested => exact (ConstTraceNestedReady.nested_table_ready_of_types_eq c d rfl) ▸ env.nested
  case locals => intro ini t hm; exact transport t (env.locals ini t hm)
  case labels => intro ts hm t ht; exact transport t (env.labels ts hm t ht)
  case results => intro t hm; exact transport t (env.results t hm)
  case tables => intro addr lim rt hm; exact transport _ (ht addr lim rt hm)
  case elems => intro rt hm; exact transport _ (env.elems rt hm)

theorem withMems (c : context) (env : Env c) (ms : List memtype) : Env {c with MEMS:=ms} := by
  let d : context := {c with MEMS:=ms}
  have transport (t : valtype) (ht : CandidateValMatch.InTableVal c t) : CandidateValMatch.InTableVal d t :=
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl ht
  refine ⟨⟨env.ready.substitution,env.ready.unrolledPredecessors⟩,
    ⟨env.provenance.funcs,?globals⟩,?nested,?locals,?labels,?results,?tables,?elems,env.tags⟩
  case globals => intro gt hm; exact transport _ (env.provenance.globals gt hm)
  case nested => exact (ConstTraceNestedReady.nested_table_ready_of_types_eq c d rfl) ▸ env.nested
  case locals => intro ini t hm; exact transport t (env.locals ini t hm)
  case labels => intro ts hm t ht; exact transport t (env.labels ts hm t ht)
  case results => intro t hm; exact transport t (env.results t hm)
  case tables => intro addr lim rt hm; exact transport _ (env.tables addr lim rt hm)
  case elems => intro rt hm; exact transport _ (env.elems rt hm)

theorem withElems (c : context) (env : Env c) (es : List reftype)
    (he : ∀rt∈es,CandidateValMatch.InTableVal c (.RefT rt)) : Env {c with ELEMS:=es} := by
  let d : context := {c with ELEMS:=es}
  have transport (t : valtype) (ht : CandidateValMatch.InTableVal c t) : CandidateValMatch.InTableVal d t :=
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl ht
  refine ⟨⟨env.ready.substitution,env.ready.unrolledPredecessors⟩,
    ⟨env.provenance.funcs,?globals⟩,?nested,?locals,?labels,?results,?tables,?elems,env.tags⟩
  case globals => intro gt hm; exact transport _ (env.provenance.globals gt hm)
  case nested => exact (ConstTraceNestedReady.nested_table_ready_of_types_eq c d rfl) ▸ env.nested
  case locals => intro ini t hm; exact transport t (env.locals ini t hm)
  case labels => intro ts hm t ht; exact transport t (env.labels ts hm t ht)
  case results => intro t hm; exact transport t (env.results t hm)
  case tables => intro addr lim rt hm; exact transport _ (env.tables addr lim rt hm)
  case elems => intro rt hm; exact transport _ (he rt hm)

theorem withDatas (c : context) (env : Env c) (ds : List datatype) : Env {c with DATAS:=ds} := by
  let d : context := {c with DATAS:=ds}
  have transport (t : valtype) (ht : CandidateValMatch.InTableVal c t) : CandidateValMatch.InTableVal d t :=
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl ht
  refine ⟨⟨env.ready.substitution,env.ready.unrolledPredecessors⟩,
    ⟨env.provenance.funcs,?globals⟩,?nested,?locals,?labels,?results,?tables,?elems,env.tags⟩
  case globals => intro gt hm; exact transport _ (env.provenance.globals gt hm)
  case nested => exact (ConstTraceNestedReady.nested_table_ready_of_types_eq c d rfl) ▸ env.nested
  case locals => intro ini t hm; exact transport t (env.locals ini t hm)
  case labels => intro ts hm t ht; exact transport t (env.labels ts hm t ht)
  case results => intro t hm; exact transport t (env.results t hm)
  case tables => intro addr lim rt hm; exact transport _ (env.tables addr lim rt hm)
  case elems => intro rt hm; exact transport _ (env.elems rt hm)

theorem withRefs (c : context) (env : Env c) (refs : SpecTec.free) : Env {c with REFS:=refs} := by
  let d : context := {c with REFS:=refs}
  have transport (t : valtype) (ht : CandidateValMatch.InTableVal c t) : CandidateValMatch.InTableVal d t :=
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl ht
  refine ⟨⟨env.ready.substitution,env.ready.unrolledPredecessors⟩,
    ⟨env.provenance.funcs,?globals⟩,?nested,?locals,?labels,?results,?tables,?elems,env.tags⟩
  case globals => intro gt hm; exact transport _ (env.provenance.globals gt hm)
  case nested => exact (ConstTraceNestedReady.nested_table_ready_of_types_eq c d rfl) ▸ env.nested
  case locals => intro ini t hm; exact transport t (env.locals ini t hm)
  case labels => intro ts hm t ht; exact transport t (env.labels ts hm t ht)
  case results => intro t hm; exact transport t (env.results t hm)
  case tables => intro addr lim rt hm; exact transport _ (env.tables addr lim rt hm)
  case elems => intro rt hm; exact transport _ (env.elems rt hm)

#print axioms withRefs
end properties.wasm_module_ok.ConstructiveModuleEnvironment
