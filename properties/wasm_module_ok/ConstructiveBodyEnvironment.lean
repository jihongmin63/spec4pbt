import properties.wasm_module_ok.ConstructiveBodyControl
import properties.wasm_module_ok.ConstLocalContextReady
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyEnvironment
open SpecTec properties.wasm_module_ok

/-- Backing for operand types can be derived from the already constructed
module header and function signature. It contains no successful body trace. -/
structure Env (c : context) : Prop where
  ready : CandidateTypeReady.Ready c
  provenance : CandidateUniverseReady.Provenance c
  nested : CandidateNestedReady.nestedTableReady c=true
  locals : ∀ini t,localtype.LocalT ini t∈c.LOCALS → CandidateValMatch.InTableVal c t
  labels : ∀ts∈c.LABELS,∀t∈ts,CandidateValMatch.InTableVal c t
  results : ∀t∈c.RESULTS,CandidateValMatch.InTableVal c t
  tables : ∀addr lim rt,tabletype.TableT addr lim rt∈c.TABLES → CandidateValMatch.InTableVal c (.RefT rt)
  elems : ∀rt∈c.ELEMS,CandidateValMatch.InTableVal c (.RefT rt)
  tags : ∀dt,tagtype.TagT dt∈c.TAGS → dt∈c.TYPES

abbrev StackBacked (c : context) (stack : inferresulttype) : Prop :=
  ∀t∈stack.2,CandidateValMatch.InTableVal c t

theorem Env.frame {c : context} (h : Env c) (ls : List localtype)
    (labels : List resulttype) (results : resulttype)
    (hl : ∀ini t,localtype.LocalT ini t∈ls → CandidateValMatch.InTableVal c t)
    (hb : ∀ts∈labels,∀t∈ts,CandidateValMatch.InTableVal c t)
    (hr : ∀t∈results,CandidateValMatch.InTableVal c t) :
    Env {c with LOCALS:=ls,LABELS:=labels,RESULTS:=results} := by
  let d : context := {c with LOCALS:=ls,LABELS:=labels,RESULTS:=results}
  have transport (t : valtype) (ht : CandidateValMatch.InTableVal c t) :
      CandidateValMatch.InTableVal d t :=
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl ht
  refine ⟨CandidateProvenanceElemDataFuncs.ready_of_types_eq c d rfl h.ready,
    ⟨h.provenance.funcs,?globals⟩,?nested,?locals,?labels,?results,?tables,?elems,h.tags⟩
  case globals => intro gt hm; exact transport _ (h.provenance.globals gt hm)
  case nested => exact (ConstTraceNestedReady.nested_table_ready_of_types_eq c d rfl) ▸ h.nested
  case locals => intro ini t hm; exact transport t (hl ini t hm)
  case labels => intro ts hm t ht; exact transport t (hb ts hm t ht)
  case results => intro t hm; exact transport t (hr t hm)
  case tables => intro addr lim rt hm; exact transport _ (h.tables addr lim rt hm)
  case elems => intro rt hm; exact transport _ (h.elems rt hm)

theorem Env.pushLabel {c : context} (h : Env c) (ts : List valtype)
    (ht : ∀t∈ts,CandidateValMatch.InTableVal c t) : Env {c with LABELS:=ts::c.LABELS} := by
  apply h.frame c.LOCALS (ts::c.LABELS) c.RESULTS h.locals _ h.results
  intro us hu t hm
  rcases List.mem_cons.mp hu with rfl|hu
  · exact ht t hm
  · exact h.labels us hu t hm

theorem Env.setLocal {c : context} (h : Env c) (x : Nat) (t : valtype)
    (ht : CandidateValMatch.InTableVal c t) :
    Env {c with LOCALS:=c.LOCALS.set x (.LocalT .Set t)} := by
  apply h.frame _ c.LABELS c.RESULTS _ h.labels h.results
  intro ini u hu
  rcases List.mem_or_eq_of_mem_set hu with he|he
  · exact h.locals ini u he
  · cases he; exact ht

theorem Env.setTags {c : context} (h : Env c) (tags : List tagtype)
    (ht : ∀dt,tagtype.TagT dt∈tags → dt∈c.TYPES) : Env {c with TAGS:=tags} := by
  let d : context := {c with TAGS:=tags}
  have transport (t : valtype) (ht : CandidateValMatch.InTableVal c t) :
      CandidateValMatch.InTableVal d t :=
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl ht
  refine ⟨CandidateProvenanceElemDataFuncs.ready_of_types_eq c d rfl h.ready,
    ⟨h.provenance.funcs,?globals⟩,?nested,?locals,?labels,?results,?tables,?elems,ht⟩
  case globals => intro gt hm; exact transport _ (h.provenance.globals gt hm)
  case nested => exact (ConstTraceNestedReady.nested_table_ready_of_types_eq c d rfl) ▸ h.nested
  case locals => intro ini t hm; exact transport t (h.locals ini t hm)
  case labels => intro ts hm t ht; exact transport t (h.labels ts hm t ht)
  case results => intro t hm; exact transport t (h.results t hm)
  case tables => intro addr lim rt hm; exact transport _ (h.tables addr lim rt hm)
  case elems => intro rt hm; exact transport _ (h.elems rt hm)

#print axioms Env.setLocal
end properties.wasm_module_ok.ConstructiveBodyEnvironment
