import properties.wasm_module_ok.ConstructiveBodyFunctionMetadata
import properties.wasm_module_ok.ConstructiveBodyReferenceMatcher
import properties.wasm_module_ok.ConstructiveBodyIndexedCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyFunctionCalls
open SpecTec properties.wasm_module_ok ConstructiveBodyFunctionMetadata ConstructiveBodyEnvironment

theorem direct (c : context) (stack : inferresulttype) (sig : Signature c.FUNCS) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.CALL sig.entry.index)⟩)
      n (.success (.of ((⟨(.NoEllipses,sig.inputs),(.NoEllipses,sig.outputs)⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.CALL sig.entry.index) 15 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:15» c stack (.CALL sig.entry.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:15»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp sig.entry.lookup).1)
  rw [sig.entry.lookup]
  apply SpecTecExecution.Eval.bind_success (sig.expand n)
  apply SpecTecExecution.Eval.bind_success ((StartValidation.functype_of_strtype_success_iff _ _ n n).2 ⟨rfl,rfl⟩)
  exact SpecTecExecution.Eval.pure _

theorem reference (c : context) (stack : inferresulttype) (sig : Signature c.TYPES) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.CALL_REF sig.entry.index)⟩)
      n (.success (.of ((⟨(.NoEllipses,sig.inputs++[.RefT (.«% %» .Null (.DefHT sig.entry.value))]),(.NoEllipses,sig.outputs)⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.CALL_REF sig.entry.index) 16 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:16» c stack (.CALL_REF sig.entry.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:16»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (sig.functionType n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp sig.entry.lookup).1)
  rw [sig.entry.lookup]
  exact SpecTecExecution.Eval.pure _

theorem indirect (c : context) (stack : inferresulttype) (sig : Signature c.TYPES) (n : Nat)
    (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype)
    (hx : c.TABLES[x]?=some (.TableT addr lim rt))
    (hm : ∀s,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_reftype» c.TYPES rt (.«% %» .Null .FuncHT)⟩)
      s (.success (.of true)) s) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.CALL_INDIRECT x sig.entry.index)⟩)
      n (.success (.of ((⟨(.NoEllipses,sig.inputs++[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,sig.outputs)⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.CALL_INDIRECT x sig.entry.index) 17 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:17» c stack (.CALL_INDIRECT x sig.entry.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:17»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (sig.functionType n)
  apply SpecTecExecution.Eval.bind_success (hm n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem returnDirect (c : context) (stack : inferresulttype) (sig : Signature c.FUNCS) (n : Nat)
    (hr : ∀s,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_resulttype» c.TYPES sig.outputs c.RESULTS⟩)
      s (.success (.of true)) s) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.RETURN_CALL sig.entry.index)⟩)
      n (.success (.of ((⟨(.Ellipses,sig.inputs),(.Ellipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.RETURN_CALL sig.entry.index) 19 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:19» c stack (.RETURN_CALL sig.entry.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:19»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp sig.entry.lookup).1)
  rw [sig.entry.lookup]
  apply SpecTecExecution.Eval.bind_success (sig.expand n)
  apply SpecTecExecution.Eval.bind_success ((StartValidation.functype_of_strtype_success_iff _ _ n n).2 ⟨rfl,rfl⟩)
  apply SpecTecExecution.Eval.bind_success (hr n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem returnReference (c : context) (stack : inferresulttype) (sig : Signature c.TYPES) (n : Nat)
    (hr : ∀s,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_resulttype» c.TYPES sig.outputs c.RESULTS⟩)
      s (.success (.of true)) s) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.RETURN_CALL_REF sig.entry.index)⟩)
      n (.success (.of ((⟨(.Ellipses,sig.inputs++[.RefT (.«% %» .Null (.DefHT sig.entry.value))]),(.Ellipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.RETURN_CALL_REF sig.entry.index) 20 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:20» c stack (.RETURN_CALL_REF sig.entry.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:20»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (sig.functionType n)
  apply SpecTecExecution.Eval.bind_success (hr n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp sig.entry.lookup).1)
  rw [sig.entry.lookup]
  exact SpecTecExecution.Eval.pure _

theorem returnIndirect (c : context) (stack : inferresulttype) (sig : Signature c.TYPES) (n : Nat)
    (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype)
    (hx : c.TABLES[x]?=some (.TableT addr lim rt))
    (hm : ∀s,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_reftype» c.TYPES rt (.«% %» .Null .FuncHT)⟩)
      s (.success (.of true)) s)
    (hr : ∀s,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_resulttype» c.TYPES sig.outputs c.RESULTS⟩)
      s (.success (.of true)) s) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.RETURN_CALL_INDIRECT x sig.entry.index)⟩)
      n (.success (.of ((⟨(.Ellipses,sig.inputs++[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.Ellipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.RETURN_CALL_INDIRECT x sig.entry.index) 21 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:21» c stack (.RETURN_CALL_INDIRECT x sig.entry.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:21»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (sig.functionType n)
  apply SpecTecExecution.Eval.bind_success (hm n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (hr n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem throwTag (c : context) (stack : inferresulttype) (tag : ConstructiveBodyTagMetadata.Tag c) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.THROW tag.index)⟩)
      n (.success (.of ((⟨(.Ellipses,tag.inputs),(.Ellipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.THROW tag.index) 22 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:22» c stack (.THROW tag.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:22»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp tag.lookup).1)
  rw [tag.lookup]
  apply SpecTecExecution.Eval.bind_success ((UnrollInterface.expanddt_success_iff_result _ _ n n).2 ⟨tag.expanded,rfl⟩)
  apply SpecTecExecution.Eval.bind_success ((StartValidation.functype_of_strtype_success_iff _ _ n n).2 ⟨rfl,rfl⟩)
  exact SpecTecExecution.Eval.pure _

#print axioms returnIndirect
#print axioms throwTag
end properties.wasm_module_ok.ConstructiveBodyFunctionCalls
