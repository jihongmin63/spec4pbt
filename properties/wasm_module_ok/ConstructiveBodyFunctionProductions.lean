import properties.wasm_module_ok.ConstructiveBodyFunctionCalls
import properties.wasm_module_ok.ConstructiveBodyIndexedProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyFunctionProductions
open SpecTec properties.wasm_module_ok ConstructiveBodyFunctionMetadata ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyIndexedProductions

def direct (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.FUNCS) : Production c stack :=
  fixed c stack env (.NoEllipses,sig.inputs) (.NoEllipses,sig.outputs)
    (fun t ht => sig.backed env env.provenance.funcs t (List.mem_append_left _ ht))
    (fun t ht => sig.backed env env.provenance.funcs t (List.mem_append_right _ ht))
    (.CALL sig.entry.index) (ConstructiveBodyFunctionCalls.direct c stack sig)

def returnDirect (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.FUNCS)
    (hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true) : Production c stack :=
  fixed c stack env (.Ellipses,sig.inputs) (.Ellipses,[])
    (fun t ht => sig.backed env env.provenance.funcs t (List.mem_append_left _ ht)) (nil_backed c .Ellipses)
    (.RETURN_CALL sig.entry.index) (fun n => ConstructiveBodyFunctionCalls.returnDirect c stack sig n (fun s => by
      rw [←hm]
      exact ConstructiveBodyMatchers.result_total c sig.outputs c.RESULTS s env.ready
        (fun t ht => sig.backed env env.provenance.funcs t (List.mem_append_right _ ht)) env.results))

def referenceInputs {c : context} (sig : Signature c.TYPES) : List valtype :=
  sig.inputs++[.RefT (.«% %» .Null (.DefHT sig.entry.value))]

theorem reference_backed {c : context} (env : Env c) (sig : Signature c.TYPES) :
    ∀t∈referenceInputs sig,CandidateValMatch.InTableVal c t :=
  append_backed .NoEllipses
    (fun t ht => sig.backed env (fun _ h => h) t (List.mem_append_left _ ht))
    (cons_backed .NoEllipses (CandidateValMembership.table_definition_in_table c _ sig.entry.mem .Null)
      (nil_backed c .NoEllipses))

def reference (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.TYPES) : Production c stack :=
  fixed c stack env (.NoEllipses,referenceInputs sig) (.NoEllipses,sig.outputs)
    (reference_backed env sig)
    (fun t ht => sig.backed env (fun _ h => h) t (List.mem_append_right _ ht))
    (.CALL_REF sig.entry.index) (ConstructiveBodyFunctionCalls.reference c stack sig)

def returnReference (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.TYPES)
    (hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true) : Production c stack :=
  fixed c stack env (.Ellipses,referenceInputs sig) (.Ellipses,[])
    (reference_backed env sig) (nil_backed c .Ellipses)
    (.RETURN_CALL_REF sig.entry.index) (fun n => ConstructiveBodyFunctionCalls.returnReference c stack sig n (fun s => by
      rw [←hm]
      exact ConstructiveBodyMatchers.result_total c sig.outputs c.RESULTS s env.ready
        (fun t ht => sig.backed env (fun _ h => h) t (List.mem_append_right _ ht)) env.results))

structure FunctionTable (c : context) where
  index : Nat
  addr : addrtype
  lim : limits
  rt : reftype
  lookup : c.TABLES[index]?=some (.TableT addr lim rt)
  matched : ConstructiveBodyReferenceMatcher.refMatch c rt (.«% %» .Null .FuncHT)=true

-- Choose existing table type metadata, not an instruction candidate.
def functionTables (c : context) : List (FunctionTable c) :=
  (ConstructiveBodyLookup.entries c.TABLES).flatMap fun e =>
    match he : e.value with
    | .TableT addr lim rt =>
      if hm : ConstructiveBodyReferenceMatcher.refMatch c rt (.«% %» .Null .FuncHT)=true then
        [⟨e.index,addr,lim,rt,by simpa [he] using e.lookup,hm⟩]
      else []

theorem FunctionTable.match_call {c : context} (tab : FunctionTable c) (env : Env c) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_reftype» c.TYPES tab.rt (.«% %» .Null .FuncHT)⟩)
      n (.success (.of true)) n := by
  rw [←tab.matched]
  exact ConstructiveBodyReferenceMatcher.total c tab.rt (.«% %» .Null .FuncHT) n env.ready
    (env.tables tab.addr tab.lim tab.rt (List.mem_iff_getElem?.mpr ⟨tab.index,tab.lookup⟩))
    (ConstructiveBodyReferenceMatcher.base_backed c .Null .FuncHT (by simp [HeaptypeValidation.baseHeaptypes]))

def indirectInputs {c : context} (tab : FunctionTable c) (sig : Signature c.TYPES) : List valtype :=
  sig.inputs++[.NumT (AddrNumtypeDecision.numtypeOfAddrtype tab.addr)]

theorem indirect_backed {c : context} (env : Env c) (tab : FunctionTable c) (sig : Signature c.TYPES) :
    ∀t∈indirectInputs tab sig,CandidateValMatch.InTableVal c t :=
  append_backed .NoEllipses
    (fun t ht => sig.backed env (fun _ h => h) t (List.mem_append_left _ ht))
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))

def indirect (c : context) (stack : inferresulttype) (env : Env c)
    (tab : FunctionTable c) (sig : Signature c.TYPES) : Production c stack :=
  fixed c stack env (.NoEllipses,indirectInputs tab sig) (.NoEllipses,sig.outputs)
    (indirect_backed env tab sig)
    (fun t ht => sig.backed env (fun _ h => h) t (List.mem_append_right _ ht))
    (.CALL_INDIRECT tab.index sig.entry.index)
    (fun n => ConstructiveBodyFunctionCalls.indirect c stack sig n tab.index tab.addr tab.lim tab.rt tab.lookup (tab.match_call env))

def returnIndirect (c : context) (stack : inferresulttype) (env : Env c)
    (tab : FunctionTable c) (sig : Signature c.TYPES)
    (hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true) : Production c stack :=
  fixed c stack env (.Ellipses,indirectInputs tab sig) (.Ellipses,[])
    (indirect_backed env tab sig) (nil_backed c .Ellipses)
    (.RETURN_CALL_INDIRECT tab.index sig.entry.index)
    (fun n => ConstructiveBodyFunctionCalls.returnIndirect c stack sig n tab.index tab.addr tab.lim tab.rt tab.lookup
      (tab.match_call env) (fun s => by
        rw [←hm]
        exact ConstructiveBodyMatchers.result_total c sig.outputs c.RESULTS s env.ready
          (fun t ht => sig.backed env (fun _ h => h) t (List.mem_append_right _ ht)) env.results))

def throwTag (c : context) (stack : inferresulttype) (env : Env c) (tag : ConstructiveBodyTagMetadata.Tag c) : Production c stack :=
  fixed c stack env (.Ellipses,tag.inputs) (.Ellipses,[])
    (fun t ht => tag.backed env t (List.mem_append_left _ ht)) (nil_backed c .Ellipses)
    (.THROW tag.index) (ConstructiveBodyFunctionCalls.throwTag c stack tag)

def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  ((signatures c.FUNCS).flatMap fun sig =>
    [direct c stack env sig] ++
    if hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true then [returnDirect c stack env sig hm] else []) ++
  ((signatures c.TYPES).flatMap fun sig =>
    [reference c stack env sig] ++
    (if hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true then [returnReference c stack env sig hm] else []) ++
    ((functionTables c).flatMap fun tab =>
      [indirect c stack env tab sig] ++
      if hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true then [returnIndirect c stack env tab sig hm] else [])) ++
  ((ConstructiveBodyTagMetadata.tags c).map fun tag => throwTag c stack env tag)

#print axioms all
end properties.wasm_module_ok.ConstructiveBodyFunctionProductions
