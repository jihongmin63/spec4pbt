import properties.wasm_module_ok.ConstructiveBodyIndexedCalls
import properties.wasm_module_ok.ConstructiveBodyOperatorProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyIndexedProductions
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore
open ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyLookup

theorem num_backed (c : context) (nt : numtype) : CandidateValMatch.InTableVal c (.NumT nt) := by
  intro heap hm; cases hm

theorem nil_backed (c : context) (ell : ellipses) : StackBacked c (ell,[]) := by simp [StackBacked]
theorem cons_backed {c : context} {t : valtype} {ts : List valtype} (ell : ellipses)
    (h : CandidateValMatch.InTableVal c t) (hs : ∀t∈ts,CandidateValMatch.InTableVal c t) : StackBacked c (ell,t::ts) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl|hv
  · exact h
  · exact hs v hv

theorem append_backed {c : context} {ts us : List valtype} (ell : ellipses)
    (hs : ∀t∈ts,CandidateValMatch.InTableVal c t)
    (hu : ∀t∈us,CandidateValMatch.InTableVal c t) : StackBacked c (ell,ts++us) := by
  intro v hv
  rcases List.mem_append.mp hv with hv|hv
  · exact hs v hv
  · exact hu v hv

def fixed (c : context) (stack : inferresulttype) (env : Env c)
    (ins outs : inferresulttype) (hi : StackBacked c ins) (ho : StackBacked c outs)
    (i : instr) (sound : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩)
      n (.success (.of ((⟨ins,outs⟩,[]) : inferinstrtype))) n) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env ins outs hi ho (Audited.pure ⟨i,sound⟩)

def labels (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  (entries c.LABELS).flatMap fun e =>
    let backed := env.labels e.value e.mem
    [fixed c stack env (.Ellipses,e.value) (.Ellipses,[]) backed (nil_backed c .NoEllipses)
      (.BR e.index) (fun n => ConstructiveBodyIndexedCalls.branch c stack e.index e.value n e.lookup),
     fixed c stack env (.NoEllipses,e.value++[.NumT .I32T]) (.NoEllipses,e.value)
      (append_backed .NoEllipses backed (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))) backed
      (.BR_IF e.index) (fun n => ConstructiveBodyIndexedCalls.branchIf c stack e.index e.value n e.lookup)]

def globals (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  (entries c.GLOBALS).flatMap fun e =>
    match he : e.value with
    | .GlobalT mu t =>
      have lookup : c.GLOBALS[e.index]?=some (.GlobalT mu t) := by simpa [he] using e.lookup
      have backed : CandidateValMatch.InTableVal c t := by simpa [he] using env.provenance.globals e.value e.mem
      let get := fixed c stack env (.NoEllipses,[]) (.NoEllipses,[t]) (nil_backed c .NoEllipses)
        (cons_backed .NoEllipses backed (nil_backed c .NoEllipses)) (.«GLOBAL.GET» e.index)
        (fun n => ConstructiveBodyIndexedCalls.globalGet c stack e.index mu t n lookup)
      match hm : mu with
      | .Cons => [get]
      | .Var =>
        [get,fixed c stack env (.NoEllipses,[t]) (.NoEllipses,[])
          (cons_backed .NoEllipses backed (nil_backed c .NoEllipses)) (nil_backed c .NoEllipses) (.«GLOBAL.SET» e.index)
          (fun n => ConstructiveBodyIndexedCalls.globalSet c stack e.index t n (by simpa [hm] using lookup))]

def tables (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  (entries c.TABLES).flatMap fun e =>
    match he : e.value with
    | .TableT addr lim rt =>
      have lookup : c.TABLES[e.index]?=some (.TableT addr lim rt) := by simpa [he] using e.lookup
      have refBacked : CandidateValMatch.InTableVal c (.RefT rt) :=
        env.tables addr lim rt (by simpa [he] using e.mem)
      let nt := AddrNumtypeDecision.numtypeOfAddrtype addr
      have number : CandidateValMatch.InTableVal c (.NumT nt) := num_backed c nt
      let empty := nil_backed c .NoEllipses
      let oneNum := cons_backed .NoEllipses number empty
      let oneRef := cons_backed .NoEllipses refBacked empty
      [fixed c stack env (.NoEllipses,[.NumT nt]) (.NoEllipses,[.RefT rt]) oneNum oneRef
        (.«TABLE.GET» e.index) (fun n => ConstructiveBodyIndexedCalls.tableGet c stack e.index addr lim rt n lookup),
       fixed c stack env (.NoEllipses,[.NumT nt,.RefT rt]) (.NoEllipses,[])
        (cons_backed .NoEllipses number oneRef) empty
        (.«TABLE.SET» e.index) (fun n => ConstructiveBodyIndexedCalls.tableSet c stack e.index addr lim rt n lookup),
       fixed c stack env (.NoEllipses,[]) (.NoEllipses,[.NumT nt]) empty oneNum
        (.«TABLE.SIZE» e.index) (fun n => ConstructiveBodyIndexedCalls.tableSize c stack e.index addr lim rt n lookup),
       fixed c stack env (.NoEllipses,[.RefT rt,.NumT nt]) (.NoEllipses,[.NumT nt])
        (cons_backed .NoEllipses refBacked oneNum) oneNum
        (.«TABLE.GROW» e.index) (fun n => ConstructiveBodyIndexedCalls.tableGrow c stack e.index addr lim rt n lookup),
       fixed c stack env (.NoEllipses,[.NumT nt,.RefT rt,.NumT nt]) (.NoEllipses,[])
        (cons_backed .NoEllipses number (cons_backed .NoEllipses refBacked oneNum)) empty
        (.«TABLE.FILL» e.index) (fun n => ConstructiveBodyIndexedCalls.tableFill c stack e.index addr lim rt n lookup)]

def memories (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  (entries c.MEMS).flatMap fun e =>
    match he : e.value with
    | .MemoryT addr lim =>
      have lookup : c.MEMS[e.index]?=some (.MemoryT addr lim) := by simpa [he] using e.lookup
      let nt := AddrNumtypeDecision.numtypeOfAddrtype addr
      have number : CandidateValMatch.InTableVal c (.NumT nt) := num_backed c nt
      let empty := nil_backed c .NoEllipses
      let one := cons_backed .NoEllipses number empty
      [fixed c stack env (.NoEllipses,[]) (.NoEllipses,[.NumT nt]) empty one
        (.«MEMORY.SIZE» e.index) (fun n => ConstructiveBodyIndexedCalls.memorySize c stack e.index addr lim n lookup),
       fixed c stack env (.NoEllipses,[.NumT nt]) (.NoEllipses,[.NumT nt]) one one
        (.«MEMORY.GROW» e.index) (fun n => ConstructiveBodyIndexedCalls.memoryGrow c stack e.index addr lim n lookup),
       fixed c stack env (.NoEllipses,[.NumT nt,.NumT .I32T,.NumT nt]) (.NoEllipses,[])
        (cons_backed .NoEllipses number (cons_backed .NoEllipses (num_backed c _) one)) empty
        (.«MEMORY.FILL» e.index) (fun n => ConstructiveBodyIndexedCalls.memoryFill c stack e.index addr lim n lookup)]

def drops (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  ((List.finRange c.ELEMS.length).map fun x =>
    fixed c stack env (.NoEllipses,[]) (.NoEllipses,[]) (nil_backed c .NoEllipses) (nil_backed c .NoEllipses)
      (.«ELEM.DROP» x.val) (fun n => ConstructiveBodyIndexedCalls.elemDrop c stack x.val n x.isLt)) ++
  ((List.finRange c.DATAS.length).map fun x =>
    fixed c stack env (.NoEllipses,[]) (.NoEllipses,[]) (nil_backed c .NoEllipses) (nil_backed c .NoEllipses)
      (.«DATA.DROP» x.val) (fun n => ConstructiveBodyIndexedCalls.dataDrop c stack x.val n x.isLt))

def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  labels c stack env ++ globals c stack env ++ tables c stack env ++ memories c stack env ++ drops c stack env

#print axioms tables
end properties.wasm_module_ok.ConstructiveBodyIndexedProductions
