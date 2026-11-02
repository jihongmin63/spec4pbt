import properties.wasm_module_ok.ConstructiveBodyCatalogCoverage
import properties.wasm_module_ok.ConstructiveBodySizedSupport
import properties.wasm_module_ok.ConstructiveBodyStepCoverage
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace properties.wasm_module_ok.ConstructiveBodyCompleteness
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyTail ConstructiveBodyGeneration

theorem sized_complete (depth : Nat) :
    ∀(root c : context) (stack : inferresulttype) (outputs : List valtype)
      (er : Env root) (ec : Env c) (hs : StackBacked c stack)
      (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) (he : c.TYPES=root.TYPES)
      (code : List instr) (finalContext : context) (finalStack : inferresulttype) (ell : ellipses)
      (n middle finish : Nat),sizeOf code≤depth →
      ConstConstructiveTrace.Trace c stack code finalContext finalStack n middle →
      Eval SpecTec.Body (.call ⟨inferresulttype,Call.«$pop» root (.NoEllipses,outputs) finalStack⟩)
        middle (.success (.of ((ell,[]) : inferresulttype))) finish →
      (∃tail,Gen.support (sized depth root c stack outputs er ec hs ho he).generator tail ∧ tail.val=code) ∧ finish=n := by
  induction depth with
  | zero =>
    intro root c stack outputs er ec hs ho he code finalContext finalStack ell n middle finish hsize htrace hpop
    have hempty : code=[] := by cases code <;> simp_all
    subst code
    cases htrace
    exact ConstructiveBodySizedSupport.ending 0 root c stack outputs er ec hs ho he ell n finish hpop
  | succ depth ih =>
    intro root c stack outputs er ec hs ho he code finalContext finalStack ell n middle finish hsize htrace hpop
    cases htrace with
    | nil => exact ConstructiveBodySizedSupport.ending (depth+1) root c stack outputs er ec hs ho he ell n finish hpop
    | @cons c next finalContext stack popped pushed finalStack i rest effect n n1 n2 n3 n4 middle hi hl hp hq hr =>
      have hiSize : sizeOf i≤depth := by simp only [List.cons.sizeOf_spec] at hsize; omega
      have hrSize : sizeOf rest≤depth := by simp only [List.cons.sizeOf_spec] at hsize; omega
      have children : ConstructiveBodyChildCoverage.Complete (ConstructiveBodySizedSupport.child depth) i := by
        intro d ed ins outs hins houts body start endSupply hbSize hbody
        obtain ⟨fs,indices,el,mid,hseq,hfinal⟩ := (BlockTrace.block_success_iff d ins outs [] body start endSupply).1 hbody
        obtain ⟨_,fc,htr⟩ := (ConstConstructiveTrace.instrs_success_iff_trace body d (.NoEllipses,ins) (fs,indices) start mid).1 hseq
        obtain ⟨⟨tail,ht,hval⟩,_⟩ := ih d d (.NoEllipses,ins) outs ed ed hins houts rfl body fc fs el start mid endSupply
          (by omega) htr hfinal
        exact ⟨asBlock tail,⟨(),rfl,tail,ht,rfl⟩,hval⟩
      have hc := (ConstructiveBodyCatalogCoverage.original c stack ec hs i depth
        ((ConstructiveBodyCatalogCoverage.arity_le_size i).trans hiSize) (ConstructiveBodySizedSupport.child depth) children effect n n1 hi).1
      obtain ⟨p,hpMem,g,s,hg,hsg,hsi,hsc,hss,hn⟩ := ConstructiveBodyStepCoverage.original c stack ec hs
        (catalog c stack ec hs depth (ConstructiveBodySizedSupport.child depth)) i effect next popped pushed n n1 n2 n3 n4 hc hi hl hp hq
      subst next
      subst pushed
      subst n4
      obtain ⟨⟨tail,ht,hval⟩,hf⟩ := ih root s.nextContext s.nextStack outputs er s.nextEnv s.nextBacked ho
        (s.typesEq.trans he) rest finalContext finalStack ell n middle finish hrSize hr hpop
      refine ⟨⟨prepend s tail,ConstructiveBodySizedSupport.cons depth root c stack outputs er ec hs ho he p hpMem g hg s hsg tail ht,?_⟩,hf⟩
      change s.instruction::tail.val=i::rest
      rw [hsi,hval]

/-- Every original successful body, with its original syntax and supply, is in
the generator support. All environment assumptions concern the existing context. -/
theorem bodies_complete (c : context) (env : Env c) (ins outs : List valtype)
    (hi : ∀t∈ins,CandidateValMatch.InTableVal c t) (ho : ∀t∈outs,CandidateValMatch.InTableVal c t)
    (code : List instr) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨Unit,Call.Block_ok c (.InstrT ins outs []) code⟩)
      n (.success (.of ())) finish) : Gen.support (bodies c env ins outs hi ho) code ∧ finish=n := by
  obtain ⟨fs,indices,el,mid,hseq,hfinal⟩ := (BlockTrace.block_success_iff c ins outs [] code n finish).1 h
  obtain ⟨_,fc,htr⟩ := (ConstConstructiveTrace.instrs_success_iff_trace code c (.NoEllipses,ins) (fs,indices) n mid).1 hseq
  obtain ⟨⟨tail,ht,hval⟩,hn⟩ := sized_complete (sizeOf code) c c (.NoEllipses,ins) outs env env hi ho rfl
    code fc fs el n mid finish (Nat.le_refl _) htr hfinal
  refine ⟨?_,hn⟩
  simp only [bodies,Gen.Support.support_map]
  exact ⟨asBlock tail,⟨sizeOf code,by simp,tail,ht,rfl⟩,hval.symm⟩

theorem bodies_exact (c : context) (env : Env c) (ins outs : List valtype)
    (hi : ∀t∈ins,CandidateValMatch.InTableVal c t) (ho : ∀t∈outs,CandidateValMatch.InTableVal c t)
    (code : List instr) (n : Nat) :
    Gen.support (bodies c env ins outs hi ho) code ↔
    Eval SpecTec.Body (.call ⟨Unit,Call.Block_ok c (.InstrT ins outs []) code⟩)
      n (.success (.of ())) n := by
  exact ⟨fun h => bodies_sound c env ins outs hi ho code h n,
    fun h => (bodies_complete c env ins outs hi ho code n n h).1⟩

#print axioms sized_complete
#print axioms bodies_complete
#print axioms bodies_exact
end properties.wasm_module_ok.ConstructiveBodyCompleteness
