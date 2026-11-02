import properties.wasm_module_ok.ConstructiveBodyCatchCoverage
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyCatchOriginal
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyTagMetadata ConstructiveBodyCatches ConstructiveBodyCatchCoverage

theorem clause0_covered (c : context) (env : Env c) (outputs : List valtype)
    (raw : SpecTec.«catch») (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Catch_ok:clause:0» c outputs raw) start (.success (.of ())) finish) : Covers c env raw := by
  unfold SpecTec.«Catch_ok:clause:0» at h
  cases h with | bind_success hg h =>
   cases hg with | guard_true hg =>
    cases raw with
    | Catch x y =>
      cases h with | bind_success _ h =>
       cases hx : c.TAGS[x]? with
       | none => rw [hx] at h; cases h
       | some tg =>
         rw [hx] at h
         cases tg with | TagT dt =>
          cases h with | bind_success hexpand h =>
           rename_i expandSupply expanded
           cases h with | bind_success hfunc h =>
            rename_i functionSupply ft
            have he := (StartValidation.functype_of_strtype_success_iff expanded ft _ _).1 hfunc |>.1
            subst expanded
            cases ft with | FuncT ins outs =>
             cases h with | bind_success _ h =>
              cases hy : c.LABELS[y]? with
              | none => rw [hy] at h; cases h
              | some target =>
                rw [hy] at h
                cases h with | bind_success hmatch h =>
                 cases h with | bind_success hg hp =>
                  cases hg with | guard_true he =>
                   cases he
                   let tag : Tag c := ⟨x,dt,ins,outs,hx,
                     (UnrollInterface.expanddt_success_iff_result dt (.DefFuncT (.FuncT ins outs)) _ _).1 hexpand |>.1⟩
                   exact specific_covers c env tag false y target hy _ _
                     (by simpa [arguments,tag,exn] using hmatch)
    | CatchRef x y => simp [SpecTec.«exec:match:catch:Catch»] at hg
    | CatchAll y => simp [SpecTec.«exec:match:catch:Catch»] at hg
    | CatchAllRef y => simp [SpecTec.«exec:match:catch:Catch»] at hg

theorem clause1_covered (c : context) (env : Env c) (outputs : List valtype)
    (raw : SpecTec.«catch») (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Catch_ok:clause:1» c outputs raw) start (.success (.of ())) finish) : Covers c env raw := by
  unfold SpecTec.«Catch_ok:clause:1» at h
  cases h with | bind_success hg h =>
   cases hg with | guard_true hg =>
    cases raw with
    | Catch x y => simp [SpecTec.«exec:match:catch:CatchRef»] at hg
    | CatchRef x y =>
      cases h with | bind_success _ h =>
       cases hx : c.TAGS[x]? with
       | none => rw [hx] at h; cases h
       | some tg =>
         rw [hx] at h
         cases tg with | TagT dt =>
          cases h with | bind_success hexpand h =>
           rename_i expandSupply expanded
           cases h with | bind_success hfunc h =>
            rename_i functionSupply ft
            have he := (StartValidation.functype_of_strtype_success_iff expanded ft _ _).1 hfunc |>.1
            subst expanded
            cases ft with | FuncT ins outs =>
             cases h with | bind_success _ h =>
              cases hy : c.LABELS[y]? with
              | none => rw [hy] at h; cases h
              | some target =>
                rw [hy] at h
                cases h with | bind_success hmatch h =>
                 cases h with | bind_success hg hp =>
                  cases hg with | guard_true he =>
                   cases he
                   let tag : Tag c := ⟨x,dt,ins,outs,hx,
                     (UnrollInterface.expanddt_success_iff_result dt (.DefFuncT (.FuncT ins outs)) _ _).1 hexpand |>.1⟩
                   exact specific_covers c env tag true y target hy _ _
                     (by simpa [arguments,tag,exn] using hmatch)
    | CatchAll y => simp [SpecTec.«exec:match:catch:CatchRef»] at hg
    | CatchAllRef y => simp [SpecTec.«exec:match:catch:CatchRef»] at hg

theorem clause2_covered (c : context) (env : Env c) (outputs : List valtype)
    (raw : SpecTec.«catch») (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Catch_ok:clause:2» c outputs raw) start (.success (.of ())) finish) : Covers c env raw := by
  unfold SpecTec.«Catch_ok:clause:2» at h
  cases h with | bind_success hg h =>
   cases hg with | guard_true hg =>
    cases raw with
    | Catch x y => simp [SpecTec.«exec:match:catch:CatchAll»] at hg
    | CatchRef x y => simp [SpecTec.«exec:match:catch:CatchAll»] at hg
    | CatchAll y =>
      cases h with | bind_success _ h =>
       cases hy : c.LABELS[y]? with
       | none => rw [hy] at h; cases h
       | some target =>
         rw [hy] at h
         cases h with | bind_success hmatch h =>
          cases h with | bind_success hg hp =>
           cases hg with | guard_true he =>
            cases he
            exact all_covers c env false y target hy _ _ hmatch
    | CatchAllRef y => simp [SpecTec.«exec:match:catch:CatchAll»] at hg

theorem clause3_covered (c : context) (env : Env c) (outputs : List valtype)
    (raw : SpecTec.«catch») (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Catch_ok:clause:3» c outputs raw) start (.success (.of ())) finish) : Covers c env raw := by
  unfold SpecTec.«Catch_ok:clause:3» at h
  cases h with | bind_success hg h =>
   cases hg with | guard_true hg =>
    cases raw with
    | Catch x y => simp [SpecTec.«exec:match:catch:CatchAllRef»] at hg
    | CatchRef x y => simp [SpecTec.«exec:match:catch:CatchAllRef»] at hg
    | CatchAll y => simp [SpecTec.«exec:match:catch:CatchAllRef»] at hg
    | CatchAllRef y =>
      cases h with | bind_success _ h =>
       cases hy : c.LABELS[y]? with
       | none => rw [hy] at h; cases h
       | some target =>
         rw [hy] at h
         cases h with | bind_success hmatch h =>
          cases h with | bind_success hg hp =>
           cases hg with | guard_true he =>
            cases he
            exact all_covers c env true y target hy _ _ hmatch

theorem original_covered (c : context) (env : Env c) (outputs : List valtype)
    (raw : SpecTec.«catch») (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Catch_ok c outputs raw⟩) start (.success (.of ())) finish) : Covers c env raw := by
  cases h with | call h =>
   change SpecTecExecution.Eval SpecTec.Body
     (SpecTecExecution.tryClauses (SpecTec.Catch_ok_clauses c outputs raw))
     start (.success (.of ())) finish at h
   obtain ⟨k,h⟩ := (SpecTecExecution.tryClauses_success_iff _ _ _ _).1 h
   unfold SpecTec.Catch_ok_clauses at h
   rcases h with h|⟨_,h|⟨_,h|⟨_,h|⟨_,h⟩⟩⟩⟩
   · exact clause0_covered c env outputs raw start finish h
   · exact clause1_covered c env outputs raw start finish h
   · exact clause2_covered c env outputs raw start finish h
   · exact clause3_covered c env outputs raw start finish h
   · cases h

theorem original_complete (c : context) (env : Env c) (outputs : List valtype)
    (raw : SpecTec.«catch») (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Catch_ok c outputs raw⟩) start (.success (.of ())) finish) :
    Covers c env raw ∧ finish=start := by
  have hc := original_covered c env outputs raw start finish h
  obtain ⟨handler,hmem,he⟩ := hc
  have hs := handler.property outputs start
  rw [he] at hs
  exact ⟨⟨handler,hmem,he⟩,(properties.wasm_module_ok.Execution.eval_deterministic h hs).2⟩

#print axioms original_complete
end properties.wasm_module_ok.ConstructiveBodyCatchOriginal
