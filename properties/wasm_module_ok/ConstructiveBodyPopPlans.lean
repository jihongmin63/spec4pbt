import properties.wasm_module_ok.ConstructiveConstProductivePlans
import properties.wasm_module_ok.PopGeneralValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyPopPlans
open SpecTec properties.wasm_module_ok

def width (need available : inferresulttype) : Nat := min need.2.length available.2.length

def actual (need available : inferresulttype) : List valtype :=
  let suffix := available.2.drop (available.2.length-width need available)
  match available.1 with
  | .Ellipses => MakeValidation.makeResult .BotT (need.2.length-width need available) ++ suffix
  | .NoEllipses => suffix

def remaining (need available : inferresulttype) : inferresulttype :=
  (available.1,match need.1 with
    | .Ellipses => []
    | .NoEllipses => available.2.take (available.2.length-width need available))

/-- This selects compatible STACK TYPE productions before an instruction or
body is emitted. It does not inspect an instruction or an AST candidate. -/
def popPlan (c : context) (need available : inferresulttype) : Option inferresulttype :=
  if MatchResulttypeDecision.matchPairs c (actual need available) need.2 then
    some (remaining need available)
  else none

theorem actual_table (c : context) (need available : inferresulttype)
    (ha : ∀t∈available.2,CandidateValMatch.InTableVal c t) :
    ∀t∈actual need available,CandidateValMatch.InTableVal c t := by
  intro t ht
  unfold actual at ht
  cases he : available.1 with
  | NoEllipses =>
    simp only [he] at ht
    exact ha t (List.mem_of_mem_drop ht)
  | Ellipses =>
    simp only [he,List.mem_append] at ht
    rcases ht with hb|hs
    · have hbot : t=.BotT := by
        rw [ConstructiveConstTableExpand.make_replicate] at hb
        exact (List.mem_replicate.mp hb).2
      subst t
      intro h hh; cases hh
    · exact ha t (List.mem_of_mem_drop hs)

theorem pop_NE_clause (c : context) (need available : List valtype) (n : Nat)
    (hm : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c
        (MakeValidation.makeResult .BotT (need.length-min need.length available.length) ++
          available.drop (available.length-min need.length available.length)) need⟩)
      n (.success (.of ())) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:1» c (.NoEllipses,need) (.Ellipses,available))
      n (.success (.of ((.Ellipses,available.take (available.length-min need.length available.length)) : inferresulttype))) n := by
  have ha : min need.length available.length≤available.length := Nat.min_le_right _ _
  have hn : min need.length available.length≤need.length := Nat.min_le_left _ _
  have haInt : Int.ofNat available.length-Int.ofNat (min need.length available.length)=Int.ofNat (available.length-min need.length available.length) := (Int.ofNat_sub ha).symm
  have hnInt : Int.ofNat need.length-Int.ofNat (min need.length available.length)=Int.ofNat (need.length-min need.length available.length) := (Int.ofNat_sub hn).symm
  have htake : (available.drop (available.length-min need.length available.length)).take (min need.length available.length)=
      available.drop (available.length-min need.length available.length) := by
    apply List.take_of_length_le
    simp only [List.length_drop]
    omega
  unfold SpecTec.«$pop:clause:1»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (MinValidation.min_total need.length available.length n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
  simp only [hnInt,Int.toNat?]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
  simp only [haInt,Int.toNat?]
  apply SpecTecExecution.Eval.bind_success
  · unfold SpecTecExecution.require
    exact SpecTecExecution.Eval.orElse_success (SpecTecExecution.Eval.guard_true (by rw [Nat.sub_add_cancel ha]))
  rw [htake]
  apply SpecTecExecution.Eval.bind_success (MakeValidation.make_total valtype .BotT _ n)
  apply SpecTecExecution.Eval.bind_success hm
  apply SpecTecExecution.Eval.bind_success
  · unfold SpecTecExecution.require
    exact SpecTecExecution.Eval.orElse_success (SpecTecExecution.Eval.guard_true (by omega))
  exact SpecTecExecution.Eval.pure _

theorem pop_EE_clause (c : context) (need available : List valtype) (n : Nat)
    (hm : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c
        (MakeValidation.makeResult .BotT (need.length-min need.length available.length) ++
          available.drop (available.length-min need.length available.length)) need⟩)
      n (.success (.of ())) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:0» c (.Ellipses,need) (.Ellipses,available))
      n (.success (.of ((.Ellipses,[]) : inferresulttype))) n := by
  have ha : min need.length available.length≤available.length := Nat.min_le_right _ _
  have hn : min need.length available.length≤need.length := Nat.min_le_left _ _
  have haInt : Int.ofNat available.length-Int.ofNat (min need.length available.length)=Int.ofNat (available.length-min need.length available.length) := (Int.ofNat_sub ha).symm
  have hnInt : Int.ofNat need.length-Int.ofNat (min need.length available.length)=Int.ofNat (need.length-min need.length available.length) := (Int.ofNat_sub hn).symm
  have htake : (available.drop (available.length-min need.length available.length)).take (min need.length available.length)=
      available.drop (available.length-min need.length available.length) := by
    apply List.take_of_length_le
    simp only [List.length_drop]
    omega
  unfold SpecTec.«$pop:clause:0»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (MinValidation.min_total need.length available.length n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
  simp only [hnInt,Int.toNat?]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
  simp only [haInt,Int.toNat?]
  apply SpecTecExecution.Eval.bind_success
  · unfold SpecTecExecution.require
    exact SpecTecExecution.Eval.orElse_success (SpecTecExecution.Eval.guard_true (by rw [Nat.sub_add_cancel ha]))
  rw [htake]
  apply SpecTecExecution.Eval.bind_success (MakeValidation.make_total valtype .BotT _ n)
  apply SpecTecExecution.Eval.bind_success hm
  exact SpecTecExecution.Eval.pure _

theorem pop_EN_clause (c : context) (need available : List valtype) (n : Nat)
    (hm : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c
        (available.drop (available.length-min need.length available.length)) need⟩)
      n (.success (.of ())) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:2» c (.Ellipses,need) (.NoEllipses,available))
      n (.success (.of ((.NoEllipses,[]) : inferresulttype))) n := by
  have ha : min need.length available.length≤available.length := Nat.min_le_right _ _
  have haInt : Int.ofNat available.length-Int.ofNat (min need.length available.length)=Int.ofNat (available.length-min need.length available.length) := (Int.ofNat_sub ha).symm
  have htake : (available.drop (available.length-min need.length available.length)).take (min need.length available.length)=
      available.drop (available.length-min need.length available.length) := by
    apply List.take_of_length_le
    simp only [List.length_drop]
    omega
  unfold SpecTec.«$pop:clause:2»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (MinValidation.min_total need.length available.length n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
  simp only [haInt,Int.toNat?]
  apply SpecTecExecution.Eval.bind_success
  · unfold SpecTecExecution.require
    exact SpecTecExecution.Eval.orElse_success (SpecTecExecution.Eval.guard_true (by rw [Nat.sub_add_cancel ha]))
  rw [htake]
  apply SpecTecExecution.Eval.bind_success hm
  exact SpecTecExecution.Eval.pure _

theorem pop_dispatch (c : context) (need available : inferresulttype) (n : Nat)
    (hm : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c (actual need available) need.2⟩)
      n (.success (.of ())) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferresulttype,SpecTecCall.«$pop» c need available⟩)
      n (.success (.of (remaining need available))) n := by
  rcases need with ⟨ne,ns⟩
  rcases available with ⟨ae,as⟩
  cases ne with
  | Ellipses =>
    cases ae with
    | Ellipses =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$pop_clauses» c (.Ellipses,ns) (.Ellipses,as)) ())
        n (.success (.of (remaining (.Ellipses,ns) (.Ellipses,as)))) n
      apply SpecTecExecution.firstSuccess_cons_success
      exact pop_EE_clause c ns as n hm
    | NoEllipses =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$pop_clauses» c (.Ellipses,ns) (.NoEllipses,as)) ())
        n (.success (.of (remaining (.Ellipses,ns) (.NoEllipses,as)))) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pop:clause:0» c (.Ellipses,ns) (.NoEllipses,as)) n .unmatch n
        unfold SpecTec.«$pop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:ellipses:Ellipses»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pop:clause:1» c (.Ellipses,ns) (.NoEllipses,as)) n .unmatch n
        unfold SpecTec.«$pop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:ellipses:NoEllipses»]))
      apply SpecTecExecution.firstSuccess_cons_success
      exact pop_EN_clause c ns as n hm
  | NoEllipses =>
    cases ae with
    | Ellipses =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$pop_clauses» c (.NoEllipses,ns) (.Ellipses,as)) ())
        n (.success (.of (remaining (.NoEllipses,ns) (.Ellipses,as)))) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pop:clause:0» c (.NoEllipses,ns) (.Ellipses,as)) n .unmatch n
        unfold SpecTec.«$pop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:ellipses:Ellipses»]))
      apply SpecTecExecution.firstSuccess_cons_success
      exact pop_NE_clause c ns as n hm
    | NoEllipses =>
      have hlen := (MatchResulttypeValidation.match_resulttype_success_iff c _ _ n n).1 hm |>.1
      have hdrop : (as.drop (as.length-min ns.length as.length)).length=min ns.length as.length := by
        simp only [List.length_drop]
        exact Nat.sub_sub_self (Nat.min_le_right _ _)
      have hlen' : ns.length=min ns.length as.length := hlen.trans hdrop
      have hle : ns.length≤as.length := hlen'.symm ▸ Nat.min_le_right ns.length as.length
      simpa only [actual,width,remaining,Nat.min_eq_left hle] using
        PopGeneralValidation.pop_noellipses_of_match c ns as n n hle
          (by simpa only [actual,width,Nat.min_eq_left hle] using hm)

theorem pop_plan_sound (c : context) (need available result : inferresulttype) (n : Nat)
    (hr : CandidateTypeReady.Ready c)
    (hn : ∀t∈need.2,CandidateValMatch.InTableVal c t)
    (ha : ∀t∈available.2,CandidateValMatch.InTableVal c t)
    (h : popPlan c need available=some result) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferresulttype,SpecTecCall.«$pop» c need available⟩)
      n (.success (.of result)) n := by
  unfold popPlan at h
  split at h
  · rename_i hm
    cases h
    exact pop_dispatch c need available n
      ((MatchResulttypeDecision.match_pairs_iff_resulttype c _ _ n hr (actual_table c need available ha) hn).1 hm)
  · cases h


theorem clause0_has_match (c : context) (ns as : List valtype)
    (r : inferresulttype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:0» c (.Ellipses,ns) (.Ellipses,as))
      start (.success (.of r)) finish) :
    ∃a b, SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c
        (actual (.Ellipses,ns) (.Ellipses,as)) ns⟩) a (.success (.of ())) b := by
  unfold SpecTec.«$pop:clause:0» at h
  cases h with | bind_success _ h =>
   cases h with | bind_success _ h =>
    cases h with | bind_success hm h =>
     obtain ⟨rfl,rfl⟩ := (MinValidation.min_success_iff ns.length as.length _ _ _).1 hm
     have hda : Int.ofNat as.length-Int.ofNat (min ns.length as.length)=
       Int.ofNat (as.length-min ns.length as.length) := (Int.ofNat_sub (Nat.min_le_right _ _)).symm
     have hdn : Int.ofNat ns.length-Int.ofNat (min ns.length as.length)=
       Int.ofNat (ns.length-min ns.length as.length) := (Int.ofNat_sub (Nat.min_le_left _ _)).symm
     have ht : (as.drop (as.length-min ns.length as.length)).take (min ns.length as.length)=
         as.drop (as.length-min ns.length as.length) := by
       apply List.take_of_length_le
       simp only [List.length_drop]
       omega
     simp only [hda,hdn,Int.toNat?] at h
     cases h with | bind_success _ h =>
      cases h with | bind_success _ h =>
       cases h with | bind_success _ h =>
        cases h with | bind_success hmake h =>
         obtain ⟨rfl,rfl⟩ := (MakeValidation.make_success_iff valtype .BotT _ _ _ _).1 hmake
         cases h with | bind_success hm _ =>
          cases_type Unit
          exact ⟨_,_,by simpa only [actual,width,ht] using hm⟩

theorem clause1_has_match (c : context) (ns as : List valtype)
    (r : inferresulttype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:1» c (.NoEllipses,ns) (.Ellipses,as))
      start (.success (.of r)) finish) :
    ∃a b, SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c
        (actual (.NoEllipses,ns) (.Ellipses,as)) ns⟩) a (.success (.of ())) b := by
  unfold SpecTec.«$pop:clause:1» at h
  cases h with | bind_success _ h =>
   cases h with | bind_success _ h =>
    cases h with | bind_success hm h =>
     obtain ⟨rfl,rfl⟩ := (MinValidation.min_success_iff ns.length as.length _ _ _).1 hm
     have hda : Int.ofNat as.length-Int.ofNat (min ns.length as.length)=
       Int.ofNat (as.length-min ns.length as.length) := (Int.ofNat_sub (Nat.min_le_right _ _)).symm
     have hdn : Int.ofNat ns.length-Int.ofNat (min ns.length as.length)=
       Int.ofNat (ns.length-min ns.length as.length) := (Int.ofNat_sub (Nat.min_le_left _ _)).symm
     have ht : (as.drop (as.length-min ns.length as.length)).take (min ns.length as.length)=
         as.drop (as.length-min ns.length as.length) := by
       apply List.take_of_length_le
       simp only [List.length_drop]
       omega
     simp only [hda,hdn,Int.toNat?] at h
     cases h with | bind_success _ h =>
      cases h with | bind_success _ h =>
       cases h with | bind_success _ h =>
        cases h with | bind_success hmake h =>
         obtain ⟨rfl,rfl⟩ := (MakeValidation.make_success_iff valtype .BotT _ _ _ _).1 hmake
         cases h with | bind_success hm _ =>
          cases_type Unit
          exact ⟨_,_,by simpa only [actual,width,ht] using hm⟩

theorem clause2_has_match (c : context) (ns as : List valtype)
    (r : inferresulttype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:2» c (.Ellipses,ns) (.NoEllipses,as))
      start (.success (.of r)) finish) :
    ∃a b, SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c
        (actual (.Ellipses,ns) (.NoEllipses,as)) ns⟩) a (.success (.of ())) b := by
  unfold SpecTec.«$pop:clause:2» at h
  cases h with | bind_success _ h =>
   cases h with | bind_success _ h =>
    cases h with | bind_success hm h =>
     obtain ⟨rfl,rfl⟩ := (MinValidation.min_success_iff ns.length as.length _ _ _).1 hm
     have hda : Int.ofNat as.length-Int.ofNat (min ns.length as.length)=
       Int.ofNat (as.length-min ns.length as.length) := (Int.ofNat_sub (Nat.min_le_right _ _)).symm
     have hdn : Int.ofNat ns.length-Int.ofNat (min ns.length as.length)=
       Int.ofNat (ns.length-min ns.length as.length) := (Int.ofNat_sub (Nat.min_le_left _ _)).symm
     have ht : (as.drop (as.length-min ns.length as.length)).take (min ns.length as.length)=
         as.drop (as.length-min ns.length as.length) := by
       apply List.take_of_length_le
       simp only [List.length_drop]
       omega
     simp only [hda,hdn,Int.toNat?] at h
     cases h with | bind_success _ h =>
      cases h with | bind_success _ h =>
       cases h with | bind_success hm _ =>
        cases_type Unit
        exact ⟨_,_,by simpa only [actual,width,ht] using hm⟩

theorem clause3_has_match (c : context) (ns as : List valtype)
    (r : inferresulttype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:3» c (.NoEllipses,ns) (.NoEllipses,as))
      start (.success (.of r)) finish) :
    ∃a b, SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c
        (actual (.NoEllipses,ns) (.NoEllipses,as)) ns⟩) a (.success (.of ())) b := by
  unfold SpecTec.«$pop:clause:3» at h
  cases h with | bind_success _ h =>
   cases h with | bind_success _ h =>
    cases h with | bind_success hm h =>
     obtain ⟨rfl,rfl⟩ := (MinValidation.min_success_iff ns.length as.length _ _ _).1 hm
     have hda : Int.ofNat as.length-Int.ofNat (min ns.length as.length)=
       Int.ofNat (as.length-min ns.length as.length) := (Int.ofNat_sub (Nat.min_le_right _ _)).symm
     have hdn : Int.ofNat ns.length-Int.ofNat (min ns.length as.length)=
       Int.ofNat (ns.length-min ns.length as.length) := (Int.ofNat_sub (Nat.min_le_left _ _)).symm
     have ht : (as.drop (as.length-min ns.length as.length)).take (min ns.length as.length)=
         as.drop (as.length-min ns.length as.length) := by
       apply List.take_of_length_le
       simp only [List.length_drop]
       omega
     simp only [hda,hdn,Int.toNat?] at h
     cases h with | bind_success _ h =>
      cases h with | bind_success _ h =>
       cases h with | bind_success hm _ =>
        cases_type Unit
        exact ⟨_,_,by simpa only [actual,width,ht] using hm⟩

theorem pop_has_match (c : context) (need available r : inferresulttype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferresulttype,SpecTecCall.«$pop» c need available⟩)
      start (.success (.of r)) finish) :
    ∃a b, SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c (actual need available) need.2⟩)
      a (.success (.of ())) b := by
  rcases need with ⟨ne,ns⟩
  rcases available with ⟨ae,as⟩
  cases h with | call h =>
   change SpecTecExecution.Eval SpecTec.specTecProgram
     (SpecTecExecution.firstSuccess (SpecTec.«$pop_clauses» c (ne,ns) (ae,as)) ())
     start (.success (.of r)) finish at h
   obtain ⟨idx,h⟩ := (SpecTecExecution.firstSuccess_success_iff _ _ _ _ _).1 h
   unfold SpecTec.«$pop_clauses» at h
   rcases h with h|⟨_,h|⟨_,h|⟨_,h|⟨_,h⟩⟩⟩⟩
   · cases ne <;> cases ae
     all_goals try exact clause0_has_match c ns as r _ _ h
     all_goals
       unfold SpecTec.«$pop:clause:0» at h
       cases h with | bind_success hg h =>
        cases hg with | guard_true hg =>
         first | solve | simp [SpecTec.«exec:match:ellipses:Ellipses»,SpecTec.«exec:match:ellipses:NoEllipses»] at hg
               | cases h with | bind_success hg _ =>
                  cases hg with | guard_true hg =>
                   simp [SpecTec.«exec:match:ellipses:Ellipses»,SpecTec.«exec:match:ellipses:NoEllipses»] at hg
   · cases ne <;> cases ae
     all_goals try exact clause1_has_match c ns as r _ _ h
     all_goals
       unfold SpecTec.«$pop:clause:1» at h
       cases h with | bind_success hg h =>
        cases hg with | guard_true hg =>
         first | solve | simp [SpecTec.«exec:match:ellipses:Ellipses»,SpecTec.«exec:match:ellipses:NoEllipses»] at hg
               | cases h with | bind_success hg _ =>
                  cases hg with | guard_true hg =>
                   simp [SpecTec.«exec:match:ellipses:Ellipses»,SpecTec.«exec:match:ellipses:NoEllipses»] at hg
   · cases ne <;> cases ae
     all_goals try exact clause2_has_match c ns as r _ _ h
     all_goals
       unfold SpecTec.«$pop:clause:2» at h
       cases h with | bind_success hg h =>
        cases hg with | guard_true hg =>
         first | solve | simp [SpecTec.«exec:match:ellipses:Ellipses»,SpecTec.«exec:match:ellipses:NoEllipses»] at hg
               | cases h with | bind_success hg _ =>
                  cases hg with | guard_true hg =>
                   simp [SpecTec.«exec:match:ellipses:Ellipses»,SpecTec.«exec:match:ellipses:NoEllipses»] at hg
   · cases ne <;> cases ae
     all_goals try exact clause3_has_match c ns as r _ _ h
     all_goals
       unfold SpecTec.«$pop:clause:3» at h
       cases h with | bind_success hg h =>
        cases hg with | guard_true hg =>
         first | solve | simp [SpecTec.«exec:match:ellipses:Ellipses»,SpecTec.«exec:match:ellipses:NoEllipses»] at hg
               | cases h with | bind_success hg _ =>
                  cases hg with | guard_true hg =>
                   simp [SpecTec.«exec:match:ellipses:Ellipses»,SpecTec.«exec:match:ellipses:NoEllipses»] at hg
   · cases h

theorem pop_plan_complete (c : context) (need available result : inferresulttype)
    (start finish : Nat) (hr : CandidateTypeReady.Ready c)
    (hn : ∀t∈need.2,CandidateValMatch.InTableVal c t)
    (ha : ∀t∈available.2,CandidateValMatch.InTableVal c t)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferresulttype,SpecTecCall.«$pop» c need available⟩)
      start (.success (.of result)) finish) :
    popPlan c need available=some result ∧ finish=start := by
  obtain ⟨a,b,hm⟩ := pop_has_match c need available result start finish h
  have hb := MatchResulttypeDecision.match_pairs_of_resulttype_success c _ _ a b hr
    (actual_table c need available ha) hn hm
  have hp : popPlan c need available=some (remaining need available) := by simp [popPlan,hb]
  have hs := pop_plan_sound c need available _ start hr hn ha hp
  have hd : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request x y hx; cases hx
  obtain ⟨he,hf⟩ := SpecTecExecution.eval_deterministic hd h hs
  cases he
  exact ⟨hp,hf⟩

#print axioms pop_plan_sound
#print axioms pop_plan_complete
end properties.wasm_module_ok.ConstructiveBodyPopPlans
