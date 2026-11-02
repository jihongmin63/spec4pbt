import properties.wasm_module_ok.SubtypeIterMatchTrace
import properties.wasm_module_ok.RectypeSourceValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeSubMatchTrace

theorem rectype_iter6_member
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (ns : List SpecTec.n) (sts : List SpecTec.subtype)
    (start finish i : Nat) (n : SpecTec.n) (st : SpecTec.subtype)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6»
        c x ns sts⟩) start (.success (.of ())) finish)
    (hn : ns[i]? = some n) (hs : sts[i]? = some st) :
    ∃ callStart callFinish : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_sub_ok
          c (x + n) st⟩)
        callStart (.success (.of ())) callFinish := by
  induction ns generalizing sts start finish i with
  | nil => simp at hn
  | cons headN tailN ih =>
      cases sts with
      | nil => simp at hs
      | cons headSt tailSt =>
          cases h with
          | call hbody =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTecExecution.firstSuccess
                  (SpecTec.«Rectype_ok:rule:iter:6_clauses»
                    c x (headN :: tailN) (headSt :: tailSt)) ())
                start (.success (.of ())) finish at hbody
              obtain ⟨idx, hselected⟩ :=
                (SpecTecExecution.firstSuccess_success_iff
                  (SpecTec.«Rectype_ok:rule:iter:6_clauses»
                    c x (headN :: tailN) (headSt :: tailSt)) ()
                  start (.of ()) finish).1 hbody
              unfold SpecTec.«Rectype_ok:rule:iter:6_clauses» at hselected
              cases hselected with
              | here h0 =>
                  unfold SpecTec.«Rectype_ok:rule:iter:6:clause:0» at h0
                  cases h0
              | next _ hrest =>
                  cases hrest with
                  | here h1 =>
                      unfold SpecTec.«Rectype_ok:rule:iter:6:clause:1» at h1
                      cases h1 with
                      | bind_success hhead htailplan =>
                          cases htailplan with
                          | bind_success htail _ =>
                              cases i with
                              | zero =>
                                  simp only [List.getElem?_cons_zero,
                                    Option.some.injEq] at hn hs
                                  subst n
                                  subst st
                                  exact ⟨_, _, hhead⟩
                              | succ j =>
                                  exact ih tailSt _ _ j htail hn hs
                  | next _ hrest => cases hrest

theorem rectype_ok_extract_sub_iters
    (before after : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish) :
    ∃ ns : List SpecTec.n,
    ∃ dts : List SpecTec.deftype,
      after = {before with TYPES := before.TYPES ++ dts} ∧
      ns.length = sts.length ∧
      ∃ iter5Start iter5Finish iter6Start iter6Finish : Nat,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5»
            after sts⟩)
          iter5Start (.success (.of ())) iter5Finish ∧
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6»
            after before.TYPES.length ns sts⟩)
          iter6Start (.success (.of ())) iter6Finish := by
  cases hrect with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Rectype_ok_clauses before (.RecT sts)) ())
        start (.success (.of after)) finish at hbody
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.firstSuccess_success_iff
          (SpecTec.Rectype_ok_clauses before (.RecT sts)) ()
          start (.of after) finish).1 hbody
      unfold SpecTec.Rectype_ok_clauses at hselected
      cases hselected with
      | here h0 =>
          unfold SpecTec.«Rectype_ok:clause:0» at h0
          dsimp only at h0
          cases h0 with
          | bind_success hrange h1 =>
              rename_i ns
              dsimp only at h1
              cases h1 with
              | bind_success hroll h2 =>
                  dsimp only at h2
                  cases h2 with
                  | bind_success hsubst h3 =>
                      rename_i dts
                      dsimp only at h3
                      cases h3 with
                      | bind_success hiter5 h4 =>
                          dsimp only at h4
                          cases h4 with
                          | bind_success hlength h5 =>
                              cases hlength with
                              | guard_true hlen =>
                                  dsimp only at h5
                                  cases h5 with
                                  | bind_success hiter6 h6 =>
                                      rename_i v
                                      cases h6
                                      cases v
                                      exact ⟨ns, dts, rfl, hlen.symm,
                                        _, _, _, _, hiter5, hiter6⟩
      | next _ hrest => cases hrest

theorem rectype_ok_supertype_static_call
    (before after : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish i : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hmem : ht ∈ hts) :
    ∃ n : SpecTec.n,
    ∃ y : SpecTec.typeidx,
    ∃ callStart callFinish : Nat,
      ht = .VarHT (.StatX y) ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.Subtype_sub_ok' after
            (before.TYPES.length + n) strt (.VarHT (.StatX y))⟩)
        callStart (.success (.of ())) callFinish := by
  obtain ⟨ns, dts, hafter, hlen,
      iter5Start, iter5Finish, iter6Start, iter6Finish,
      hiter5, hiter6⟩ :=
    rectype_ok_extract_sub_iters before after sts start finish hrect
  have hiNs : i < ns.length := by rw [hlen]; exact hi
  have hn : ns[i]? = some ns[i] := List.getElem?_eq_getElem hiNs
  obtain ⟨callStart, callFinish, hsub⟩ :=
    rectype_iter6_member after before.TYPES.length ns sts
      iter6Start iter6Finish i ns[i] (.SubT fin hts strt)
      hiter6 hn hsource
  obtain ⟨y, hshape, staticStart, staticFinish, hstatic⟩ :=
    SubtypeIterMatchTrace.subtype_sub_ok_static_call
      after (before.TYPES.length + ns[i]) fin hts strt
      callStart callFinish hsub ht hmem
  exact ⟨ns[i], y, staticStart, staticFinish, hshape, hstatic⟩

theorem rectype_ok_supertype_match_pair
    (before after : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish i : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hmem : ht ∈ hts) :
    ∃ n : SpecTec.n,
    ∃ y : SpecTec.typeidx,
    ∃ dt : SpecTec.deftype,
    ∃ finU : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
    ∃ matchStart matchFinish : Nat,
      ht = .VarHT (.StatX y) ∧
      after.TYPES[y]? = some dt ∧
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT finU htsU strtU) ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype»
          after.TYPES strt strtU⟩)
        matchStart (.success (.of true)) matchFinish ∧
      y < before.TYPES.length + n ∧ finU = .NoFinal := by
  obtain ⟨n, y, callStart, callFinish, hshape, hcall⟩ :=
    rectype_ok_supertype_static_call
      before after sts start finish i fin hts strt ht
      hrect hi hsource hmem
  obtain ⟨dt, finU, htsU, strtU, matchStart,
      hlookup, hunroll, hmatch, hlt, hfin⟩ :=
    SubtypeStaticMatchTrace.subtype_sub_ok_static_match_trace
      after (before.TYPES.length + n) y strt callStart callFinish hcall
  have hpure :
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT finU htsU strtU) :=
    (UnrollInterface.unrolldt_success_iff dt
      (.SubT finU htsU strtU) callStart matchStart).1 hunroll |>.1
  exact ⟨n, y, dt, finU, htsU, strtU, matchStart, callFinish,
    hshape, hlookup, hpure, hmatch, hlt, hfin⟩

theorem rectype_ok_source_reference_lookup
    (before after : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish i : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (raw : SpecTec.heaptype)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hmem : raw ∈ ReadyMatchReachability.sourceHeaptypes strt) :
    raw ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ k : Nat, ∃ dtK : SpecTec.deftype,
        after.TYPES[k]? = some dtK ∧ raw = .VarHT (.StatX k) := by
  rcases RectypeSourceValidation.rectype_ok_source_heaptype_base_or_stat
      before after sts start finish i fin hts strt raw
      hrect hi hsource hmem with hbase | ⟨k, hraw, hk⟩
  · exact Or.inl hbase
  · exact Or.inr ⟨k, after.TYPES[k], List.getElem?_eq_getElem hk, hraw⟩

theorem rectype_ok_supertype_indexed_match_pair
    (before after : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish i : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (hbefore : ValidatedTypeChain.ValidatedTypes before)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hmem : ht ∈ hts) :
    ∃ n : SpecTec.n,
    ∃ y : SpecTec.typeidx,
    ∃ dt : SpecTec.deftype,
    ∃ finU : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
    ∃ matchStart matchFinish : Nat,
      ht = .VarHT (.StatX y) ∧
      after.TYPES[y]? = some dt ∧
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT finU htsU strtU) ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype»
          after.TYPES strt strtU⟩)
        matchStart (.success (.of true)) matchFinish ∧
      y < before.TYPES.length + n ∧ finU = .NoFinal ∧
      (∀ raw, raw ∈ ReadyMatchReachability.sourceHeaptypes strt →
        raw ∈ HeaptypeValidation.baseHeaptypes ∨
          ∃ k : Nat, ∃ dtK : SpecTec.deftype,
            after.TYPES[k]? = some dtK ∧ raw = .VarHT (.StatX k)) ∧
      (∀ raw, raw ∈ ReadyMatchReachability.sourceHeaptypes strtU →
        raw ∈ HeaptypeValidation.baseHeaptypes ∨
          ∃ k : Nat, ∃ dtK : SpecTec.deftype,
            after.TYPES[k]? = some dtK ∧ raw = .DefHT dtK) := by
  obtain ⟨n, y, dt, finU, htsU, strtU, matchStart, matchFinish,
      hshape, hlookup, hpure, hmatch, hlt, hfin⟩ :=
    rectype_ok_supertype_match_pair before after sts start finish i
      fin hts strt ht hrect hi hsource hmem
  have hready : CandidateNestedReady.nestedTableReady after = true :=
    CandidateNestedReady.rectype_success_nestedTableReady
      before after sts start finish hbefore hrect
  have hy : y < after.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  obtain ⟨dt', fin', hts', strtU', hlookup', hunroll', htarget⟩ :=
    (CandidateNestedReady.nestedTableReady_true_iff after).mp hready y hy
  have hdt : dt' = dt := by
    rw [hlookup] at hlookup'
    cases hlookup'
    rfl
  subst dt'
  rw [hpure] at hunroll'
  cases hunroll'
  refine ⟨n, y, dt, finU, htsU, strtU, matchStart, matchFinish,
    hshape, hlookup, hpure, hmatch, hlt, hfin, ?_, htarget⟩
  intro raw hraw
  exact rectype_ok_source_reference_lookup before after sts
    start finish i fin hts strt raw hrect hi hsource hraw

end properties.wasm_module_ok.RectypeSubMatchTrace
