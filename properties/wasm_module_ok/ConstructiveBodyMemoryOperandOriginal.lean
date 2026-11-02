import properties.wasm_module_ok.ConstructiveBodyMemorySuffix
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryOperandOriginal
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEvalReduction ConstructiveBodyMemoryOperands ConstructiveBodyMemorySuffix ConstructiveBodyMemoryBounds ConstructiveBodyScalarSizes

theorem loadop_ok_some (c : context) (ty : numtype) (align offset : Nat) (pt : packtype) (ext : extension)
    (got : numtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨numtype,SpecTecCall.Loadop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : loadop_)⟩)
      n (.success (.of got)) finish) :
    ∃addr lim,c.MEMS[0]?=some (.MemoryT addr lim) ∧ OffsetBound addr offset ∧
      align≤packLog pt ∧ packSize pt<Int.ofNat (2^numLog ty) ∧ got=ty ∧ finish=n := by
  cases h with | call h =>
    obtain ⟨idx,hs⟩ := (firstSuccess_success_iff (SpecTec.Loadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : loadop_)) () n (.of got) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Loadop_ok:clause:0» at h
      obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
      rw [bind_known _ _ _ _ _ _ (scalar_size ty n)] at h
      cases h with | bind_success hp h =>
        rename_i middle unit
        cases unit
        obtain ⟨hpackBound,hn⟩ := pack_original (2^numLog ty) pt n middle hp
        subst middle
        rw [bind_known _ _ _ _ _ _ (pack_size pt n)] at h
        obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
        change Eval SpecTec.specTecProgram (tail c .I32AT offset ty) n (.success (.of got)) finish at h
        obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I32AT offset ty got n finish h
        have hk : packLog pt<4096 := by cases pt <;> decide
        rw [pack_pow] at ha
        exact ⟨.I32AT,lim,hx,hoff,(alignment align (packLog pt) hk).1 ha,hpackBound,he,hn⟩
    | next _ hs =>
      cases hs with
      | here h =>
        unfold SpecTec.«Loadop_ok:clause:1» at h
        obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
        rw [bind_known _ _ _ _ _ _ (scalar_size ty n)] at h
        cases h with | bind_success hp h =>
          rename_i middle unit
          cases unit
          obtain ⟨hpackBound,hn⟩ := pack_original (2^numLog ty) pt n middle hp
          subst middle
          rw [bind_known _ _ _ _ _ _ (pack_size pt n)] at h
          obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
          change Eval SpecTec.specTecProgram (tail c .I64AT offset ty) n (.success (.of got)) finish at h
          obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I64AT offset ty got n finish h
          have hk : packLog pt<4096 := by cases pt <;> decide
          rw [pack_pow] at ha
          exact ⟨.I64AT,lim,hx,hoff,(alignment align (packLog pt) hk).1 ha,hpackBound,he,hn⟩
      | next _ hs =>
        cases hs with
        | here h =>
          unfold SpecTec.«Loadop_ok:clause:2» at h
          obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
          cases hg
        | next _ hs =>
          cases hs with
          | here h =>
            unfold SpecTec.«Loadop_ok:clause:3» at h
            obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
            cases hg
          | next _ hs =>
            cases hs

theorem loadop_ok_none (c : context) (ty : numtype) (align offset : Nat)
    (got : numtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨numtype,SpecTecCall.Loadop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : loadop_)⟩)
      n (.success (.of got)) finish) :
    ∃addr lim,c.MEMS[0]?=some (.MemoryT addr lim) ∧ OffsetBound addr offset ∧
      align≤numLog ty ∧ got=ty ∧ finish=n := by
  cases h with | call h =>
    obtain ⟨idx,hs⟩ := (firstSuccess_success_iff (SpecTec.Loadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : loadop_)) () n (.of got) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Loadop_ok:clause:0» at h
      obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
      cases hg
    | next _ hs =>
      cases hs with
      | here h =>
        unfold SpecTec.«Loadop_ok:clause:1» at h
        obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
        cases hg
      | next _ hs =>
        cases hs with
        | here h =>
          unfold SpecTec.«Loadop_ok:clause:2» at h
          obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
          rw [bind_known _ _ _ _ _ _ (scalar_size ty n)] at h
          obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
          change Eval SpecTec.specTecProgram (tail c .I32AT offset ty) n (.success (.of got)) finish at h
          obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I32AT offset ty got n finish h
          have hk : numLog ty<4096 := by cases ty <;> decide
          exact ⟨.I32AT,lim,hx,hoff,(alignment align (numLog ty) hk).1 ha,he,hn⟩
        | next _ hs =>
          cases hs with
          | here h =>
            unfold SpecTec.«Loadop_ok:clause:3» at h
            obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
            rw [bind_known _ _ _ _ _ _ (scalar_size ty n)] at h
            obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
            change Eval SpecTec.specTecProgram (tail c .I64AT offset ty) n (.success (.of got)) finish at h
            obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I64AT offset ty got n finish h
            have hk : numLog ty<4096 := by cases ty <;> decide
            exact ⟨.I64AT,lim,hx,hoff,(alignment align (numLog ty) hk).1 ha,he,hn⟩
          | next _ hs =>
            cases hs

theorem storeop_ok_some (c : context) (ty : numtype) (align offset : Nat) (pt : packtype)
    (got : numtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨numtype,SpecTecCall.Storeop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some pt } : storeop_)⟩)
      n (.success (.of got)) finish) :
    ∃addr lim,c.MEMS[0]?=some (.MemoryT addr lim) ∧ OffsetBound addr offset ∧
      align≤packLog pt ∧ packSize pt<Int.ofNat (2^numLog ty) ∧ got=ty ∧ finish=n := by
  cases h with | call h =>
    obtain ⟨idx,hs⟩ := (firstSuccess_success_iff (SpecTec.Storeop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some pt } : storeop_)) () n (.of got) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Storeop_ok:clause:0» at h
      obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
      rw [bind_known _ _ _ _ _ _ (scalar_size ty n)] at h
      cases h with | bind_success hp h =>
        rename_i middle unit
        cases unit
        obtain ⟨hpackBound,hn⟩ := pack_original (2^numLog ty) pt n middle hp
        subst middle
        rw [bind_known _ _ _ _ _ _ (pack_size pt n)] at h
        obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
        change Eval SpecTec.specTecProgram (tail c .I32AT offset ty) n (.success (.of got)) finish at h
        obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I32AT offset ty got n finish h
        have hk : packLog pt<4096 := by cases pt <;> decide
        rw [pack_pow] at ha
        exact ⟨.I32AT,lim,hx,hoff,(alignment align (packLog pt) hk).1 ha,hpackBound,he,hn⟩
    | next _ hs =>
      cases hs with
      | here h =>
        unfold SpecTec.«Storeop_ok:clause:1» at h
        obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
        rw [bind_known _ _ _ _ _ _ (scalar_size ty n)] at h
        cases h with | bind_success hp h =>
          rename_i middle unit
          cases unit
          obtain ⟨hpackBound,hn⟩ := pack_original (2^numLog ty) pt n middle hp
          subst middle
          rw [bind_known _ _ _ _ _ _ (pack_size pt n)] at h
          obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
          change Eval SpecTec.specTecProgram (tail c .I64AT offset ty) n (.success (.of got)) finish at h
          obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I64AT offset ty got n finish h
          have hk : packLog pt<4096 := by cases pt <;> decide
          rw [pack_pow] at ha
          exact ⟨.I64AT,lim,hx,hoff,(alignment align (packLog pt) hk).1 ha,hpackBound,he,hn⟩
      | next _ hs =>
        cases hs with
        | here h =>
          unfold SpecTec.«Storeop_ok:clause:2» at h
          obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
          cases hg
        | next _ hs =>
          cases hs with
          | here h =>
            unfold SpecTec.«Storeop_ok:clause:3» at h
            obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
            cases hg
          | next _ hs =>
            cases hs

theorem storeop_ok_none (c : context) (ty : numtype) (align offset : Nat)
    (got : numtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨numtype,SpecTecCall.Storeop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : storeop_)⟩)
      n (.success (.of got)) finish) :
    ∃addr lim,c.MEMS[0]?=some (.MemoryT addr lim) ∧ OffsetBound addr offset ∧
      align≤numLog ty ∧ got=ty ∧ finish=n := by
  cases h with | call h =>
    obtain ⟨idx,hs⟩ := (firstSuccess_success_iff (SpecTec.Storeop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : storeop_)) () n (.of got) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Storeop_ok:clause:0» at h
      obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
      cases hg
    | next _ hs =>
      cases hs with
      | here h =>
        unfold SpecTec.«Storeop_ok:clause:1» at h
        obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
        cases hg
      | next _ hs =>
        cases hs with
        | here h =>
          unfold SpecTec.«Storeop_ok:clause:2» at h
          obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
          rw [bind_known _ _ _ _ _ _ (scalar_size ty n)] at h
          obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
          change Eval SpecTec.specTecProgram (tail c .I32AT offset ty) n (.success (.of got)) finish at h
          obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I32AT offset ty got n finish h
          have hk : numLog ty<4096 := by cases ty <;> decide
          exact ⟨.I32AT,lim,hx,hoff,(alignment align (numLog ty) hk).1 ha,he,hn⟩
        | next _ hs =>
          cases hs with
          | here h =>
            unfold SpecTec.«Storeop_ok:clause:3» at h
            obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
            rw [bind_known _ _ _ _ _ _ (scalar_size ty n)] at h
            obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
            change Eval SpecTec.specTecProgram (tail c .I64AT offset ty) n (.success (.of got)) finish at h
            obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I64AT offset ty got n finish h
            have hk : numLog ty<4096 := by cases ty <;> decide
            exact ⟨.I64AT,lim,hx,hoff,(alignment align (numLog ty) hk).1 ha,he,hn⟩
          | next _ hs =>
            cases hs

theorem vloadop_ok_some (c : context) (ty : vectype) (align offset : Nat) (pt : packtype) (ext : vextension)
    (got : vectype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨vectype,SpecTecCall.Vloadop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : vloadop_)⟩)
      n (.success (.of got)) finish) :
    ∃addr lim,c.MEMS[0]?=some (.MemoryT addr lim) ∧ OffsetBound addr offset ∧
      align≤packLog pt ∧ packSize pt<Int.ofNat (2^4) ∧ got=ty ∧ finish=n := by
  cases h with | call h =>
    obtain ⟨idx,hs⟩ := (firstSuccess_success_iff (SpecTec.Vloadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : vloadop_)) () n (.of got) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Vloadop_ok:clause:0» at h
      obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
      rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty n)] at h
      cases h with | bind_success hp h =>
        rename_i middle unit
        cases unit
        obtain ⟨hpackBound,hn⟩ := pack_original (2^4) pt n middle hp
        subst middle
        rw [bind_known _ _ _ _ _ _ (pack_size pt n)] at h
        obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
        change Eval SpecTec.specTecProgram (tail c .I32AT offset ty) n (.success (.of got)) finish at h
        obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I32AT offset ty got n finish h
        have hk : packLog pt<4096 := by cases pt <;> decide
        rw [pack_pow] at ha
        exact ⟨.I32AT,lim,hx,hoff,(alignment align (packLog pt) hk).1 ha,hpackBound,he,hn⟩
    | next _ hs =>
      cases hs with
      | here h =>
        unfold SpecTec.«Vloadop_ok:clause:1» at h
        obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
        rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty n)] at h
        cases h with | bind_success hp h =>
          rename_i middle unit
          cases unit
          obtain ⟨hpackBound,hn⟩ := pack_original (2^4) pt n middle hp
          subst middle
          rw [bind_known _ _ _ _ _ _ (pack_size pt n)] at h
          obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
          change Eval SpecTec.specTecProgram (tail c .I64AT offset ty) n (.success (.of got)) finish at h
          obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I64AT offset ty got n finish h
          have hk : packLog pt<4096 := by cases pt <;> decide
          rw [pack_pow] at ha
          exact ⟨.I64AT,lim,hx,hoff,(alignment align (packLog pt) hk).1 ha,hpackBound,he,hn⟩
      | next _ hs =>
        cases hs with
        | here h =>
          unfold SpecTec.«Vloadop_ok:clause:2» at h
          obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
          cases hg
        | next _ hs =>
          cases hs with
          | here h =>
            unfold SpecTec.«Vloadop_ok:clause:3» at h
            obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
            cases hg
          | next _ hs =>
            cases hs

theorem vloadop_ok_none (c : context) (ty : vectype) (align offset : Nat)
    (got : vectype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨vectype,SpecTecCall.Vloadop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : vloadop_)⟩)
      n (.success (.of got)) finish) :
    ∃addr lim,c.MEMS[0]?=some (.MemoryT addr lim) ∧ OffsetBound addr offset ∧
      align≤4 ∧ got=ty ∧ finish=n := by
  cases h with | call h =>
    obtain ⟨idx,hs⟩ := (firstSuccess_success_iff (SpecTec.Vloadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : vloadop_)) () n (.of got) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Vloadop_ok:clause:0» at h
      obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
      cases hg
    | next _ hs =>
      cases hs with
      | here h =>
        unfold SpecTec.«Vloadop_ok:clause:1» at h
        obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
        cases hg
      | next _ hs =>
        cases hs with
        | here h =>
          unfold SpecTec.«Vloadop_ok:clause:2» at h
          obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
          rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty n)] at h
          obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
          change Eval SpecTec.specTecProgram (tail c .I32AT offset ty) n (.success (.of got)) finish at h
          obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I32AT offset ty got n finish h
          have hk : 4<4096 := by decide
          exact ⟨.I32AT,lim,hx,hoff,(alignment align (4) hk).1 ha,he,hn⟩
        | next _ hs =>
          cases hs with
          | here h =>
            unfold SpecTec.«Vloadop_ok:clause:3» at h
            obtain ⟨hg,h⟩ := (bind_guard _ _ _ _ _).1 h
            rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty n)] at h
            obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
            change Eval SpecTec.specTecProgram (tail c .I64AT offset ty) n (.success (.of got)) finish at h
            obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I64AT offset ty got n finish h
            have hk : 4<4096 := by decide
            exact ⟨.I64AT,lim,hx,hoff,(alignment align (4) hk).1 ha,he,hn⟩
          | next _ hs =>
            cases hs

theorem vstoreop_ok_void (c : context) (ty : vectype) (align offset : Nat)
    (got : vectype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨vectype,SpecTecCall.Vstoreop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=.VOID } : vstoreop_)⟩)
      n (.success (.of got)) finish) :
    ∃addr lim,c.MEMS[0]?=some (.MemoryT addr lim) ∧ OffsetBound addr offset ∧
      align≤4 ∧ got=ty ∧ finish=n := by
  cases h with | call h =>
    obtain ⟨idx,hs⟩ := (firstSuccess_success_iff (SpecTec.Vstoreop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=.VOID } : vstoreop_)) () n (.of got) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Vstoreop_ok:clause:0» at h
      rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty n)] at h
      obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
      change Eval SpecTec.specTecProgram (tail c .I32AT offset ty) n (.success (.of got)) finish at h
      obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I32AT offset ty got n finish h
      have hk : 4<4096 := by decide
      exact ⟨.I32AT,lim,hx,hoff,(alignment align (4) hk).1 ha,he,hn⟩
    | next _ hs =>
      cases hs with
      | here h =>
        unfold SpecTec.«Vstoreop_ok:clause:1» at h
        rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty n)] at h
        obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
        change Eval SpecTec.specTecProgram (tail c .I64AT offset ty) n (.success (.of got)) finish at h
        obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I64AT offset ty got n finish h
        have hk : 4<4096 := by decide
        exact ⟨.I64AT,lim,hx,hoff,(alignment align (4) hk).1 ha,he,hn⟩
      | next _ hs =>
        cases hs

theorem vlaneop_ok_pack (c : context) (ty : vectype) (align offset : Nat) (pt : packtype)
    (got : vectype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨vectype,SpecTecCall.Vlaneop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=pt } : vlaneop_)⟩)
      n (.success (.of got)) finish) :
    ∃addr lim,c.MEMS[0]?=some (.MemoryT addr lim) ∧ OffsetBound addr offset ∧
      align≤packLog pt ∧ packSize pt<Int.ofNat (2^4) ∧ got=ty ∧ finish=n := by
  cases h with | call h =>
    obtain ⟨idx,hs⟩ := (firstSuccess_success_iff (SpecTec.Vlaneop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=pt } : vlaneop_)) () n (.of got) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Vlaneop_ok:clause:0» at h
      rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty n)] at h
      cases h with | bind_success hp h =>
        rename_i middle unit
        cases unit
        obtain ⟨hpackBound,hn⟩ := pack_original (2^4) pt n middle hp
        subst middle
        rw [bind_known _ _ _ _ _ _ (pack_size pt n)] at h
        obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
        change Eval SpecTec.specTecProgram (tail c .I32AT offset ty) n (.success (.of got)) finish at h
        obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I32AT offset ty got n finish h
        have hk : packLog pt<4096 := by cases pt <;> decide
        rw [pack_pow] at ha
        exact ⟨.I32AT,lim,hx,hoff,(alignment align (packLog pt) hk).1 ha,hpackBound,he,hn⟩
    | next _ hs =>
      cases hs with
      | here h =>
        unfold SpecTec.«Vlaneop_ok:clause:1» at h
        rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty n)] at h
        cases h with | bind_success hp h =>
          rename_i middle unit
          cases unit
          obtain ⟨hpackBound,hn⟩ := pack_original (2^4) pt n middle hp
          subst middle
          rw [bind_known _ _ _ _ _ _ (pack_size pt n)] at h
          obtain ⟨ha,h⟩ := (bind_guard _ _ _ _ _).1 h
          change Eval SpecTec.specTecProgram (tail c .I64AT offset ty) n (.success (.of got)) finish at h
          obtain ⟨lim,hx,hoff,he,hn⟩ := tail_original c .I64AT offset ty got n finish h
          have hk : packLog pt<4096 := by cases pt <;> decide
          rw [pack_pow] at ha
          exact ⟨.I64AT,lim,hx,hoff,(alignment align (packLog pt) hk).1 ha,hpackBound,he,hn⟩
      | next _ hs =>
        cases hs

#print axioms loadop_ok_some
#print axioms vlaneop_ok_pack
end properties.wasm_module_ok.ConstructiveBodyMemoryOperandOriginal
