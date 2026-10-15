import SpecTecDecl0133

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$split_text_clauses» (input0 : _root_.String) (input1 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$split_text:clause:0»  input0 input1), fun (_ : _root_.Unit) => .abort "builtin $split_text failed"]


noncomputable def «$concat_text:clause:0» (input0 : (_root_.List _root_.String)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «t*» : (_root_.List _root_.String) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «t*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure (("" : _root_.String))))))


noncomputable def «$concat_text:clause:1» (input0 : (_root_.List _root_.String)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «t*» : (_root_.List _root_.String) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «t*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «t*» with | «exec:2» :: «exec:1» => (let t_h : _root_.String := «exec:2»; (let «t_t*» : (_root_.List _root_.String) := «exec:1»; (.bind (.call ⟨_root_.String, SpecTecCall.«$concat_text» «t_t*»⟩) (fun («exec:3» : _root_.String) => (let «eval:0» : _root_.String := «exec:3»; (.pure (((t_h ++ «eval:0») : _root_.String)))))))) | [] => .unmatch))))


noncomputable def «$concat_text_clauses» (input0 : (_root_.List _root_.String)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$concat_text:clause:0»  input0), fun (_ : _root_.Unit) => («$concat_text:clause:1»  input0)]


noncomputable def «$join_text:clause:0» (input0 : (_root_.List _root_.String)) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «t*» : (_root_.List _root_.String) := input0; (let t_sep : _root_.String := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «t*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure (("" : _root_.String)))))))


noncomputable def «$join_text:clause:1» (input0 : (_root_.List _root_.String)) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «t*» : (_root_.List _root_.String) := input0; (let t_sep : _root_.String := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «t*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «t*» with | «exec:2» :: «exec:1» => (let t_h : _root_.String := «exec:2»; (match «exec:1» with | [] => (.pure ((t_h : _root_.String))) | _ :: _ => .unmatch)) | [] => .unmatch)))))


noncomputable def «$join_text:clause:2» (input0 : (_root_.List _root_.String)) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «t'*» : (_root_.List _root_.String) := input0; (let t_sep : _root_.String := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «t'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «t'*» with | «exec:2» :: «exec:1» => (let t_h1 : _root_.String := «exec:2»; (let «t*» : (_root_.List _root_.String) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «t*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «t*» with | «exec:4» :: «exec:3» => (let t_h2 : _root_.String := «exec:4»; (let «t_t*» : (_root_.List _root_.String) := «exec:3»; (.bind (.call ⟨_root_.String, SpecTecCall.«$join_text» (t_h2 :: «t_t*») t_sep⟩) (fun («exec:5» : _root_.String) => (let «eval:0» : _root_.String := «exec:5»; (.pure ((((t_h1 ++ t_sep) ++ «eval:0») : _root_.String)))))))) | [] => .unmatch))))) | [] => .unmatch)))))


noncomputable def «$join_text_clauses» (input0 : (_root_.List _root_.String)) (input1 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$join_text:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$join_text:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$join_text:clause:2»  input0 input1)]


noncomputable def «$replace_text':clause:0» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) (input4 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n_len : _root_.Nat := input0; (let n_len' : _root_.Nat := input1; (let t : _root_.String := input2; (let t_old : _root_.String := input3; (let t_new : _root_.String := input4; (.bind (.guard (n_len' = n_len)) (fun (_ : Unit) => (.pure ((t : _root_.String))))))))))


noncomputable def «$replace_text':clause:1» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) (input4 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n : _root_.Nat := input0; (let n_len : _root_.Nat := input1; (let t : _root_.String := input2; (let t_old : _root_.String := input3; (let t_new : _root_.String := input4; (.bind (.guard ((n < n_len))) (fun (_ : Unit) => (.bind (.guard ((n < (_root_.String.utf8ByteSize t)))) (fun (_ : Unit) => (.bind (SpecTecExecution.require (((n + (1 : _root_.Nat)) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t n (1 : _root_.Nat))) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((n < (_root_.String.utf8ByteSize t))) "update index out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require (((_root_.String.utf8ByteSize t_new) = (1 : _root_.Nat))) "text update requires one byte") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextUpdateValid t n t_new)) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (.call ⟨_root_.String, SpecTecCall.«$ite» _root_.String (_root_.Decidable.decide ((_root_.specTecTextSlice t n (1 : _root_.Nat)) = t_old)) (_root_.specTecTextUpdate t n t_new) t⟩) (fun («exec:1» : _root_.String) => (let «eval:0» : _root_.String := «exec:1»; (let t_replaced : _root_.String := «eval:0»; (.bind (.call ⟨_root_.String, SpecTecCall.«$replace_text'» (n + (1 : _root_.Nat)) n_len t_replaced t_old t_new⟩) (fun («exec:2» : _root_.String) => (let «eval:1» : _root_.String := «exec:2»; (.pure ((«eval:1» : _root_.String)))))))))))))))))))))))))))))


noncomputable def «$replace_text'_clauses» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) (input4 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$replace_text':clause:0»  input0 input1 input2 input3 input4), fun (_ : _root_.Unit) => («$replace_text':clause:1»  input0 input1 input2 input3 input4)]


noncomputable def «$replace_text:clause:0» (input0 : _root_.String) (input1 : _root_.String) (input2 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_old : _root_.String := input1; (let t_new : _root_.String := input2; (.bind (.call ⟨_root_.String, SpecTecCall.«$replace_text'» (0 : _root_.Nat) (_root_.String.utf8ByteSize t) t t_old t_new⟩) (fun («exec:1» : _root_.String) => (let «eval:0» : _root_.String := «exec:1»; (.pure ((«eval:0» : _root_.String)))))))))


noncomputable def «$replace_text_clauses» (input0 : _root_.String) (input1 : _root_.String) (input2 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$replace_text:clause:0»  input0 input1 input2)]


noncomputable def «$replace_text_except':clause:0» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) (input4 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n_len : _root_.Nat := input0; (let n_len' : _root_.Nat := input1; (let t : _root_.String := input2; (let t_old : _root_.String := input3; (let t_new : _root_.String := input4; (.bind (.guard (n_len' = n_len)) (fun (_ : Unit) => (.pure ((t : _root_.String))))))))))


noncomputable def «$replace_text_except':clause:1» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) (input4 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n : _root_.Nat := input0; (let n_len : _root_.Nat := input1; (let t : _root_.String := input2; (let t_old : _root_.String := input3; (let t_new : _root_.String := input4; (.bind (.guard ((n < n_len))) (fun (_ : Unit) => (.bind (.guard ((n < (_root_.String.utf8ByteSize t)))) (fun (_ : Unit) => (.bind (SpecTecExecution.require (((n + (1 : _root_.Nat)) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t n (1 : _root_.Nat))) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((n < (_root_.String.utf8ByteSize t))) "update index out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require (((_root_.String.utf8ByteSize t_new) = (1 : _root_.Nat))) "text update requires one byte") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextUpdateValid t n t_new)) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (.call ⟨_root_.String, SpecTecCall.«$ite» _root_.String (_root_.Decidable.decide ((_root_.specTecTextSlice t n (1 : _root_.Nat)) = t_old)) t (_root_.specTecTextUpdate t n t_new)⟩) (fun («exec:1» : _root_.String) => (let «eval:0» : _root_.String := «exec:1»; (let t_replaced : _root_.String := «eval:0»; (.bind (.call ⟨_root_.String, SpecTecCall.«$replace_text_except'» (n + (1 : _root_.Nat)) n_len t_replaced t_old t_new⟩) (fun («exec:2» : _root_.String) => (let «eval:1» : _root_.String := «exec:2»; (.pure ((«eval:1» : _root_.String)))))))))))))))))))))))))))))


noncomputable def «$replace_text_except'_clauses» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) (input4 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$replace_text_except':clause:0»  input0 input1 input2 input3 input4), fun (_ : _root_.Unit) => («$replace_text_except':clause:1»  input0 input1 input2 input3 input4)]


noncomputable def «$replace_text_except:clause:0» (input0 : _root_.String) (input1 : _root_.String) (input2 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_old : _root_.String := input1; (let t_new : _root_.String := input2; (.bind (.call ⟨_root_.String, SpecTecCall.«$replace_text_except'» (0 : _root_.Nat) (_root_.String.utf8ByteSize t) t t_old t_new⟩) (fun («exec:1» : _root_.String) => (let «eval:0» : _root_.String := «exec:1»; (.pure ((«eval:0» : _root_.String)))))))))


noncomputable def «$replace_text_except_clauses» (input0 : _root_.String) (input1 : _root_.String) (input2 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$replace_text_except:clause:0»  input0 input1 input2)]


noncomputable def «$strip_prefix:clause:0» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let p : _root_.String := input1; (.bind (.guard (_root_.specTecTextSliceValid t (p).utf8ByteSize ((t).utf8ByteSize - (p).utf8ByteSize))) (fun (_ : Unit) => (let r : _root_.String := (_root_.specTecTextSlice t (p).utf8ByteSize ((t).utf8ByteSize - (p).utf8ByteSize)); (.bind (.guard (t = (p ++ r))) (fun (_ : Unit) => (.pure ((r : _root_.String))))))))))


noncomputable def «$strip_prefix_clauses» (input0 : _root_.String) (input1 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$strip_prefix:clause:0»  input0 input1), fun (_ : _root_.Unit) => .abort "builtin $strip_prefix failed"]


noncomputable def «$strip_suffix:clause:0» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let s : _root_.String := input1; (.bind (.guard (_root_.specTecTextSliceValid t 0 ((t).utf8ByteSize - (s).utf8ByteSize))) (fun (_ : Unit) => (let r : _root_.String := (_root_.specTecTextSlice t 0 ((t).utf8ByteSize - (s).utf8ByteSize)); (.bind (.guard (t = (r ++ s))) (fun (_ : Unit) => (.pure ((r : _root_.String))))))))))


noncomputable def «$strip_suffix_clauses» (input0 : _root_.String) (input1 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$strip_suffix:clause:0»  input0 input1), fun (_ : _root_.Unit) => .abort "builtin $strip_suffix failed"]


noncomputable def «$starts_with:clause:0» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_prefix : _root_.String := input1; (.bind (.guard (((_root_.String.utf8ByteSize t_prefix) ≤ (_root_.String.utf8ByteSize t)))) (fun (_ : Unit) => (.bind (SpecTecExecution.require ((((0 : _root_.Nat) + (_root_.String.utf8ByteSize t_prefix)) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t (0 : _root_.Nat) (_root_.String.utf8ByteSize t_prefix))) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (.guard (t_prefix = (_root_.specTecTextSlice t (0 : _root_.Nat) (_root_.String.utf8ByteSize t_prefix)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))))))


noncomputable def «$starts_with:clause:1» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_prefix : _root_.String := input1; (.pure ((false : _root_.Bool)))))


noncomputable def «$starts_with_clauses» (input0 : _root_.String) (input1 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$starts_with:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$starts_with:clause:1»  input0 input1)]


noncomputable def «$ends_with:clause:0» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_suffix : _root_.String := input1; (.bind (.guard (((_root_.String.utf8ByteSize t_suffix) ≤ (_root_.String.utf8ByteSize t)))) (fun (_ : Unit) => (let i : _root_.Int := ((_root_.Int.ofNat (_root_.String.utf8ByteSize t)) - (_root_.Int.ofNat (_root_.String.utf8ByteSize t_suffix))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n_start : _root_.Nat := (_root_.Int.toNat i); (.bind (SpecTecExecution.require (((n_start + (_root_.String.utf8ByteSize t_suffix)) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t n_start (_root_.String.utf8ByteSize t_suffix))) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (.guard (t_suffix = (_root_.specTecTextSlice t n_start (_root_.String.utf8ByteSize t_suffix)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))))))))))))


noncomputable def «$ends_with:clause:1» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_suffix : _root_.String := input1; (.pure ((false : _root_.Bool)))))


noncomputable def «$ends_with_clauses» (input0 : _root_.String) (input1 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$ends_with:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$ends_with:clause:1»  input0 input1)]


noncomputable def «$strip_prefix_rec:clause:0» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_prefix : _root_.String := input1; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$starts_with» t t_prefix⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.String, SpecTecCall.«$strip_prefix» t t_prefix⟩) (fun («exec:2» : _root_.String) => (let «eval:1» : _root_.String := «exec:2»; (let t_stripped : _root_.String := «eval:1»; (.bind (.call ⟨_root_.String, SpecTecCall.«$strip_prefix_rec» t_stripped t_prefix⟩) (fun («exec:3» : _root_.String) => (let «eval:2» : _root_.String := «exec:3»; (.pure ((«eval:2» : _root_.String)))))))))))))))))


noncomputable def «$strip_prefix_rec:clause:1» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_prefix : _root_.String := input1; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$starts_with» t t_prefix⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure ((t : _root_.String))))))))))


noncomputable def «$strip_prefix_rec_clauses» (input0 : _root_.String) (input1 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$strip_prefix_rec:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$strip_prefix_rec:clause:1»  input0 input1)]


noncomputable def «$strip_suffix_rec:clause:0» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_suffix : _root_.String := input1; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$ends_with» t t_suffix⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.String, SpecTecCall.«$strip_suffix» t t_suffix⟩) (fun («exec:2» : _root_.String) => (let «eval:1» : _root_.String := «exec:2»; (let t_stripped : _root_.String := «eval:1»; (.bind (.call ⟨_root_.String, SpecTecCall.«$strip_suffix_rec» t_stripped t_suffix⟩) (fun («exec:3» : _root_.String) => (let «eval:2» : _root_.String := «exec:3»; (.pure ((«eval:2» : _root_.String)))))))))))))))))

end SpecTec
