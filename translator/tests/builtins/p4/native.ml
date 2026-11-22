(* Execute the pinned implementation, without patches, in a private source copy. *)
open Util.Source
module V = Runtime.Value
module T = Runtime.Type.Typ
module B = Builtin.Call.Make (Builtin.Call.No_ext) ()
let add _ = ()
let n i = V.Make.nat (Bigint.of_int i)
let z i = V.Make.int (Bigint.of_int i)
let s = V.Make.text
let b = V.Make.bool
let list xs = V.Make.list (T.Make.list T.Make.int) xs
let tuple xs = V.Make.tuple (T.Make.tuple [T.Make.nat;T.Make.text]) xs
let opt x = V.Make.opt (T.Make.opt T.Make.text) x
let set xs = V.Make.case (T.Make.var ("set" $ no_region) [T.Make.nat])
  (Domain.Mixfix.fill Builtin.Sets.mixop_set [list (List.map n xs)])
let pair (k,v) = Builtin.Maps.make_pair add T.Make.nat T.Make.text (n k) (s v)
let map xs = Builtin.Maps.value_of_map add T.Make.nat T.Make.text (List.map pair xs)
let count = ref 0
let check name typs args expected =
  let got = B.invoke add (name $ no_region) typs args in
  if V.compare got expected <> 0 then
    failwith (Printf.sprintf "%s: expected %s; got %s" name (V.to_string expected) (V.to_string got));
  incr count;
  Printf.printf "PASS %s\n%!" name
let fails name typs args =
  match B.invoke add (name $ no_region) typs args with
  | _ -> failwith (name ^ ": expected BuiltinError")
  | exception Builtin.Error.BuiltinError _ -> incr count; Printf.printf "PASS %s BuiltinError\n%!" name
let host_fails name typs args =
  match B.invoke add (name $ no_region) typs args with
  | _ -> failwith (name ^ ": expected host exception")
  | exception Builtin.Error.BuiltinError _ -> failwith (name ^ ": unexpected BuiltinError")
  | exception _ -> incr count; Printf.printf "PASS %s HostConversion\n%!" name
let () =
  check "sum_nat" [] [list [n 1;n 2;n 3]] (n 6);
  check "max_nat" [] [list [n 1;n 3;n 2]] (n 3);
  check "min_nat" [] [list [n 2;n 1;n 3]] (n 1);
  fails "max_nat" [] [list []]; fails "min_nat" [] [list []];
  check "sum_int" [] [list [z (-3);z 2]] (z (-1));
  check "max_int" [] [list []] (z 0); check "min_int" [] [list []] (z 0);
  check "max_int" [] [list [z (-3);z (-1)]] (z (-1));
  check "min_int" [] [list [z (-3);z (-1)]] (z (-3));
  check "int_to_text" [] [z 0] (s "+0"); check "int_to_text" [] [z (-7)] (s "-7");
  check "text_to_int" [] [s "-0xff"] (z (-255)); check "text_to_int" [] [s "1_024"] (z 1024);
  List.iter (fun text -> check "text_to_int" [] [s text] (z 0)) ["";"+";"-";"0x";"-0b"];
  List.iter (fun text -> host_fails "text_to_int" [] [s text]) ["_1";"0x_f"];
  check "split_text" [] [s ",a,,";s ","] (list (List.map s ["";"a";"";""]));
  check "strip_prefix" [] [s "abc";s "ab"] (s "c");
  check "strip_suffix" [] [s "abc";s "bc"] (s "a");
  check "strip_all_whitespace" [] [s " a\t b"] (s "a\tb");
  check "rev_" [T.Make.nat] [list [n 1;n 2]] (list [n 2;n 1]);
  check "concat_" [T.Make.nat] [list [list [n 1];list [];list [n 2;n 3]]] (list [n 1;n 2;n 3]);
  check "distinct_" [T.Make.nat] [list [n 1;n 2;n 1]] (b false);
  check "partition_" [T.Make.nat] [list [n 1;n 2];n 5] (tuple [list [n 1;n 2];list []]);
  check "assoc_" [T.Make.nat;T.Make.text] [n 1;list [tuple [n 1;s "a"];tuple [n 1;s "b"]]] (opt (Some (s "a")));
  check "sort_" [T.Make.text] [list [tuple [n 2;s "b"];tuple [n 1;s "a"];tuple [n 2;s "c"]]]
    (list [tuple [n 1;s "a"];tuple [n 2;s "b"];tuple [n 2;s "c"]]);
  check "transpose_" [T.Make.nat] [list [list [n 1;n 2];list [n 3;n 4]]] (list [list [n 1;n 3];list [n 2;n 4]]);
  fails "transpose_" [T.Make.nat] [list [list [n 1];list [n 2;n 3]]];
  check "intersect_set" [T.Make.nat] [set [3;1;1];set [2;1]] (set [1]);
  check "union_set" [T.Make.nat] [set [3;1;1];set [2;1]] (set [1;2;3]);
  check "unions_set" [T.Make.nat] [list [set [3;1];set [2;1]]] (set [1;2;3]);
  check "diff_set" [T.Make.nat] [set [3;1;1];set [2;1]] (set [3]);
  check "sub_set" [T.Make.nat] [set [1;1];set [1;2]] (b true);
  check "eq_set" [T.Make.nat] [set [2;1;1];set [1;2]] (b true);
  check "find_map" [T.Make.nat;T.Make.text] [map [1,"a";1,"b"];n 1] (opt (Some (s "a")));
  check "find_maps" [T.Make.nat;T.Make.text] [list [map [1,"a"];map [1,"b"]];n 1] (opt (Some (s "a")));
  check "add_map" [T.Make.nat;T.Make.text] [map [1,"a";1,"b"];n 1;s "c"] (map [1,"c";1,"b"]);
  check "update_map" [T.Make.nat;T.Make.text] [map [1,"a"];n 2;s "b"] (map [1,"a";2,"b"]);
  check "adds_map" [T.Make.nat;T.Make.text] [map [1,"a"];list [n 2;n 1];list [s "b";s "c"]] (map [1,"c";2,"b"]);
  check "shl" [] [z 7;z (-1)] (z 7); check "shr" [] [z (-7);z 1] (z (-3));
  check "shr_arith" [] [z 7;z 2;z 8] (z 13); fails "shl" [] [z 1;z 2049];
  check "pow2" [] [z (-3)] (z 1);
  check "bitstr_to_int" [] [z 4;z 15] (z (-1)); check "bitstr_to_int" [] [z 0;z 99] (z 0);
  check "int_to_bitstr" [] [z 4;z (-1)] (z 15); check "int_to_bitstr" [] [z (-1);z 99] (z 0);
  check "bits_to_int_unsigned" [] [list [b true;b false;b true]] (z 5);
  check "bits_to_int_signed" [] [list [b true;b false;b true]] (z (-3));
  fails "bits_to_int_signed" [] [list []];
  check "int_to_bits_unsigned" [] [z 3;z (-3)] (list [b true;b false;b true]);
  check "int_to_bits_signed" [] [z 3;z (-3)] (list [b true;b false;b true]);
  check "bneg" [] [z 5] (z (-6)); check "band" [] [z 5;z 3] (z 1);
  check "bxor" [] [z 5;z 3] (z 6); check "bor" [] [z 5;z 3] (z 7);
  check "bitacc" [] [z 171;z 5;z 2] (z 10); check "bitacc_replace" [] [z 171;z 5;z 2;z 1] (z 135);
  check "fresh_typeId" [] [] (s "FRESH__0"); check "fresh_typeId" [] [] (s "FRESH__1");
  ignore (Interface.P4.init (Runtime.Dynamic_Runner.Signature.AL []));
  let printed = Interface.P4.call_builtin add ("print_" $ no_region) [T.Make.int] [z 7] in
  assert (V.compare printed (s "7") = 0); incr count; Printf.printf "PASS print_\n%!";
  host_fails "text_to_int" [] [s "not-a-number"];
  host_fails "split_text" [] [s "abc";s ""];
  host_fails "strip_prefix" [] [s "abc";s "x"];
  host_fails "strip_suffix" [] [s "abc";s "x"];
  host_fails "adds_map" [T.Make.nat;T.Make.text] [map [];list [n 1];list []];
  host_fails "int_to_bits_unsigned" [] [z (-1);z 1];
  host_fails "bitacc" [] [z 1;z 2;z (-1)];
  host_fails "bitacc_replace" [] [z 1;z 2;z (-1);z 0];
  List.iter (fun text ->
    let value = try Bigint.of_string text |> Bigint.to_string with _ -> "ERROR" in
    Printf.printf "PARSE %S %s\n%!" text value)
    ["";"_";"_1";"1_";"0x";"0x_";"0x_f";" 1";"1 ";"+";"01";"0b10";"0o17"];
  Printf.printf "Native checks: %d passed\n%!" !count
