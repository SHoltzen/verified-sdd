open Core.Std
open OUnit2
open Sdd

let test_vtree test_ctx =
  let v = VNode(VAtom(0), VNode(VAtom(1), VAtom(2))) in
  let sdd = sdd_of_atom v 1 true in
  print_string (string_of_sdd sdd)

let suite =
"suite">:::
[
  "transfored_sdd">::test_vtree;
];;

let () =
  run_test_tt_main suite;
;;
