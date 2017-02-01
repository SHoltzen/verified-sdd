open Core.Std
open OUnit2

(** a core Boolean expression data type which is used to represent non-SDD formulas *)
module BoolExpr = struct
  (** An arbitrary Boolean expression restricted to normal form *)
  type boolexpr =
    | And of boolexpr * boolexpr
    | Or of boolexpr * boolexpr
    | Atom of int * bool
  [@@deriving sexp]

  let string_of_boolexpr e =
    Sexp.to_string_hum @@
    sexp_of_boolexpr e

  (** evaluate a boolean expression on input i *)
  let rec eval e i =
    match e with
    | And(e1, e2) ->
      let r1 = eval e1 i and r2 = eval e2 i in
      (r1 && r2)
    | Or(e1, e2) ->
      let r1 = eval e1 i and r2 = eval e2 i in
      r1 || r2
    | Atom(id, b) ->
      let fb = Map.Poly.find_exn i id in
      b = fb
end

(**
   encode SDDs as a mutually recursive data type which
   enforces alternation between Or/And nodes and forces
   all Or-Nodes to have And-Nodes for children. This should make
   proving correctness easier *)
type sddatom =
  | False
  | True
  | Var of int * bool
[@@deriving sexp]

type sdd =
  | Or of (sdd * sdd) list
  | Atom of sddatom
[@@deriving sexp]

(** operations which can be applied to SDDs *)
type ops = OAnd | OOr

(* v-trees encode variable orderings *)
type vtree =
  | VNode of vtree * vtree
  | VAtom of int
[@@deriving sexp]

(** evaluate an SDD on input i *)
let rec eval_sdd sdd i =
  match sdd with
  | Or(l) -> List.exists l (fun (prime, sub) ->
      (eval_sdd prime i) && (eval_sdd sub i)
    )
  | Atom(a) ->
    (match a with
     | True -> true
     | False -> false
     | Var(id, b) ->
       let v = Map.Poly.find_exn i id in
       b = v)

let rec sdd_eq s1 s2 =
  match s1, s2 with
  | Or(l1), Or(l2) ->
    List.for_all l1 ~f:(fun (prime1, sub1) ->
        List.exists l2 ~f:(fun (prime2, sub2) ->
          (sdd_eq prime1 prime2) && (sdd_eq sub1 sub2)
          )
      )
  | Atom(a), Atom(b) -> a = b
  | _ -> false


(** printing functions *)
let string_of_vtree v =
  Sexp.to_string_hum @@ sexp_of_vtree v

let string_of_sdd sdd =
  Sexp.to_string_hum @@ sexp_of_sdd sdd

let b_to_atom b =
  match b with
  | true -> True
  | false -> False

let rec expanded_sdd vtree term =
  match vtree with
  | VNode(l, r) ->
    let el, er = if term = True then True, True else True, False in
    let l = expanded_sdd l el and r = expanded_sdd r er in
    Or([l, r])
  | VAtom(a) -> Atom(term)

(** generate an SDD given an atom from the Boolean expression grammar *)
let rec sdd_of_atom vtree atom v =
  match vtree with
  | VAtom(i) -> if i = atom then
      Atom(Var(i, v))
    else Atom(True)
  | VNode(vl, vr) ->
    let left_t = sdd_of_atom vl atom v and
    right_t = sdd_of_atom vr atom v and
    left_f = sdd_of_atom vl atom (not v) in
    let f = expanded_sdd vr False in
    Or([(left_t, right_t); (left_f, f)]) (* if you just do it this way, you don't need to expand *)


(** Apply an SDD operation to two atoms
    @returns an SDD atom *)
let apply_op_const op a b : sddatom =
  match op with
  | OAnd ->
    (match a, b with
     | True, False | False, True | False, False | Var(_), False | False, Var(_) -> False
     | True, True -> True
     | Var(i1, b1), Var(i2, b2) -> assert (i1 = i2); if (b1 = b2) then Var(i1, b1) else False
     | Var(i, b), True | True, Var(i, b) -> Var(i, b))
  | OOr ->
    (match a, b with
     | True, False | False, True | True, True | Var(_), True | True, Var(_) -> True
     | False, False -> False
     | Var(i, b), False | False, Var(i, b) -> Var(i, b)
     | Var(i1, b1), Var(i2, b2) -> assert (i1 = i2); if (b1 = b2) then Var(i1, b1) else True)


let expand n =
  match n with
  | Atom(False) -> [(Atom(True), Atom(False))]
  | Atom(True) -> [(Atom(True), Atom(True))]
  | _ -> failwith "invalid expansion"

type cache_item = {a:sdd;
                   b:sdd;
                   op:ops}
type cache_type = (cache_item, sdd) Map.Poly.t
exception Invalid_sdd of string
(** @returns an SDD that is the result of applying 'op' to SDD a and b*)
let rec apply (cache:cache_type) op (a:sdd) (b:sdd) =
  let apply_or l1 l2 =
    (* iterate over each prime and sub *)
    let new_cache, r = List.fold l1 ~init: (cache, []) ~f:(fun (c, l) ((prime1, sub1)) ->
        List.fold l2 ~init:(c, l) ~f:(fun (subc, sublst) ((prime2, sub2)) ->
            let new_cache, new_prime = apply subc OAnd prime1 prime2 in
            match new_prime with
            | Atom(False) -> subc, sublst
            | _ ->
              let sub_cache, new_sub = apply new_cache op sub1 sub2 in
              sub_cache, (((new_prime, new_sub))) :: sublst)
      ) in
    let new_or = Or(r) in
    (Map.Poly.add new_cache {a=Or(l1); b=Or(l2); op=op} new_or), new_or in
  match a, b with
  | Atom(atom1), Atom(atom2) -> cache, Atom (apply_op_const op atom1 atom2)
  | Or(or1), Or(or2) -> apply_or or1 or2
  (* manually expand atoms; this should make verification easier *)
  | _ -> failwith "Invalid SDD: not properly normalized"




let rec compile vtree cache (expr:BoolExpr.boolexpr) =
  let r = compile vtree in
  match expr with
  | BoolExpr.And(b1, b2) ->
    let cache1, l = r cache b1 in
    let cache2, r = r cache1 b2 in
    apply cache2 OAnd l r
  | BoolExpr.Or(b1, b2) ->
    let cache1, l = r cache b1 in
    let cache2, r = r cache b2 in
    apply cache2 OOr l r
 | BoolExpr.Atom(i, b) -> cache, sdd_of_atom vtree i b

(*********************************************************************************)
(* tests *)
(*********************************************************************************)

(** split a list into 2 parts, the length of the first equal to n *)
let split list n =
    let rec aux i acc = function
      | [] -> List.rev acc, []
      | h :: t as l -> if i = 0 then List.rev acc, l
                       else aux (i-1) (h :: acc) t  in
    aux n [] list;;

(** generates a random vtree for num_vars variables *)
let gen_vtree num_vars =
  let rec partition l =
    match l with
    | x :: [] -> VAtom(x)
    | xs ->
      (* pivot somewhere between first and last element exclusive *)
      let pivot = 1 + (Random.int ((List.length l) - 1)) in
      let ll, rl = split l pivot in
      let subl = partition ll and subr = partition rl in
      VNode(subl, subr) in
  let int_list = List.permute ~random_state:(Random.State.make_self_init ()) @@ List.range 0 num_vars in
  partition int_list

(** generates random input for num_vars variables *)
let rec gen_input num_vars =
  let int_list = List.range 0 num_vars in
  let l = List.map int_list ~f:(fun i -> (i, (Random.bool ()))) in
  Map.Poly.of_alist_exn l

let test_vtree test_ctx =
  let v = gen_vtree 4 in
  let sdd = sdd_of_atom v 1 true in
  Format.printf "Sdd: %s\nVtree:%s"
    (string_of_sdd sdd)
    (string_of_vtree v)


(* test to see if a given bexpr and the SDD it compiles to yield the same result when
   evaluated on random inputs *)
let test_congruency bexpr num_vars =
  let vtree = gen_vtree num_vars in
  (* Format.printf "Vtree: %s" (string_of_vtree vtree); *)
  let _, sdd = compile vtree (Map.Poly.empty) bexpr in
  (* Format.printf "Testing bexpr: %s\nSdd: %s\n" *)
  (*   (BoolExpr.string_of_boolexpr bexpr) (string_of_sdd sdd); *)
  for counter = 0 to 25 do
    let input = gen_input num_vars in
    if (eval_sdd sdd input) <> (BoolExpr.eval bexpr input) then
    assert_failure
      (Format.sprintf "Not equal: \nBool expr: %s\nSDD: %s\n"
        (BoolExpr.string_of_boolexpr bexpr)
        (string_of_sdd sdd))
    else ()
  done



let test_apply test_ctx =
  let v = VNode(VAtom(0), VNode(VAtom(1), VAtom(2))) in
  let sdd1 = sdd_of_atom v 1 true in
  let sdd2 = sdd_of_atom v 2 false in
  let c, applied = apply Map.Poly.empty OAnd sdd1 sdd2 in
  (* print_string ("Apply:\n" ^ (string_of_sdd applied)) *)
  let c2, applied_redundant = apply Map.Poly.empty OAnd applied sdd2 in
  assert_equal applied applied_redundant ~printer:(string_of_sdd)
    ~cmp:(sdd_eq)

(* Equivalent sentences have identical circuits *)
let test_canonicity bexpr0 bexpr1 num_vars=
  let vtree = gen_vtree num_vars in
  let _, sdd0 = compile vtree (Map.Poly.empty) bexpr0 in
  let _, sdd1 = compile vtree (Map.Poly.empty) bexpr1 in
  for counter = 0 to 25 do
    if not (sdd_eq sdd0 sdd1) then
      assert_failure
        (Format.sprintf "Not equal: \nSDD0: %s\nSDD1: %s\n"
          (string_of_sdd sdd0)
          (string_of_sdd sdd1))
        else ()
  done

let f0 = BoolExpr.(And(Atom(0, true), Atom(1, false)))

let f1 = BoolExpr.(Or(Atom(1, true), Or(Atom(0, false),
                   (And(Atom(0, true), Atom(2, true))))))

let f2 = BoolExpr.(And(Atom(3, false), Or(f0, f1)))

let test_congruent_f0 test_ctx =
  test_congruency f0 2

let test_congruent_f1 test_ctx =
  test_congruency f1 3

let test_congruent_f2 test_ctx =
  test_congruency f2 4


let f3a = BoolExpr.(And(Atom(1, true), Or(Atom(2, true), Atom(3, true))))
let f3b = BoolExpr.(Or(
  And(Atom(1, true), Atom(2, true)),
  And(Atom(1, true), Atom(3, true))
))

let f4a = BoolExpr.(Atom(1, false))
let f4b = BoolExpr.(And(
  Or(Atom(1, false), Atom(2, true)),
  Or(Atom(1, false), Atom(2, false))
))

let f5a = BoolExpr.(Or(Atom(1, true), Atom(2, false)))
let f5b = BoolExpr.(And(
  Or(Atom(1, true), Or(Atom(2, false), Atom(3, true))),
  Or(Atom(1, true), Or(Atom(2, false), Atom(3, false)))
))
let f6 = BoolExpr.(And(
  Or(Or(Atom(1, true), Atom(2, false)), Atom(3, true)),
  Or(Or(Atom(1, true), Atom(2, false)), Atom(3, false))
))

let test_canonicity_f3 test_ctx =
  test_canonicity f3a f3b 3

let test_canonicity_f4 test_ctx =
  test_canonicity f4a f4b 2

let test_canonicity_f5 test_ctx =
  test_canonicity f5a f5b 3

let test_canonicity_f6 test_ctx =
  test_canonicity f6 f5b 3

let suite =
"suite">:::
[
  "vtree">::test_vtree;
  "basic_apply">::test_apply;
  "congruent_f0">::test_congruent_f0;
  "congruent_f1">::test_congruent_f1;
  "congruent_f2">::test_congruent_f2;
  "canonicity_f3">::test_canonicity_f3;
  "canonicity_f4">::test_canonicity_f4;
  "canonicity_f5">::test_canonicity_f5;
  "canonicity_f6">::test_canonicity_f6
];;

let () =
  run_test_tt_main suite;
;;
