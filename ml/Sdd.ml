open Core.Std
open OUnit2

(** a core Boolean expression data type which is used to represent non-SDD formulas *)
module BoolExpr = struct
  type boolexpr =
    | False
    | True
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
    | False -> false
    | True -> true
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

and
  sddor = Or of sddand list
and
  or_or_atom = COr of sddor | Atom of sddatom
and
  sddand = And of or_or_atom * or_or_atom
[@@deriving sexp]

(** operations which can be applied to SDDs *)
type ops = OAnd | OOr

(* v-trees encode variable orderings *)
type vtree =
  | VNode of vtree * vtree
  | VAtom of int
[@@deriving sexp]

(* check for equality of two SDDs *)
let rec sdd_and_eq (sdd_a:sddand) (sdd_b:sddand) =
  let And(b1, b2) = sdd_a and And(b3, b4) = sdd_b in
  (sdd_eq b1 b3) && (sdd_eq b2 b4)
and
sdd_eq s1 s2 =
  match s1, s2 with
  | COr(Or(l1)), COr(Or(l2)) ->
    List.for_all l1 ~f:(fun itm ->
        List.exists l2 ~f:(fun s ->
            sdd_and_eq itm s
          )
      )
  | Atom(a), Atom(b) -> a = b
  | _ -> false


(** printing functions *)
let string_of_vtree v =
  Sexp.to_string_hum @@ sexp_of_vtree v

let string_of_sdd sdd =
  Sexp.to_string_hum @@ sexp_of_or_or_atom sdd


(** generate an SDD given an atom from the Boolean expression grammar *)
let rec sdd_of_atom vtree atom v =
  match vtree with
  | VAtom(i) -> if i = atom then Atom(Var(i, v)) else Atom(True)
  | VNode(vl, vr) ->
    let left_t = sdd_of_atom vl atom v and
    right_t = sdd_of_atom vr atom v and
    left_f = sdd_of_atom vl atom (not v) in
    if (left_t = left_f) then (* the atom is in the right vtree *)
      COr(Or([And(left_t, right_t)]))
    else
      COr(Or([And(left_t, right_t); And(left_f, Atom(False))]))


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


type cache_item = {a:sddor;
                   b:sddor;
                   op:ops}
type cache_type = (cache_item, or_or_atom) Map.Poly.t

(** @returns an SDD that is the result of applying 'op' to SDD a and b*)
let rec apply (cache:cache_type) op (a:or_or_atom) (b:or_or_atom) =
  match a, b with
  | Atom(atom1), Atom(atom2) -> cache, Atom (apply_op_const op atom1 atom2)
  | COr(or1), COr(or2) ->
    (match Map.Poly.find cache {a=or1; b=or2; op=op} with
    | Some(r) -> cache, r (* we have the SDD in the cache *)
    | None -> (* make a new SDD *)
      (* iterate over each prime and sub *)
      let Or(l1) = or1 in
      let new_cache, r = List.fold l1 ~init: (cache, []) ~f:(fun (c, l) (And(prime1, sub1)) ->
          let Or(l2) = or2 in
          List.fold l2 ~init:(c, l) ~f:(fun (subc, sublst) (And(prime2, sub2)) ->
              let new_cache, new_prime = apply subc OAnd prime1 prime2 in
              match new_prime with
              | Atom(False) -> subc, sublst
              | _ ->
                let sub_cache, new_sub = apply new_cache op sub1 sub2 in
                sub_cache, ((And(new_prime, new_sub))) :: sublst)
        ) in
      let new_or = Or(r) in
      (Map.Poly.add new_cache {a=or1; b=or2; op=op} (COr(new_or))), COr(new_or)
    )
  | _ -> failwith "SDDs not normalized wrt. the same vtree"


(*********************************************************************************)
(* tests *)

let test_vtree test_ctx =
  let v = VNode(VAtom(0), VNode(VAtom(1), VAtom(2))) in
  let sdd = sdd_of_atom v 1 true in
  print_string (string_of_sdd sdd)

let test_apply test_ctx =
  let v = VNode(VAtom(0), VNode(VAtom(1), VAtom(2))) in
  let sdd1 = sdd_of_atom v 1 true in
  let sdd2 = sdd_of_atom v 2 false in
  let c, applied = apply Map.Poly.empty OAnd sdd1 sdd2 in
  (* print_string ("Apply:\n" ^ (string_of_sdd applied)) *)
  let c2, applied_redundant = apply Map.Poly.empty OAnd applied sdd2 in
  assert_equal applied applied_redundant ~printer:(string_of_sdd)
    ~cmp:(sdd_eq)

let suite =
"suite">:::
[
  "vtree">::test_vtree;
  "basic_apply">::test_apply;
];;

let () =
  run_test_tt_main suite;
;;
