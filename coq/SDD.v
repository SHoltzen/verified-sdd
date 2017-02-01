Require Import Lists.List.
Require Import Arith.Arith.
Require Import Bool.
Require Import Bool.BoolEq.
Require Import Lists.ListSet.

Inductive vtree : Type :=
| VNode : vtree -> vtree -> vtree
| VAtom : nat -> vtree.

Inductive atom : nat -> Type :=
| AFalse : forall n, atom n
| ATrue : forall n, atom n
| AVar : forall n, bool -> atom n.

Inductive sdd : vtree -> Type :=
| Or : forall l r : vtree, list (sdd l * sdd r) -> sdd (VNode l r)
| Atom : forall n, atom n -> sdd (VAtom n).

Inductive ops : Type :=
| OAnd : ops
| OOr : ops.


(* Inductive atom_eq_rel : atom -> atom -> Prop := *)
(* | EqTrue : atom_eq_rel ATrue ATrue *)
(* | EqFalse : atom_eq_rel AFalse AFalse *)
(* | EqVar : forall n, atom_eq_rel (AVar n) (AVar n). *)

(* Fixpoint atom_eq n1 (a : atom n1) n2 (b : atom n2): bool := *)
(*   match a, b with *)
(*   | ATrue n1, ATrue n2 => true *)
(*   | AFalse n1, AFalse n2 => true *)
(*   | AVar n1, AVar n2 => beq_nat n1 n2 *)
(*   | _, _ => false *)
(*   end. *)



(* Fixpoint sdd_eq (s1: sdd) (s2 : sdd) : bool := *)
(*   match s1, s2 with *)
(*   | Or [], Or [] => true *)
(*   | Or (prime1, sub1) :: rst1, Or (prime2, sub2) :: rst2 => *)
(*     sdd_eq  *)
(*   | Atom a1, Atom a2 => atom_eq a1 a2 *)
(*   | _, _ => false *)
(*   end. *)



(* let rec expanded_sdd vtree term = *)
(*   match vtree with *)
(*   | VNode(l, r) -> *)
(*     let el, er = if term = True then True, True else True, False in *)
(*     let l = expanded_sdd l el and r = expanded_sdd r er in *)
(*     Or([l, r]) *)
(*   | VAtom(a) -> Atom(term) *)

(* (** generate an SDD given an atom from the Boolean expression grammar *) *)
(* let rec sdd_of_atom vtree atom v = *)
(*   match vtree with *)
(*   | VAtom(i) -> if i = atom then *)
(*       Atom(Var(i, v)) *)
(*     else Atom(True) *)
(*   | VNode(vl, vr) -> *)
(*     let left_t = sdd_of_atom vl atom v and *)
(*     right_t = sdd_of_atom vr atom v and *)
(*     left_f = sdd_of_atom vl atom (not v) in *)
(*     let f = expanded_sdd vr False in *)
(*     Or([(left_t, right_t); (left_f, f)]) (* if you just do it this way, you don't need to expand *) *)

Fixpoint expanded_sdd (v : vtree) (term : bool) : sdd v :=
  match v with
  | VAtom i => if term then Atom i (ATrue i) else Atom i (AFalse i)
  | VNode l r =>
    let (el, er) := if term then (true, true) else (true, false) in
    let lsdd := expanded_sdd l el in
    let rsdd := expanded_sdd r er in
    Or l r ((lsdd, rsdd) :: nil)
  end.


Fixpoint sdd_of_atom (v : vtree) (a : nat) (value : bool) : sdd v :=
  match v with
  | VAtom n => if beq_nat a n then Atom n (AVar n value) else Atom n (ATrue n)
  | VNode vl vr =>
    let left_t := sdd_of_atom vl a value in
    let left_f := sdd_of_atom vl a (negb value) in
    let right_t := sdd_of_atom vr a value in
    let right_f := expanded_sdd vr false in
    Or vl vr ((left_t, right_t) :: (left_f, right_f) :: nil)
  end.

Definition atom_and (n : nat) (a : atom n) (b : atom n) : atom n :=
  match a, b with
  | (ATrue _), (ATrue _) => ATrue n
  | (ATrue _), (AVar _ b1) | (AVar _ b1), (ATrue _) => AVar n b1
  | AVar _ b1, AVar _ b2 => if (eqb b1 b2) then AVar n b1 else AFalse n
  | _, _ => AFalse n
  end.


Definition atom_or (n : nat) (a : atom n) (b : atom n) : atom n :=
  match a, b with
  | (AFalse _), (AFalse _) => AFalse n
  | (AFalse _), (AVar _ b1) | (AVar _ b1), (AFalse _) => AVar n b1
  | AVar _ b1, AVar _ b2 => if (eqb b1 b2) then AVar n b1 else ATrue n
  | _, _ => AFalse n
  end.

Definition apply_op (op : ops) (n : nat) (a : atom n) (b : atom n) :=
  match op with
  | OAnd => atom_and n a b
  | OOr => atom_or n a b
  end.


Fixpoint apply (o : ops) (v : vtree) (a : sdd v) (b : sdd v) : sdd v :=
  match a, b with
  | Atom n a1, Atom _ a2 => apply_op o n a1 a2
  | Or lvtree rvtree l1, Or _ _ l2 =>
    let new_or_lst :=
        List.fold_left l1 nil
                       (fun a outer_accum =>
                          let (prime1, sub1) := a in
                          List.fold_left l2 outer_accum (fun b inner_accum =>
                                                           let (prime2, sub2) := b in
                                                           let new_prime := apply OAnd lvtree prime1 prime2 in
                                                           let new_sub := apply o rvtree sub1 sub2 in
                                                           (new_prime, new_sub) :: inner_accum
                       )) in
    Or (VNode lvtree rvtree) new_or_lst


  end.

