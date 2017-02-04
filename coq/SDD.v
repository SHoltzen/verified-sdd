Require Import Lists.List.
Require Import Arith.Arith.
Require Import Bool.
Require Import Bool.BoolEq.
Require Import Lists.ListSet.

Inductive vtree : Type :=
| VNode : vtree -> vtree -> vtree
| VAtom : nat -> vtree.

Inductive atom :  Type :=
| AFalse : atom
| ATrue : atom
| AVar :  nat -> bool -> atom.

Inductive sdd : Type :=
| Or : list (sdd * sdd) -> sdd
| Atom : atom -> sdd.

Inductive ops : Type :=
| OAnd : ops
| OOr : ops.


Fixpoint expanded_sdd (v : vtree) (term : bool) : sdd :=
  match v with
  | VAtom i => if term then Atom ATrue else Atom AFalse
  | VNode l r =>
    let (el, er) := if term then (true, true) else (true, false) in
    let lsdd := expanded_sdd l el in
    let rsdd := expanded_sdd r er in
    Or ((lsdd, rsdd) :: nil)
  end.


Fixpoint sdd_of_atom (v : vtree) (a : nat) (value : bool) : sdd :=
  match v with
  | VAtom n => if beq_nat a n then Atom (AVar n value) else Atom n (ATrue n)
  | VNode vl vr =>
    let left_t := sdd_of_atom vl a value in
    let left_f := sdd_of_atom vl a (negb value) in
    let right_t := sdd_of_atom vr a value in
    let right_f := expanded_sdd vr false in
    Or ((left_t, right_t) :: (left_f, right_f) :: nil)
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
  match v, a, b with
  | VAtom n, Atom _ a1, Atom _ a2 => apply_op o n a1 a2
  | VNode vl vr, Or _ _ l1, Or _ _ l2 =>
    Or (process_or_list o vl vr l1 l2)
  end with
process_or_list (o : ops) (vl : vtree) (vr : vtree) (l1 : list (sdd vl * sdd vr)) (l2 : list (sdd vl * sdd vr)) : list (sdd vl * sdd vr) :=
  match l1 with
  | nil => nil
  | x::xs =>
    (process_or_single o vl vr x l2) :: (process_or_list o vl vr xs l2)
  end with
process_or_single (o : ops) (vl : vtree) (vr : vtree) (cur : (sdd vl * sdd vr)) (l2 : list (sdd vl * sdd vr)) : list (sdd vl * sdd vr) :=
  match l2 with
  | nil => nil
  | (sdd_a _, sdd_b _)::rst => nil
  end.
