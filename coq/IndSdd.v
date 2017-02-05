Require Export Bool.Bool.
Require Export List.
Print Bool.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Inductive vtree : Type :=
| VNode : vtree -> vtree -> vtree
| VAtom : nat -> vtree.

Inductive atom : Type :=
| AFalse : atom
| ATrue : atom
| AVar :  nat -> bool -> atom.

Inductive sdd : Type :=
          (*prime sub   next *)
| Or: list (sdd * sdd) -> sdd
| Atom : atom -> sdd.

Inductive op : Type :=
| OAnd.

Inductive test : list (bool*bool) -> Prop :=
| EmptyList : test nil
| OnlyTrue : test [(true, true)]
| HeadFlip : forall (b1 b2 : bool) (l : list (bool*bool)), 
    test((b1, b2)::l) -> test([(b2, b1)]).


Inductive sdd_apply : op -> sdd -> sdd -> sdd -> Prop :=
| AtomAndTT : sdd_apply OAnd (Atom ATrue) (Atom ATrue) (Atom ATrue)
| AtomAndTF : sdd_apply OAnd (Atom ATrue) (Atom AFalse) (Atom AFalse) 
| AtomAndFT : sdd_apply OAnd (Atom AFalse) (Atom ATrue) (Atom AFalse)
| AtomAndFF : sdd_apply OAnd (Atom AFalse) (Atom AFalse) (Atom AFalse)
| AtomAndVT : forall (n : nat) (b : bool), sdd_apply OAnd (Atom (AVar n b)) (Atom ATrue) (Atom (AVar n b))
| AtomAndTV : forall (n : nat) (b : bool), sdd_apply OAnd (Atom ATrue) (Atom (AVar n b)) (Atom (AVar n b))
| AtomAndVF : forall (n : nat) (b : bool), sdd_apply OAnd (Atom AFalse) (Atom (AVar n b)) (Atom AFalse)
| AtomAndFV : forall (n : nat) (b : bool), sdd_apply OAnd (Atom (AVar n b)) (Atom AFalse) (Atom AFalse)
| AtomAndVVEq : forall (n : nat) (b : bool), sdd_apply OAnd (Atom (AVar n b)) (Atom (AVar n b)) (Atom (AVar n b))
| AtomAndVVNEq : forall (n : nat) (b1 : bool) (b2 : bool),
    (b1 <> b2) -> sdd_apply OAnd (Atom (AVar n b1)) (Atom (AVar n b2)) (Atom AFalse)
| ApplyOr : forall (l1 l2 res: list (sdd*sdd)) (o : op),
    or_list o l1 l2 res -> sdd_apply o (Or l1) (Or l2) (Or res)
with
(* an auxiliary inductive type to handle applying together two lists of primes and subs *)
or_list : op -> list (sdd*sdd) -> list (sdd*sdd) -> list(sdd*sdd) -> Prop :=
| EmptyLeft : forall (l : list (sdd * sdd)) (o : op),
    or_list o [] l []
| NonEmptyLeft : forall (prime sub : sdd) (ltail singleres orres linput : list (sdd * sdd)) (o : op),
    single_list o prime sub linput singleres ->
    or_list o ltail linput orres ->
    or_list o ((prime, sub)::ltail) linput (singleres ++ orres)
with
(* an auxiliary inductive type to handle applying together a single prime and sub with a list of primes
   and subs *)
single_list : op -> sdd -> sdd -> list (sdd * sdd) -> list (sdd * sdd) -> Prop :=
| EmptyRight : forall (prime sub : sdd) (o : op),
    single_list o prime sub [] []
| NonEmptyRight : forall (prime1 prime2 sub1 sub2 newprime newsub : sdd) (o : op) (tl subres : list (sdd * sdd)),
    sdd_apply OAnd prime1 prime2 newprime ->
    sdd_apply o sub1 sub2 newsub ->
    single_list o prime1 sub1 tl subres -> (* process the rest of the list *)
    single_list o prime1 sub1 ((prime2, sub2)::tl) ((newprime, newsub)::subres).

Example ex_sdd_apply0:
  sdd_apply OAnd (Or [(Atom ATrue, Atom AFalse)]) (Or [(Atom ATrue, Atom AFalse)]) (Or [(Atom ATrue, Atom AFalse)]).
Proof.
  apply ApplyOr.
  apply (NonEmptyLeft (Atom ATrue) (Atom AFalse) [] [(Atom ATrue, Atom AFalse)] _ _ OAnd).
  - apply (NonEmptyRight (Atom ATrue)  (Atom ATrue) (Atom AFalse) (Atom AFalse)
                         (Atom ATrue) (Atom AFalse) OAnd [] []).
    * apply AtomAndTT.
    * apply AtomAndFF.
    * apply EmptyRight.
  - apply EmptyLeft.
Qed.

    (* apply (NonEmptyRight (Atom ATrue) (Atom ATrue) (Atom AFalse) *)
    (*                      (Atom AFalse) (Atom ATrue) (Atom AFalse) OAnd [] []). *)


Example ex_sdd_apply1:
  sdd_apply OAnd (Atom ATrue) (Atom AFalse) (Atom AFalse).
Proof.
  apply AtomAndTF. Qed.

(* this gon' be fun... *)
(* Theorem self_apply: *)
(*   forall (sdd : sdd), sdd_apply OAnd sdd sdd sdd. *)
(* Proof. *)
(*   intros. induction sdd0. *)
(*   - induction l. *)
(*     * apply (ApplyOr [] [] []). apply EmptyLeft. *)
(*     * apply ApplyOr.  destruct a. remember ([(s,s0)]++l) as lb. *)
(*       apply (Single s s0 l s s0 l). *)