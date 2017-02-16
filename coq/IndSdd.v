Require Export Bool.Bool.
Require Export List.
Require Export Coq.Unicode.Utf8_core.

Require Export VarAssign.

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
    apply_or_list o l1 l2 res -> sdd_apply o (Or l1) (Or l2) (Or res)

with

(* an auxiliary inductive type to handle applying together two lists of primes and subs *)
apply_or_list : op -> list (sdd*sdd) -> list (sdd*sdd) -> list(sdd*sdd) -> Prop :=
| EmptyLeft : forall (l : list (sdd * sdd)) (o : op),
    apply_or_list o [] l []
| NonEmptyLeft : forall (prime sub : sdd) (ltail singleres orres linput : list (sdd * sdd)) (o : op),
    apply_single_list o prime sub linput singleres ->
    apply_or_list o ltail linput orres ->
    apply_or_list o ((prime, sub)::ltail) linput (singleres ++ orres)

with

(* an auxiliary inductive type to handle applying together a single prime and sub with a list of primes
   and subs *)
apply_single_list : op -> sdd -> sdd -> list (sdd * sdd) -> list (sdd * sdd) -> Prop :=
| EmptyRight : forall (prime sub : sdd) (o : op),
    apply_single_list o prime sub [] []
| NonEmptyRightSat : forall (prime1 prime2 sub1 sub2 newprime newsub : sdd) (o : op) (tl subres : list (sdd * sdd)),
    sdd_apply OAnd prime1 prime2 newprime ->
    newprime <> Atom AFalse ->
    sdd_apply o sub1 sub2 newsub ->
    apply_single_list o prime1 sub1 tl subres -> (* process the rest of the list *)
    apply_single_list o prime1 sub1 ((prime2, sub2)::tl) ((newprime, newsub)::subres)
| NonEmptyRightUnsat : forall (prime1 prime2 sub1 sub2: sdd) (o : op) (tl subres : list (sdd * sdd)),
    sdd_apply OAnd prime1 prime2 (Atom AFalse) ->
    apply_single_list o prime1 sub1 tl subres -> (* process the rest of the list *)
    apply_single_list o prime1 sub1 ((prime2, sub2)::tl) subres.

Inductive sdd_vtree : sdd -> vtree -> Prop :=
| AtomTrue : forall n, sdd_vtree (Atom ATrue) (VAtom n)
| AtomFalse : forall n, sdd_vtree (Atom AFalse) (VAtom n)
| AtomVar : forall n b, sdd_vtree (Atom (AVar n b)) (VAtom n)
| OrEmpty : forall v, sdd_vtree (Or []) v
| OrSingle: forall prime sub lvtree rvtree tail, 
    sdd_vtree prime lvtree ->
    sdd_vtree sub rvtree ->
    sdd_vtree (Or (tail)) (VNode lvtree rvtree) ->
    sdd_vtree (Or ((prime, sub) :: tail)) (VNode lvtree rvtree).

Example sdd_vtree_ex0:
  sdd_vtree (Or [(Atom (AVar 0 true), Atom (AVar 1 false))]) (VNode (VAtom 0) (VAtom 1)).
Proof.
  constructor.
  - constructor.
  - constructor.
  - constructor.
Qed.

Example ex_sdd_apply0:
  sdd_apply OAnd (Or [(Atom ATrue, Atom AFalse)]) (Or [(Atom ATrue, Atom AFalse)]) (Or [(Atom ATrue, Atom AFalse)]).
Proof.
  apply ApplyOr.
  apply (NonEmptyLeft (Atom ATrue) (Atom AFalse) [] [(Atom ATrue, Atom AFalse)] _ _ OAnd).

  - constructor.
    + constructor.
    + discriminate.
    + constructor.
    + constructor.
  - constructor. 
Qed.


Example ex_sdd_apply1:
  sdd_apply OAnd (Atom ATrue) (Atom AFalse) (Atom AFalse).
Proof.
  apply AtomAndTF. Qed.

Example ex_sdd_apply2:
  sdd_apply OAnd (Or [(Atom (AVar 0 true), Atom (AVar 1 true)); (Atom (AVar 0 false), Atom(AFalse))])
            (Or [(Atom (AVar 0 true), Atom (AVar 1 true)); (Atom (AVar 0 false), Atom(AFalse))])
            (Or [(Atom (AVar 0 true), Atom (AVar 1 true)); (Atom (AVar 0 false), Atom(AFalse))]).
Proof.
  constructor.
  - apply (NonEmptyLeft (Atom (AVar 0 true)) (Atom (AVar 1 true)) [(Atom (AVar 0 false), Atom AFalse)]
                        [(Atom (AVar 0 true), Atom (AVar 1 true))]).
    + constructor.
      * constructor.
      * discriminate.
      * constructor.
      * constructor.
        { constructor. discriminate. }
        { constructor. }
    + apply (NonEmptyLeft (Atom (AVar 0 false)) (Atom AFalse) [] [(Atom (AVar 0 false), Atom AFalse)]).
      * apply NonEmptyRightUnsat.
        { constructor. discriminate. }
        { Admitted.

(* Example sdd_and_eq: *)
(*   forall (a : sdd), sdd_apply OAnd a a a. *)
(* Proof. *)
(*   induction a. *)
(*   * constructor. *)
(*     induction l. *)
(*   + constructor. *)
(*   + destruct IHl. *)
    


  (* prime, sub : sdd *)
  (* lvtree, rvtree : vtree *)
  (* tail : list (sdd * sdd) *)
  (* H : sdd_vtree prime lvtree *)
  (* H0 : sdd_vtree sub rvtree *)
  (* H1 : sdd_vtree (Or tail) (VNode lvtree rvtree) *)
  (* IHsdd_vtree1 : sdd_apply OAnd prime prime prime *)
  (* IHsdd_vtree2 : sdd_apply OAnd sub sub sub *)
  (* IHsdd_vtree3 : sdd_apply OAnd (Or tail) (Or tail) (Or tail) *)
  (* ============================ *)
  (*  sdd_apply OAnd (Or ((prime, sub) :: tail)) (Or ((prime, sub) :: tail)) *)
  (*    (Or ((prime, sub) :: tail)) *)

Example sdd_and_eq:
  forall  (v : vtree) (a : sdd),
    sdd_vtree a v ->
    sdd_apply OAnd a a a.
Proof.
  intros.
  destruct a.
  induction H.
  -  constructor.
  -  constructor.
  -  constructor.
  -  constructor.
     *  constructor.
  - constructor. 
    eapply (NonEmptyLeft prime sub tail [(prime, sub)] tail ((prime, sub) :: tail)).
    * apply NonEmptyRightUnsat.
      { Admitted. (*assumption. }
      { discriminate. }*)


(* Apply preserves vtree consistency
  forall v sdd1 sdd2 sddRes, sdd_vtree sdd1 v → sdd_vtree sdd2 v → sdd_apply OAnd sdd1 sdd2 sddRes → sdd_vtree sddRes v.
*)

Inductive orList : list bool -> bool -> Prop :=
| OrListEmpty    : orList [] false
| OrListNonEmpty : forall b bs rest, orList bs rest -> orList (b::bs) (orb b rest).

Inductive sdd_eval : sdd -> bool → varAssign → Prop :=
| SDDEvalATrue    : forall va, sdd_eval (Atom ATrue) true va
| SDDEvalAFalse   : forall va, sdd_eval (Atom AFalse) false va
| SDDEvalAVarSame : forall va n res, assigns va n res → sdd_eval (Atom (AVar n true)) res va
| SDDEvalAVarDiff : forall va n res, assigns va n res → sdd_eval (Atom (AVar n false)) (negb res) va
| SDDEvalOr       : forall va pairs disjuncts res, sdd_eval_orList pairs disjuncts va -> 
                                               orList disjuncts res ->
                                               sdd_eval (Or pairs) res va

with

sdd_eval_orList : list (sdd*sdd) → list bool → varAssign → Prop :=
| SDDEvalEmpty    : forall va, sdd_eval_orList [] [] va
| SDDEvalNonEmpty : forall va prime sub tail pRes sRes tailRes, 
    sdd_eval prime pRes va →
    sdd_eval sub sRes va →
    sdd_eval_orList tail tailRes va →
    sdd_eval_orList ((prime, sub)::tail) ((andb pRes sRes)::tailRes) va.

Example sdd_eval_1_true : 
  sdd_eval (Or [((Atom (AVar 1 true)), (Atom ATrue))]) true (Var 1 true Empty).
Proof.
  eapply SDDEvalOr. 
  - apply SDDEvalNonEmpty. 
    * apply SDDEvalAVarSame. constructor.
    * apply SDDEvalATrue.
    * apply SDDEvalEmpty.
  - simpl. eapply (OrListNonEmpty true []). apply OrListEmpty. 
Qed.

