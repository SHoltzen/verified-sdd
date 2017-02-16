Require Export Bool.Bool.
Require Export List.
<<<<<<< HEAD
Require Export Coq.Unicode.Utf8_core.

Require Export VarAssign.

Print Bool.
=======

>>>>>>> 426c316f0ea7e6432240719f831722b8f1641f25

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).


Inductive boolExpr : Type :=
| BAtom : nat -> bool -> boolExpr
| BAnd  : boolExpr -> boolExpr -> boolExpr
| BOr   : boolExpr -> boolExpr -> boolExpr.

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

(* the magic of the Vtree lets us turn SDD sat/unsat testing into syntactic queries of the SDD *)


(* idea: a false atom is unsat, a false atom conjoined with anything is unsat,
   in order for an OR to be unsat all its children must be unsat *)
Inductive sdd_unsat : sdd -> Prop :=
| UnsatAtom : sdd_unsat (Atom AFalse)
| UnsatOrPrime : forall tl (prime sub : sdd),
    sdd_unsat prime ->
    sdd_unsat (Or tl) ->
    sdd_unsat (Or ((prime, sub)::tl))
| UnsatOrSub: forall tl (prime sub : sdd),
    sdd_unsat sub ->
    sdd_unsat (Or tl) ->
    sdd_unsat (Or ((prime, sub)::tl))
| UnsatEmptyOr :
    sdd_unsat (Or []).

Example sdd_unsat_ex0:
  sdd_unsat (Or [(Atom ATrue, Atom AFalse); (Atom (AVar 1 true), Atom AFalse)]).
Proof.
  apply UnsatOrSub.
  constructor.
  apply UnsatOrSub.
  constructor.
  constructor.
Qed.

(* idea: a true atom is sat, a var is sat,
   SAT /\ SAT is SAT, a single or-child must be sat for the
   OR to be sat *)
Inductive sdd_sat : sdd -> Prop :=
| SatAtom : sdd_sat (Atom ATrue)
| SatVar : forall n b, sdd_sat (Atom (AVar n b))
| SatOr : forall tl (prime sub : sdd),
    sdd_sat prime ->
    sdd_sat sub ->
    sdd_sat (Or ((prime, sub) :: tl))
| SatOrStep : forall tl (prime sub : sdd),
    sdd_sat (Or tl) ->
    sdd_sat (Or ((prime, sub) :: tl)).

Example sdd_sat_ex0 :
  sdd_sat (Or [(Atom ATrue, Atom AFalse); (Atom ATrue, Atom (AVar 1 true))]).
Proof.
  apply SatOrStep. constructor. constructor. constructor.
Qed.





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
    sdd_sat newprime ->
    sdd_apply o sub1 sub2 newsub ->
<<<<<<< HEAD
    apply_single_list o prime1 sub1 tl subres -> (* process the rest of the list *)
    apply_single_list o prime1 sub1 ((prime2, sub2)::tl) ((newprime, newsub)::subres)
| NonEmptyRightUnsat : forall (prime1 prime2 sub1 sub2: sdd) (o : op) (tl subres : list (sdd * sdd)),
    sdd_apply OAnd prime1 prime2 (Atom AFalse) ->
    apply_single_list o prime1 sub1 tl subres -> (* process the rest of the list *)
    apply_single_list o prime1 sub1 ((prime2, sub2)::tl) subres.
=======
    single_list o prime1 sub1 tl subres -> (* process the rest of the list *)
    single_list o prime1 sub1 ((prime2, sub2)::tl) ((newprime, newsub)::subres)
| NonEmptyRightUnsat : forall (prime1 prime2 sub1 sub2 r: sdd) (o : op) (tl subres : list (sdd * sdd)),
    sdd_apply OAnd prime1 prime2 r ->
    sdd_unsat r ->
    single_list o prime1 sub1 tl subres -> (* process the rest of the list *)
    single_list o prime1 sub1 ((prime2, sub2)::tl) subres.
>>>>>>> 426c316f0ea7e6432240719f831722b8f1641f25

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

(* an interesting theorem: all valid SDDs are either SAT or UNSAT. *)
Theorem sdd_sat_or_unsat :
  forall (sdd : sdd) vtree,
    sdd_vtree sdd vtree ->
    sdd_unsat sdd \/ sdd_sat sdd.
Proof.
Admitted.

Inductive expanded_sdd : vtree -> atom -> sdd -> Prop :=
| ExpandAtomT : forall n, expanded_sdd (VAtom n) ATrue (Atom ATrue)
| ExpandAtomF : forall n, expanded_sdd (VAtom n) AFalse (Atom AFalse)
| ExpandFalseNode : forall lvtree rvtree lsdd rsdd,
    expanded_sdd lvtree ATrue lsdd ->
    expanded_sdd rvtree AFalse rsdd ->
    expanded_sdd (VNode lvtree rvtree) AFalse (Or [(lsdd, rsdd)])
| ExpandTrueNode : forall lvtree rvtree lsdd rsdd,
    expanded_sdd lvtree ATrue lsdd ->
    expanded_sdd rvtree ATrue lsdd ->
    expanded_sdd (VNode lvtree rvtree) ATrue (Or [(lsdd, rsdd)]).


(* need to handle cases when the derived primes are sat/unsat, otherwise
   you get false primes in the generated SDD *)
Inductive sdd_of_var : nat -> vtree -> bool -> sdd -> Prop :=
| VarOfLeafMatchT : forall n b, sdd_of_var n (VAtom n) b (Atom (AVar n b))
| VarOfLeafNonmatchT : forall n1 n2 b,
    n1 <> n2 ->
    sdd_of_var n1 (VAtom n2) b (Atom ATrue)
| VarOfLeafNonmatchF : forall n1 n2 b,
    n1 <> n2 ->
    sdd_of_var n1 (VAtom n2) b (Atom AFalse)
| VarOfNode : forall n b lvtree rvtree lsdd_t rsdd_t lsdd_f false_expanded,
    sdd_of_var n lvtree b lsdd_t ->
    sdd_of_var n lvtree (negb b) lsdd_f ->
    sdd_of_var n rvtree b rsdd_t ->
    expanded_sdd rvtree AFalse false_expanded ->
    sdd_of_var n (VNode lvtree rvtree) b
               (Or [(lsdd_t, rsdd_t); (lsdd_f, false_expanded)]).

(*
The generated term containing the unsat branch:
(Or
 (((Atom True)
   (Or
    (((Atom (Var 1 true)) (Atom True)) ((Atom (Var 1 false)) (Atom False)))))
  ((Atom True) (Or (((Atom True) (Atom False)))))))
*)
Example sdd_of_var_ex0:
  sdd_of_var 2 (VNode (VAtom 1) (VNode (VAtom 2) (VAtom 3))) true
             (Or [(Atom ATrue,
                   (Or [(Atom (AVar 2 true), (Atom ATrue));
                          (Atom (AVar 2 false), Atom AFalse)]));
                    (Atom ATrue, Or ([(Atom ATrue, Atom AFalse)]))]).
Proof.
  (* coming up with this term SUCKS... *)
  eapply (VarOfNode 2 true (VAtom 1)
                    (VNode (VAtom 2) (VAtom 3))
                    (Atom ATrue)
                    (Or [(Atom (AVar 2 true), Atom ATrue); (Atom (AVar 2 false), Atom AFalse)])
                    (Atom ATrue)
                    (Or ([(Atom ATrue, Atom AFalse)]))
         ).
  - constructor. discriminate.
  - constructor. discriminate.
  - constructor. constructor.
    + constructor.
    + constructor. discriminate.
    + constructor.
  - apply ExpandFalseNode.
    + constructor.
    + constructor.
Qed.

Example ex_sdd_apply0:
  sdd_apply OAnd (Or [(Atom ATrue, Atom AFalse)]) (Or [(Atom ATrue, Atom AFalse)]) (Or [(Atom ATrue, Atom AFalse)]).
Proof.
  apply ApplyOr.
  apply (NonEmptyLeft (Atom ATrue) (Atom AFalse) [] [(Atom ATrue, Atom AFalse)] _ _ OAnd).
  repeat constructor.
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
      * constructor.
      * constructor.
      * apply (NonEmptyRightUnsat _ _ _ _ (Atom AFalse)).
        { constructor. discriminate. }
        { constructor. }
        { constructor. }
    + apply (NonEmptyLeft (Atom (AVar 0 false)) (Atom AFalse) [] [(Atom (AVar 0 false), Atom AFalse)]).
      * apply (NonEmptyRightUnsat _ _ _ _ (Atom AFalse)).
        { constructor. discriminate. }
<<<<<<< HEAD
        { Admitted.
=======
        { constructor. }
        { apply NonEmptyRightSat. 
          - constructor.
          - constructor.
          - constructor.
          - constructor. }
      * constructor. 
Qed.
>>>>>>> 426c316f0ea7e6432240719f831722b8f1641f25


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

<<<<<<< HEAD

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
=======
>>>>>>> 426c316f0ea7e6432240719f831722b8f1641f25

