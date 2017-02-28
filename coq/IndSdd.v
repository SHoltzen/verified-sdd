Require Export Bool.Bool.
Require Export List.
Require Export Coq.Unicode.Utf8_core.

Require Import VarAssign.


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


Inductive atom_apply : op → atom → atom → atom → Prop :=
| AndTT : atom_apply OAnd ATrue ATrue ATrue
| AndTF : atom_apply OAnd ATrue AFalse AFalse
| AndFT : atom_apply OAnd AFalse ATrue AFalse
| AndFF : atom_apply OAnd AFalse AFalse AFalse
| AndVT : forall (n:nat) (b:bool), atom_apply OAnd (AVar n b) ATrue (AVar n b)
| AndTV : forall (n:nat) (b:bool), atom_apply OAnd ATrue (AVar n b) (AVar n b)
| AndVF : forall (n:nat) (b:bool), atom_apply OAnd (AVar n b) AFalse AFalse
| AndFV : forall (n:nat) (b:bool), atom_apply OAnd AFalse (AVar n b) AFalse
| AndVVEq : forall (n:nat) (b:bool), atom_apply OAnd (AVar n b) (AVar n b) (AVar n b)
| AndVVNeq : forall (n:nat) (b1:bool) (b2:bool), (b1 <> b2) → atom_apply OAnd (AVar n b1) (AVar n b2) (AFalse).



Inductive sdd_apply : op -> sdd -> sdd -> sdd -> Prop :=
| ApplyAtom : forall (a1:atom) (a2:atom) (a3:atom) (o:op),
    atom_apply o a1 a2 a3 → sdd_apply o (Atom a1) (Atom a2) (Atom a3)
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
  apply ApplyAtom. constructor.
  Qed.

Example ex_sdd_apply2:
  sdd_apply OAnd (Or [(Atom (AVar 0 true), Atom (AVar 1 true)); (Atom (AVar 0 false), Atom(AFalse))])
            (Or [(Atom (AVar 0 true), Atom (AVar 1 true)); (Atom (AVar 0 false), Atom(AFalse))])
            (Or [(Atom (AVar 0 true), Atom (AVar 1 true)); (Atom (AVar 0 false), Atom(AFalse))]).
Proof.
  constructor.
  - apply (NonEmptyLeft (Atom (AVar 0 true)) (Atom (AVar 1 true)) [(Atom (AVar 0 false), Atom AFalse)]
                        [(Atom (AVar 0 true), Atom (AVar 1 true))]).
    + constructor.
      * constructor. constructor.
      * constructor.
      * constructor. constructor.
      * constructor.
        { constructor. constructor. discriminate. }
        { constructor. }
    + apply (NonEmptyLeft (Atom (AVar 0 false)) (Atom AFalse) [] [(Atom (AVar 0 false), Atom AFalse)]).
      * apply NonEmptyRightUnsat.
        { constructor. constructor. discriminate. }
        { constructor. constructor. constructor. constructor. constructor. constructor.  constructor. }
      * constructor.
Qed.

Example sdd_and_eq:
  forall  (v : vtree) (a : sdd),
    sdd_vtree a v ->
    sdd_apply OAnd a a a.
Proof.
  intros.
  destruct a.
  induction H.
  -  constructor. constructor.
  -  constructor. constructor.
  -  constructor. constructor.
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

(* Inductive compile *)


Ltac rewAndInvert :=
  match goal with
  | [ H1: _ = ?x, H2: _ = ?x |- _ ] =>
      rewrite <- H2 in H1; inversion H1
  end.

Lemma single_list_right_empty :
  forall o prime sub res, apply_single_list o prime sub [ ] res → res = [].
Proof.
  intros.  inversion H. reflexivity.
Qed.


Lemma or_list_right_empty :
  forall o l res, apply_or_list o l [] res → res = [].
Proof. 
  intros. generalize dependent res. induction l.
  * intros. inversion H. reflexivity.
  * intros. inversion H. apply IHl in H6.
    apply single_list_right_empty in H3.
    rewrite H3. rewrite H6. reflexivity.
Qed.

Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | [] => True
      | h::t => P h /\ All t
    end.
End All.

Section AllPairs.
  Variable T : Set.
  Variable P : T → Prop.

  Fixpoint AllPairs (ls : list (T*T)) : Prop :=
    match ls with
    | [] => True
    | (a,b)::t => P a ∧ P b ∧ AllPairs t
    end.
End AllPairs.
  
Section sdd_ind'.
  Variable P: sdd → Prop.
  Hypothesis Or_case' : forall (l:list (sdd*sdd)), AllPairs sdd P l → P (Or l).
  Hypothesis Atom_case' : forall (a:atom), P (Atom a).

    Fixpoint sdd_ind' (s:sdd) : P s :=
    let list_or_ind := (fix list_or_ind (l: list (sdd*sdd)) : (AllPairs sdd P l) :=
           match l with
           | [] => I
           | (p,s)::rest => (conj (sdd_ind' p) (conj (sdd_ind' s) (list_or_ind rest)))
           end)  in
    match s with
    | Or l => Or_case' l (list_or_ind l)
    | Atom a => Atom_case' a
    end.

End sdd_ind'.


Lemma or_append_vtree :
  forall subres orres v,
    sdd_vtree (Or subres) v ->
    sdd_vtree (Or orres) v ->
    sdd_vtree (Or (subres ++ orres)) v.
Proof.
  Admitted.

Lemma append_list_vtree :
  forall vl vr p s l,
    sdd_vtree p vl ->
    sdd_vtree s vr ->
    sdd_vtree (Or l) (VNode vl vr) -> 
    sdd_vtree (Or ((p, s)::l)) (VNode vl vr).
Admitted.



(* apply_single_list o p1 s1 l0 subres *)
Lemma single_list_vtree :
  forall lvtree rvtree p s l o subres,
    sdd_vtree p lvtree ->
    sdd_vtree s rvtree ->
    sdd_vtree (Or l) (VNode lvtree rvtree) ->
    apply_single_list o p s l subres ->
    sdd_vtree (Or subres) (VNode lvtree rvtree).
Proof.
  induction l. generalize dependent s. generalize dependent p.
  - intros. inversion H2. constructor.
  - generalize dependent p. generalize dependent s.
    intros.  apply (Hvl op l).
    + intros. apply (IHl o ); repeat assumption.
      * 

Lemma concat_list_vtree :
  forall vl vr l1 l2,
    sdd_vtree (Or l1) (VNode vl vr) -> 
    sdd_vtree (Or l2) (VNode vl vr) -> 
    sdd_vtree (Or (l1 ++ l2)) (VNode vl vr).
Admitted.

(* apply_or_list o l ((p2, s2) :: l0) orres *)
(* sdd_vtree (Or orres) (VNode lvtree0 rvtree0) *)
Lemma or_list_vtree :
  forall lvtree rvtree l l0 res o,
    sdd_vtree (Or l) (VNode lvtree rvtree) ->
    sdd_vtree (Or l0) (VNode lvtree rvtree) ->
    apply_or_list o l l0 res ->
    sdd_vtree (Or res) (VNode lvtree rvtree).
Proof.
  induction l.
  - intros. inversion H1. constructor.
  - intros. inversion H1. subst.
    + apply concat_list_vtree.
      * apply (single_list_vtree lvtree rvtree prime sub l0 o singleres); repeat (inversion H; assumption).
      * apply (IHl l0 orres o); repeat (inversion H; assumption).
Qed.

  (*  apply_or_list o ((p1, s1) :: l) ((p2, s2) :: l0) (singleres ++ orres) *)
Lemma or_list_multi_vtree :
  forall lvtree rvtree p1 s1 p2 s2 l l0 res o,
    sdd_vtree p1 lvtree ->
    sdd_vtree p2 lvtree ->
    sdd_vtree s1 rvtree ->
    sdd_vtree s2 rvtree ->
    sdd_vtree (Or l) (VNode lvtree rvtree) ->
    sdd_vtree (Or l0) (VNode lvtree rvtree) ->
    apply_or_list o ((p1, s1)::l) ((p2, s2) :: l0) res ->
    sdd_vtree (Or res) (VNode lvtree rvtree).
Admitted.

Theorem apply_preserves_vtree :
  forall sdd1 sdd2 sddRes v o,
    sdd_vtree sdd1 v →
    sdd_vtree sdd2 v →
    sdd_apply o sdd1 sdd2 sddRes →
    sdd_vtree sddRes v.
Proof.
  destruct v.
  - intros. inversion H. subst.
    + inversion H0.
      * subst. inversion H1.
        { subst. inversion H5. constructor. }
      * subst. inversion H1.
        { subst. inversion H8.
          - subst.  constructor.
        }
    + subst. inversion H1. subst.
      assert (sdd_vtree (Or ((prime, sub) :: tail)) (VNode v1 v2)).
      { apply (append_list_vtree v1 v2 prime sub tail); repeat assumption. }
      remember ((prime, sub) :: tail) as l.
      eapply (or_list_vtree v1 v2 l l2 res o); repeat assumption.
  - intros. inversion H.
    + inversion H1.
      * subst. inversion H3; repeat (subst; constructor).
        { subst. discriminate H6. }
        { subst. inversion H0. subst. constructor. }
        { subst. discriminate H6. }
      * subst. inversion H0. subst.  discriminate H6.
    + subst. inversion H1. inversion H4.
      * constructor.
      * constructor.
      * constructor.
    + subst. inversion H0.
      * inversion H1. subst. inversion H6; repeat constructor.
      * subst. inversion H1. inversion H5. constructor.
      * subst. destruct b.
        { destruct b0; repeat (inversion H1; inversion H5; constructor). }
        { destruct b0; repeat (inversion H1; inversion H5; constructor). }
      * subst. inversion H1.
    + subst. inversion H. inversion H1. inversion H5. constructor.
Qed.
   


Theorem apply_preserves_vtree :
  forall sdd1 sdd2 sddRes v o,
    sdd_vtree sdd1 v →
    sdd_vtree sdd2 v →
    sdd_apply o sdd1 sdd2 sddRes →
    sdd_vtree sddRes v.
Proof.
  - induction sdd1 using sdd_ind'. destruct l.
    + intros sdd2 sddRes v o Hsdd1 Hsdd2 Happ. inversion Happ. inversion H2. constructor.
    + induction sdd2 using sdd_ind'.
      * intros sddRes v o Hsdd1 Hsdd2 Happ. destruct l0.
        { inversion Happ. apply or_list_right_empty in H4.
          rewrite H4. constructor. }
        { simpl in H0. destruct p as [p1 s1]. destruct p0 as [p2 s2]. destruct H0. destruct H1. destruct H. destruct H3.
          inversion Hsdd1. inversion Hsdd2.
          + repeat rewAndInvert. inversion Happ.
            * inversion H24. inversion H32. constructor.
              { rewrite <- H20. apply (H p2 newprime lvtree OAnd).
                assumption. rewrite <- H20 in H15. assumption. assumption. }
              { rewrite <- H21. apply (H3 s2 newsub rvtree o).
                assumption. rewrite <- H21 in H17. assumption. assumption. }
              { fold (app subres orres). apply or_append_vtree.
                - apply (single_list_vtree lvtree0 rvtree0 p1 s1 l0 o). subst.
                  + assumption.
                  + subst. assumption.
                  + subst. assumption.
                  + assumption.
                - subst.  apply (or_list_vtree lvtree0 rvtree0 p2 s2 l l0 orres o).
                  + assumption.
                  + assumption.
                  + assumption.
                  + assumption.
              }
              (*   lvtree rvtree p1 s1 p2 s2 l l0 res o *)
              { subst.
                apply (or_list_multi_vtree lvtree0 rvtree0 p1 s1 p2 s2 l l0 (singleres ++ orres) o).
                - assumption.
                - assumption.
                - assumption.
                - assumption.
                - assumption.
                - assumption.
                - assumption. }
        }
      * destruct v. intros.
        {  
             
Qed.

  (* - induction l. *)
  (*   + induction sdd2. *)
  (*     * intros. simpl in H. *)
        
    (*     { intros. inversion H2. inversion H6. assumption. } *)
    (*     { admit. } *)
    (*   * admit. *)
    (* + induction sdd2. *)
    (*   * induction l0. *)
    (*     { intros. simpl in H. inversion H. *)

    (* induction sdd2 using sdd_ind'. *)
    (* * intros. destruct sdd2. *)
    (* * induction l. *)
    (*   { induction l0. *)
    (*     - inversion H2. inversion H6. constructor. *)
    (*     - inversion H2. inversion H6. constructor. *)
    (*   } *)
    (*   { induction l0. *)
    (*     - inversion H2. apply or_list_right_empty in H6. rewrite H6. constructor. *)
    (*     - (* each prime in l0 applied to a prime in l1 produces a prime that obeys the correct vtree *) *)
    (*       inversion H0.  *)
    (*       + eapply IHl0. *)

(* Theorem apply_preserves_vtree : *)
(*   forall sdd1 sdd2 sddRes v o, *)
(*     sdd_vtree sdd1 v → *)
(*     sdd_vtree sdd2 v → *)
(*     sdd_apply o sdd1 sdd2 sddRes → *)
(*     sdd_vtree sddRes v. *)
(*   intros sdd1 sdd2 sddRes v o HSdd1 HSdd2 Happly. *)
(*   induction sdd1 using sdd_ind'; induction sdd2 using sdd_ind'. *)
(*   - inversion HSdd1; inversion HSdd2. *)
(*     * rewrite <- H2 in Happly. rewrite <- H4 in Happly. *)
(*       inversion Happly. inversion H8. constructor. *)
(*     * rewrite <- H2 in Happly.  inversion Happly. inversion H11. constructor. *)
(*     * rewrite <- H7 in Happly. inversion Happly. apply or_list_right_empty in H11. *)
(*       rewrite H11. constructor. *)
(*     * Admitted. *)

Theorem compile_correct :
  forall (boolExp:boolExpr) (sdd:sdd) (input:varAssign) (result:bool),
    compile boolExp sdd →
    eval_sdd sdd result input →
    eval boolExp result input.

