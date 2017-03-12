Require Export Bool.Bool.
Require Export List.
Require Export Coq.Unicode.Utf8_core.

Require Import VarSet.


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

Inductive vtree_varSet : vtree -> varSet -> Prop :=
| vtree_varSet_atom : forall n, vtree_varSet (VAtom n) (Var n Empty)
| vtree_varSet_node : forall l r lSet rSet resSet, vtree_varSet l lSet ->
                                                   vtree_varSet r rSet ->
                                                   union lSet rSet resSet ->
                                                   vtree_varSet (VNode l r) resSet.

Theorem vtree_varSet_unique :
  forall v vs, vtree_varSet v vs -> unique vs.
Proof.
  intros v vs Hv.
  induction Hv.
  - repeat constructor.
  - apply (union_unique lSet rSet); assumption.
Qed.

Inductive vtree_correct : vtree -> Prop :=
| vtree_correct_atom : forall n, vtree_correct (VAtom n)
| vtree_correct_node : forall l r lSet rSet, vtree_correct l ->
                                             vtree_correct r ->
                                             vtree_varSet l lSet ->
                                             vtree_varSet r rSet ->
                                             disjoint lSet rSet ->
                                             vtree_correct (VNode l r).

Inductive atom : Type :=
| AFalse : atom
| ATrue : atom
| AVar :  nat -> bool -> atom.

Inductive atom_varSet : atom -> varSet -> Prop :=
| atom_varSet_false : atom_varSet AFalse Empty
| atom_varSet_true  : atom_varSet ATrue Empty
| atom_varSet_var   : forall n b, atom_varSet (AVar n b) (Var n Empty).


Inductive sdd : Type :=
          (*prime sub   next *)
| Or: list (sdd * sdd) -> sdd
| Atom : atom -> sdd.

Inductive

sdd_varSet : sdd -> varSet -> Prop :=
| sdd_varSet_atom : forall a vs, atom_varSet a vs -> sdd_varSet (Atom a) vs
| sdd_varSet_or   : forall l vs, sddList_varSet l vs -> sdd_varSet (Or l) vs

with

sddList_varSet : list (sdd*sdd) -> varSet -> Prop :=
| sddList_varSet_empty : sddList_varSet [] Empty
| sddList_varSet_pair  : forall p s rest pVs sVs rVs pairVs resVs, sdd_varSet p pVs ->
                                                                   sdd_varSet s sVs ->
                                                                   sddList_varSet rest rVs ->
                                                                   union pVs sVs pairVs ->
                                                                   union pairVs rVs resVs ->
                                                                   sddList_varSet ((p, s)::rest) resVs.

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
| NonEmptyRightUnsat : forall (prime1 prime2 newprime sub1 sub2: sdd) (o : op) (tl subres : list (sdd * sdd)),
    sdd_apply OAnd prime1 prime2 newprime ->
    sdd_unsat newprime ->
    apply_single_list o prime1 sub1 tl subres -> (* process the rest of the list *)
    apply_single_list o prime1 sub1 ((prime2, sub2)::tl) subres.



Check sdd_apply_ind.
Check apply_single_list_ind.
Check apply_or_list.

Print sdd_apply_ind.

Section sdd_apply_ind'.
  Variable P: op -> sdd -> sdd -> sdd → Prop.
  Variable Atom_case' : forall  (a1 a2 a3 :atom) (o : op),
      atom_apply o a1 a2 a3 -> P o (Atom a1) (Atom a2) (Atom a3).
  Hypothesis Apply_empty_list' : forall (o : op) (l : list (sdd * sdd)),
      P o (Or l) (Or [ ]) (Or [ ]).
  Hypothesis Apply_empty_l_list' : forall (o : op) (l : list (sdd * sdd)),
      P o (Or [ ]) (Or l) (Or [ ]).
  Hypothesis ApplySingleConcatenation: forall p1 p2 s1 s2 newprime newsub l lres o,
      sdd_apply OAnd p1 p2 newprime ->
      sdd_apply o s1 s2 newsub ->
      sdd_sat newprime ->
      P o (Or [(p1, s1)]) (Or [(p2, s2)]) (Or [(newprime, newsub)]) -> 
      P o (Or [(p1, s1)]) (Or l) (Or lres) ->
      P o (Or [(p1, s1)]) (Or ((p2, s2) :: l)) (Or ((newprime, newsub) :: lres)).
  Hypothesis ApplyUnsatSingleConcatenation: forall p1 p2 s1 s2 newprime l lres o,
      sdd_apply OAnd p1 p2 newprime ->
      sdd_unsat newprime ->
      P o (Or [(p1, s1)]) (Or l) (Or lres) ->
      P o (Or [(p1, s1)]) (Or ((p2, s2) :: l)) (Or lres).
  Hypothesis ApplyConcat : forall l11 l12 l2 l11res l12res o,
      P o (Or l11) (Or l2) (Or l11res) ->
      P o (Or l12) (Or l2) (Or l12res) ->
      P o (Or (l11 ++ l12)) (Or l2) (Or (l11res ++ l12res)).
  Hypothesis ApplyCombine : forall o p1 p2 s1 s2 nprime nsub,
      sdd_apply OAnd p1 p2 nprime ->
      sdd_apply o s1 s2 nsub ->
      P OAnd p1 p2 nprime ->
      P o s1 s2 nsub ->
      P o (Or [(p1, s1)]) (Or [(p2, s2)]) (Or [(nprime, nsub)]).


  Fixpoint sdd_apply_ind' (o : op) (s1 s2 res :sdd) (d : sdd_apply o s1 s2 res): P o s1 s2 res :=
    match d in (sdd_apply o0 s3 s4 s5) return (P o0 s3 s4 s5) with
    | ApplyAtom a1 a2 a3 o d => Atom_case' a1 a2 a3 o d 
    | ApplyOr l1 l2 res o or_d => 
      (* handle applying a (prime,sub) pair to a list *)
      (* handle non_empty_right derivations *)
      let handle_sub_l :=
          fix handle_sub_l (prime sub : sdd) (l res : list (sdd * sdd)) (o : op)
              (d : apply_single_list o prime sub l res) : P o (Or [(prime, sub)]) (Or l) (Or res) :=
            match d in (apply_single_list o prime sub l res) return P o (Or [(prime, sub)]) (Or l) (Or res) with
            | EmptyRight p s o =>
              Apply_empty_list' o [(p, s)]
            | NonEmptyRightSat p1 p2 s1 s2 nprime nsub o1 tl subres app_prime_d sat_d app_sub_d rest_d =>
              let sub_proof := handle_sub_l p1 s1 tl subres o1 rest_d in
              let prime_holds := sdd_apply_ind' OAnd p1 p2 nprime app_prime_d in
              let sub_holds := sdd_apply_ind' o1 s1 s2 nsub app_sub_d in
              let combined := ApplyCombine o1 p1 p2 s1 s2 nprime nsub app_prime_d app_sub_d prime_holds sub_holds in
              ApplySingleConcatenation p1 p2 s1 s2 nprime nsub tl subres o1
                                        app_prime_d app_sub_d sat_d combined sub_proof
            | NonEmptyRightUnsat prime1 prime2 newprime sub1 sub2 o tl subres app_prime_d unsat_d rest_d =>
              let sub_proof := handle_sub_l prime1 sub1 tl subres o rest_d in
              ApplyUnsatSingleConcatenation prime1 prime2 sub1 sub2 newprime tl subres o app_prime_d unsat_d sub_proof
            end in
              (* handle non_empty_left derivations *)
      let handle_l :=
          fix handle_l o l1 l2 res (cur_d : apply_or_list o l1 l2 res) : P o (Or l1) (Or l2) (Or res) :=
            match cur_d in (apply_or_list o l1 l2 res) return (P o (Or l1) (Or l2) (Or res)) with
            | EmptyLeft l o1  => Apply_empty_l_list' o1 l
            | NonEmptyLeft prime sub ltail singleres orres linput o1 single_d sub_or_d =>
              let single_proof := handle_sub_l prime sub linput singleres o1 single_d in
              let or_proof := handle_l o1 ltail linput orres sub_or_d in
              ApplyConcat [(prime, sub)] ltail linput singleres orres o1 single_proof or_proof
                   
            end in
              handle_l o l1 l2 res or_d
    end.
End sdd_apply_ind'.

Print sdd_apply_ind.

(*
Section sdd_apply_ind_vtree.
  Variable Atom_case' : forall  (a1 a2 a3 :atom) (o : op),
      atom_apply o a1 a2 a3 -> sdd_vtree (Atom a1) v -> sdd_vtree (Atom a2) v -> sdd_vtree (Atom a3) v. 
  Hypothesis Apply_empty_list' : forall (o : op) (l : list (sdd * sdd)),
      sdd_vtree (Or l) v -> sdd_vtree (Or []) v o (Or l) (Or [ ]) (Or [ ]).
  Hypothesis Apply_empty_l_list' : forall (o : op) (l : list (sdd * sdd)),
      P o (Or [ ]) (Or l) (Or [ ]).
  Hypothesis ApplySingleConcatenation: forall p1 p2 s1 s2 newprime newsub l lres o,
      sdd_apply OAnd p1 p2 newprime ->
      sdd_apply o s1 s2 newsub ->
      sdd_sat newprime ->
      P o (Or [(p1, s1)]) (Or [(p2, s2)]) (Or [(newprime, newsub)]) -> 
      P o (Or [(p1, s1)]) (Or l) (Or lres) ->
      P o (Or [(p1, s1)]) (Or ((p2, s2) :: l)) (Or ((newprime, newsub) :: lres)).
  Hypothesis ApplyUnsatSingleConcatenation: forall p1 p2 s1 s2 newprime l lres o,
      sdd_apply OAnd p1 p2 newprime ->
      sdd_unsat newprime ->
      P o (Or [(p1, s1)]) (Or l) (Or lres) ->
      P o (Or [(p1, s1)]) (Or ((p2, s2) :: l)) (Or lres).
  Hypothesis ApplyConcat : forall l11 l12 l2 l11res l12res o,
      P o (Or l11) (Or l2) (Or l11res) ->
      P o (Or l12) (Or l2) (Or l12res) ->
      P o (Or (l11 ++ l12)) (Or l2) (Or (l11res ++ l12res)).
  Hypothesis ApplyCombine : forall o p1 p2 s1 s2 nprime nsub,
      sdd_apply OAnd p1 p2 nprime ->
      sdd_apply o s1 s2 nsub ->
      P OAnd p1 p2 nprime ->
      P o s1 s2 nsub ->
      P o (Or [(p1, s1)]) (Or [(p2, s2)]) (Or [(nprime, nsub)]).


  Fixpoint sdd_apply_ind' (o : op) (s1 s2 res :sdd) (d : sdd_apply o s1 s2 res): P o s1 s2 res :=
    match d in (sdd_apply o0 s3 s4 s5) return (P o0 s3 s4 s5) with
    | ApplyAtom a1 a2 a3 o d => Atom_case' a1 a2 a3 o d 
    | ApplyOr l1 l2 res o or_d => 
      (* handle applying a (prime,sub) pair to a list *)
      (* handle non_empty_right derivations *)
      let handle_sub_l :=
          fix handle_sub_l (prime sub : sdd) (l res : list (sdd * sdd)) (o : op)
              (d : apply_single_list o prime sub l res) : P o (Or [(prime, sub)]) (Or l) (Or res) :=
            match d in (apply_single_list o prime sub l res) return P o (Or [(prime, sub)]) (Or l) (Or res) with
            | EmptyRight p s o =>
              Apply_empty_list' o [(p, s)]
            | NonEmptyRightSat p1 p2 s1 s2 nprime nsub o1 tl subres app_prime_d sat_d app_sub_d rest_d =>
              let sub_proof := handle_sub_l p1 s1 tl subres o1 rest_d in
              let prime_holds := sdd_apply_ind' OAnd p1 p2 nprime app_prime_d in
              let sub_holds := sdd_apply_ind' o1 s1 s2 nsub app_sub_d in
              let combined := ApplyCombine o1 p1 p2 s1 s2 nprime nsub app_prime_d app_sub_d prime_holds sub_holds in
              ApplySingleConcatenation p1 p2 s1 s2 nprime nsub tl subres o1
                                        app_prime_d app_sub_d sat_d combined sub_proof
            | NonEmptyRightUnsat prime1 prime2 newprime sub1 sub2 o tl subres app_prime_d unsat_d rest_d =>
              let sub_proof := handle_sub_l prime1 sub1 tl subres o rest_d in
              ApplyUnsatSingleConcatenation prime1 prime2 sub1 sub2 newprime tl subres o app_prime_d unsat_d sub_proof
            end in
              (* handle non_empty_left derivations *)
      let handle_l :=
          fix handle_l o l1 l2 res (cur_d : apply_or_list o l1 l2 res) : P o (Or l1) (Or l2) (Or res) :=
            match cur_d in (apply_or_list o l1 l2 res) return (P o (Or l1) (Or l2) (Or res)) with
            | EmptyLeft l o1  => Apply_empty_l_list' o1 l
            | NonEmptyLeft prime sub ltail singleres orres linput o1 single_d sub_or_d =>
              let single_proof := handle_sub_l prime sub linput singleres o1 single_d in
              let or_proof := handle_l o1 ltail linput orres sub_or_d in
              ApplyConcat [(prime, sub)] ltail linput singleres orres o1 single_proof or_proof
                   
            end in
              handle_l o l1 l2 res or_d
    end.
End sdd_apply_ind'.
*)



Inductive sdd_vtree : sdd -> vtree -> Prop :=
| AtomTrue : forall n, sdd_vtree (Atom ATrue) (VAtom n)
| AtomFalse : forall n, sdd_vtree (Atom AFalse) (VAtom n)
| AtomVar : forall n b, sdd_vtree (Atom (AVar n b)) (VAtom n)
| OrEmpty : forall v, vtree_correct v -> sdd_vtree (Or []) v
| OrSingle: forall prime sub lvtree rvtree tail, 
    sdd_vtree prime lvtree ->
    sdd_vtree sub rvtree ->
    sdd_vtree (Or (tail)) (VNode lvtree rvtree) ->
    vtree_correct (VNode lvtree rvtree) ->
    sdd_vtree (Or ((prime, sub) :: tail)) (VNode lvtree rvtree)
| ExtendL : forall l r sdd,
    sdd_vtree sdd l ->
    vtree_correct (VNode l r) ->
    sdd_vtree sdd (VNode l r)
| ExtendR : forall l r sdd,
    sdd_vtree sdd r ->
    vtree_correct (VNode l r) ->
    sdd_vtree sdd (VNode l r).


Lemma single_vtree :
  forall (prime sub : sdd) l v,
    sdd_vtree (Or [(prime, sub)]) v ->
    sdd_vtree (Or l) v ->
    sdd_vtree (Or ((prime, sub) :: l)) v.
Proof.
  intros.
  induction l.
  - assumption.
  - inversion H. subst. inversion H0. subst.
    apply OrSingle.
    + assumption.
    + assumption.
    + assumption.
    +  admit.
Admitted.

Lemma vtree_concat :
  forall l1 l2 v,
    sdd_vtree (Or l1) v ->
    sdd_vtree (Or l2) v ->
    sdd_vtree (Or (l1 ++ l2)) v.
Proof.
  intros. induction l1.
  - simpl. assumption.
  - destruct a. remember (l1 ++ l2) as l. simpl. rewrite <- Heql. apply single_vtree.
    + inversion H. subst. constructor. assumption. assumption. constructor.
    (* + apply IHl1. inversion H. subst. assumption. admit. *)
Admitted.

Lemma vtree_slice_l :
  forall l1 l2 v,
    sdd_vtree (Or (l1 ++ l2)) v ->
    sdd_vtree (Or l1) v.
Proof.
  intros. induction l1.
  - constructor. Admitted.
(*  - inversion H. subst.
    apply single_vtree.
    + constructor. assumption. assumption.
      constructor.
    + apply IHl1. inversion H.
      subst. assumption.
Admitted. *)

Lemma vtree_reorder :
  forall l1 l2 v,
    sdd_vtree (Or (l1 ++ l2)) v ->
    sdd_vtree (Or (l2 ++ l1)) v.
Proof.
  intros. induction l1.
  - simpl in H. remember (l2 ++ []) as l3. remember (l2 ++ []) as l4.  admit.
Admitted.


Lemma vtree_slice_r :
  forall l1 l2 v,
    sdd_vtree (Or (l1 ++ l2)) v ->
    sdd_vtree (Or l2) v.
Proof.
  intros. induction l2.
  - constructor. Admitted. (*
  - destruct a. apply single_vtree.
    + inversion H.
      * symmetry in H1. apply app_eq_nil in H1. inversion H1. inversion H3.
      * induction l1.
        { simpl in H0. admit. }
        { apply IHl1.
          - inversion H.  subst. 


Admitted.*)

Lemma unsat_concat :
  forall prime sub l,
    sdd_unsat (Or [(prime, sub)]) ->
    sdd_unsat (Or l) ->
    sdd_unsat (Or ((prime, sub) :: l)).
Proof.
  intros.
  inversion H.
  - subst. constructor.
    + assumption.
    + assumption.
  - subst. apply UnsatOrSub.
    + assumption.
    + assumption.
Qed.

Lemma unsat_append :
  forall l1 l2,
    sdd_unsat (Or l1) ->
    sdd_unsat (Or l2) ->
    sdd_unsat (Or (l1 ++ l2)).
Proof.
  intros.
  induction l1.
  - simpl. assumption.
  - simpl. destruct a.
    remember (l1 ++ l2) as l. apply unsat_concat.
    + inversion H. subst. constructor.
      * assumption.
      * constructor.
      * apply UnsatOrSub.
        { assumption. }
        { constructor. }
    + apply IHl1.
      * inversion H. assumption. assumption. 
Qed.

Lemma unsat_split_l :
  forall l1 l2,
    sdd_unsat (Or (l1 ++ l2)) ->
    sdd_unsat (Or l1).
Proof.
  intros. induction l1.
  - constructor.
  - destruct a. apply unsat_concat.
    + inversion H. subst. constructor.
      * assumption.
      * constructor.
      * apply UnsatOrSub.
        { assumption. }
        { constructor. }
    + apply IHl1.
      * inversion H.
        { assumption. }
        { assumption. }
Qed. 


Lemma unsat_app_nil:
  forall l,
    sdd_unsat (Or (l ++ [])) ->
    sdd_unsat (Or l).
Proof.
  intros.
  induction l.
  - constructor.
  - inversion H.
    + subst. constructor.
      * assumption.
      * apply IHl.
        { assumption. }
    + subst. apply UnsatOrSub.
      * assumption.
      * apply IHl.
        { assumption. }
Qed.

Lemma unsat_split_r:
  forall l1 l2,
    sdd_unsat (Or (l1 ++ l2)) ->
    sdd_unsat (Or (l2)).
Proof.
  intros. 
  induction l1, l2.
  - constructor.
  - simpl in H. assumption.
  - constructor.
  - apply IHl1.
    + inversion H.
      * subst.  assumption.
      * subst.  assumption.
Qed. 
     


Theorem apply_unsat :
  forall sdd1 sdd2 sddres,
    sdd_unsat sdd1 ->
    sdd_apply OAnd sdd1 sdd2 sddres ->
    sdd_unsat sddres.
Proof.
  intros. induction H0 using sdd_apply_ind'.
  - inversion H0;
      try (inversion H; subst; inversion H);
      try (subst; inversion H);
      try (subst; constructor);
      try (subst; assumption).
  - constructor.
  - constructor.
  - subst. apply unsat_concat.
    + apply IHsdd_apply1. assumption.
    + apply IHsdd_apply2. assumption.
  - apply IHsdd_apply. assumption.
  - apply unsat_append.
    + apply IHsdd_apply. apply (unsat_split_l l11 l12). assumption. 
    + apply IHsdd_apply0. apply (unsat_split_r l11 l12). assumption.
  - inversion H. subst. constructor.
    + apply IHsdd_apply1. assumption.
    + assumption.
    + apply UnsatOrSub;
        try apply IHsdd_apply2;
        assumption.
Qed.


Inductive

decomposable : sdd -> Prop :=
| decomposable_atom : forall a, decomposable (Atom a)
| decomposable_or : forall l, decomposable_pairs l -> decomposable (Or l)

with

decomposable_pairs : list (sdd*sdd) -> Prop :=
| decomposable_pairs_empty : decomposable_pairs []
| decomposable_pairs_pair  : forall p s rest pVs sVs, sdd_varSet p pVs ->
                                                      sdd_varSet s sVs ->
                                                      disjoint pVs sVs ->
                                                      decomposable_pairs rest ->
                                                      decomposable_pairs ((p, s)::rest).

Theorem sdd_decomposable :
  forall sdd v,
    sdd_vtree sdd v ->
    decomposable sdd.
Admitted.

(* ---------------------------- *)
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
  Admitted. 
(*   induction l. generalize dependent s. generalize dependent p. *)
(*   - intros. inversion H2. constructor. *)
(*   - generalize dependent p. generalize dependent s. *)
(*     intros.  apply (Hvl op l). *)
(*     + intros. apply (IHl o ); repeat assumption. *)
(* Admitted. *)

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
   


(* Theorem compile_correct : *)
(*   forall (boolExp:boolExpr) (sdd:sdd) (input:varAssign) (result:bool), *)
(*     compile boolExp sdd → *)
(*     eval_sdd sdd result input → *)
(*     eval boolExp result input. *)

