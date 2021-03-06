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
| Or: ((sdd * sdd)*(sdd * sdd)) -> sdd
| Atom : atom -> sdd.

Inductive op : Type :=
| OAnd.

(* the magic of the Vtree lets us turn SDD sat/unsat testing into syntactic queries of the SDD *)


(* idea: a false atom is unsat, a false atom conjoined with anything is unsat,
   in order for an OR to be unsat all its children must be unsat *)
Inductive sdd_unsat : sdd -> Prop :=
| UnsatAtom : sdd_unsat (Atom AFalse)
| UnsatOrPrime : forall (prime0 sub0 prime1 sub1 : sdd),
    sdd_unsat prime0 ->
    sdd_unsat prime1 ->
    sdd_unsat (Or ((prime0, sub0),(prime1, sub1)))
| UnsatOrSub: forall (prime0 sub0 prime1 sub1 : sdd),
    sdd_unsat sub0 ->
    sdd_unsat sub1 ->
    sdd_unsat (Or ((prime0, sub0),(prime1, sub1))).

Example sdd_unsat_ex0:
  sdd_unsat (Or ((Atom ATrue, Atom AFalse), (Atom (AVar 1 true), Atom AFalse))).
Proof.
  apply UnsatOrSub; constructor.
Qed.

(* idea: a true atom is sat, a var is sat,
   SAT /\ SAT is SAT, a single or-child must be sat for the
   OR to be sat *)
Inductive sdd_sat : sdd -> Prop :=
| SatAtom : sdd_sat (Atom ATrue)
| SatVar : forall n b, sdd_sat (Atom (AVar n b))
| SatOrLeft : forall tl (prime sub : sdd),
    sdd_sat prime ->
    sdd_sat sub ->
    sdd_sat (Or ((prime, sub), tl))
| SatOrRight : forall tl (prime sub : sdd),
    sdd_sat prime ->
    sdd_sat sub ->
    sdd_sat (Or (tl, (prime, sub))).


Example sdd_sat_ex0 :
  sdd_sat (Or ((Atom ATrue, Atom AFalse), (Atom ATrue, Atom (AVar 1 true)))).
Proof.
  apply SatOrRight; constructor.
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
| ApplyOr : forall o p1 s1 p2 s2 pa sa pb sb pRes1 sRes1 pRes2 sRes2,
    cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pRes1,sRes1) (pRes2,sRes2) ->
    sdd_apply o (Or ((p1,s1),(p2,s2))) (Or ((pa,sa),(pb,sb))) (Or ((pRes1,sRes1),(pRes2,sRes2)))

with

cross_and_prune : op -> (sdd*sdd) -> (sdd*sdd) -> (sdd*sdd) -> (sdd*sdd) -> (sdd*sdd) -> (sdd*sdd)
                  -> Prop :=
| OneSatA1 : forall o p1 s1 p2 s2 pa sa pb sb pa1 sa1,
  sdd_apply OAnd p1 pa pa1 ->
  sdd_apply OAnd p2 pa (Atom AFalse) ->
  sdd_apply OAnd p1 pb (Atom AFalse) ->
  sdd_apply OAnd p2 pb (Atom AFalse) ->
  sdd_sat pa1 -> sdd_apply o s1 sa sa1 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pa1,sa1) ((Atom ATrue), (Atom AFalse))
| OneSatA2 : forall o p1 s1 p2 s2 pa sa pb sb pa2 sa2,
  sdd_apply OAnd p1 pa (Atom AFalse) ->
  sdd_apply OAnd p2 pa pa2 ->
  sdd_apply OAnd p1 pb (Atom AFalse) ->
  sdd_apply OAnd p2 pb (Atom AFalse) ->
  sdd_sat pa2 -> sdd_apply o s2 sa sa2 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pa2,sa2) ((Atom ATrue), (Atom AFalse))
| OneSatB1 : forall o p1 s1 p2 s2 pa sa pb sb pb1 sb1,
  sdd_apply OAnd p1 pa (Atom AFalse) ->
  sdd_apply OAnd p2 pa (Atom AFalse) ->
  sdd_apply OAnd p1 pb pb1 ->
  sdd_apply OAnd p2 pb (Atom AFalse) ->
  sdd_sat pb1 -> sdd_apply o s1 sb sb1 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pb1,sb1) ((Atom ATrue), (Atom AFalse))
| OneSatB2 : forall o p1 s1 p2 s2 pa sa pb sb pb2 sb2,
  sdd_apply OAnd p1 pa (Atom AFalse) ->
  sdd_apply OAnd p2 pa (Atom AFalse) ->
  sdd_apply OAnd p1 pb (Atom AFalse) ->
  sdd_apply OAnd p2 pb pb2 ->
  sdd_sat pb2 -> sdd_apply o s1 sb sb2 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pb2,sb2) ((Atom ATrue), (Atom AFalse))
| TwoSatA1A2 : forall o p1 s1 p2 s2 pa sa pb sb pa1 sa1 pa2 sa2,
  sdd_apply OAnd p1 pa pa1 ->
  sdd_apply OAnd p2 pa pa2 ->
  sdd_apply OAnd p1 pb (Atom AFalse) ->
  sdd_apply OAnd p2 pb (Atom AFalse) ->
  sdd_sat pa1 -> sdd_sat pa2 ->
  sdd_apply o s1 sa sa1 -> sdd_apply o s2 sa sa2 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pa1,sa1) (pa2, sa2)
| TwoSatA1B1 : forall o p1 s1 p2 s2 pa sa pb sb pa1 sa1 pb1 sb1,
  sdd_apply OAnd p1 pa pa1 ->
  sdd_apply OAnd p2 pa (Atom AFalse) ->
  sdd_apply OAnd p1 pb pb1 ->
  sdd_apply OAnd p2 pb (Atom AFalse) ->
  sdd_sat pa1 -> sdd_sat pb1 ->
  sdd_apply o s1 sa sa1 -> sdd_apply o s1 sb sb1 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pa1,sa1) (pb1, sb1)
| TwoSatA1B2 : forall o p1 s1 p2 s2 pa sa pb sb pa1 sa1 pb2 sb2,
  sdd_apply OAnd p1 pa pa1 ->
  sdd_apply OAnd p2 pa (Atom AFalse) ->
  sdd_apply OAnd p1 pb (Atom AFalse) ->
  sdd_apply OAnd p2 pb pb2 ->
  sdd_sat pa1 -> sdd_sat pb2 ->
  sdd_apply o s1 sa sa1 -> sdd_apply o s2 sb sb2 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pa1,sa1) (pb2, sb2)
| TwoSatA2B1 : forall o p1 s1 p2 s2 pa sa pb sb pa2 sa2 pb1 sb1,
  sdd_apply OAnd p1 pa (Atom AFalse) ->
  sdd_apply OAnd p2 pa pa2 ->
  sdd_apply OAnd p1 pb pb1 ->
  sdd_apply OAnd p2 pb (Atom AFalse) ->
  sdd_sat pa2 -> sdd_sat pb1 ->
  sdd_apply o s1 sa sa2 -> sdd_apply o s2 sb sb1 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pa2,sa2) (pb1, sb1)
| TwoSatA2B2 : forall o p1 s1 p2 s2 pa sa pb sb pa2 sa2 pb2 sb2,
  sdd_apply OAnd p1 pa (Atom AFalse) ->
  sdd_apply OAnd p2 pa pa2 ->
  sdd_apply OAnd p1 pb (Atom AFalse) ->
  sdd_apply OAnd p2 pb pb2 ->
  sdd_sat pa2 -> sdd_sat pb2 ->
  sdd_apply o s1 sa sa2 -> sdd_apply o s2 sb sb2 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pa2,sa2) (pb2, sb2)
| TwoSatB1B2 : forall o p1 s1 p2 s2 pa sa pb sb pb1 sb1 pb2 sb2,
  sdd_apply OAnd p1 pa (Atom AFalse) ->
  sdd_apply OAnd p2 pa (Atom AFalse) ->
  sdd_apply OAnd p1 pb pb1 ->
  sdd_apply OAnd p2 pb pb2 ->
  sdd_sat pb1 -> sdd_sat pb2 ->
  sdd_apply o s1 sb sb1 -> sdd_apply o s2 sb sb2 ->
  cross_and_prune o (p1,s1) (p2,s2) (pa,sa) (pb,sb) (pb1,sb1) (pb2, sb2).

Inductive sdd_vtree : sdd -> vtree -> Prop :=
| OrSingle: forall p1 s1 p2 s2 lvtree rvtree,
    sdd_vtree p1 lvtree ->
    sdd_vtree p2 lvtree ->
    sdd_vtree s1 rvtree ->
    sdd_vtree s2 rvtree ->
    sdd_vtree (Or ((p1,s1),(p2,s2))) (VNode lvtree rvtree)
| AtomTrue : forall n, sdd_vtree (Atom ATrue) (VAtom n)
| AtomFalse : forall n, sdd_vtree (Atom AFalse) (VAtom n)
| AtomVar : forall n b, sdd_vtree (Atom (AVar n b)) (VAtom n).


Example sdd_vtree_ex0:
  sdd_vtree (Or ((Atom (AVar 0 true), Atom (AVar 1 false)), ((Atom AFalse),(Atom AFalse))))
            (VNode (VAtom 0) (VAtom 1)).
Proof.
  constructor; constructor.
Qed.


(* an interesting theorem: all valid SDDs are either SAT or UNSAT. *)
Theorem sdd_sat_or_unsat :
  forall (sdd : sdd) vtree,
    sdd_vtree sdd vtree ->
    sdd_unsat sdd \/ sdd_sat sdd.
Proof.
Admitted.

(*Inductive expanded_sdd : vtree -> atom -> sdd -> Prop :=
| ExpandAtomT : forall n, expanded_sdd (VAtom n) ATrue (Atom ATrue)
| ExpandAtomF : forall n, expanded_sdd (VAtom n) AFalse (Atom AFalse)
| ExpandFalseNode : forall lvtree rvtree lsdd rsdd,
    expanded_sdd lvtree ATrue lsdd ->
    expanded_sdd rvtree AFalse rsdd ->
    expanded_sdd (VNode lvtree rvtree) AFalse (Or [(lsdd, rsdd)])
| ExpandTrueNode : forall lvtree rvtree lsdd rsdd,
    expanded_sdd lvtree ATrue lsdd ->
    expanded_sdd rvtree ATrue lsdd ->
    expanded_sdd (VNode lvtree rvtree) ATrue (Or [(lsdd, rsdd)]).*)


(* need to handle cases when the derived primes are sat/unsat, otherwise
   you get false primes in the generated SDD *)
(*Inductive sdd_of_var : nat -> vtree -> bool -> sdd -> Prop :=
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
               (Or [(lsdd_t, rsdd_t); (lsdd_f, false_expanded)]).*)

(*
The generated term containing the unsat branch:
(Or
 (((Atom True)
   (Or
    (((Atom (Var 1 true)) (Atom True)) ((Atom (Var 1 false)) (Atom False)))))
  ((Atom True) (Or (((Atom True) (Atom False)))))))
*)
(*Example sdd_of_var_ex0:
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
Qed.*)

Example ex_sdd_apply0:
  sdd_apply OAnd
            (Or ((Atom ATrue, Atom ATrue), (Atom ATrue, Atom AFalse)))
            (Or ((Atom ATrue, Atom ATrue), (Atom ATrue, Atom AFalse)))
            (Or ((Atom ATrue, Atom ATrue), (Atom ATrue, Atom AFalse))).
Proof.
  apply ApplyOr. apply TwoSatA1B2. Admitted.

Example ex_sdd_apply1:
  sdd_apply OAnd (Atom ATrue) (Atom AFalse) (Atom AFalse).
Proof.
  apply ApplyAtom. constructor.
Qed.

Example ex_sdd_apply2:
  sdd_apply OAnd
            (Or ((Atom (AVar 0 true), Atom (AVar 1 true)), (Atom (AVar 0 false), Atom(AFalse))))
            (Or ((Atom (AVar 0 true), Atom (AVar 1 true)), (Atom (AVar 0 false), Atom(AFalse))))
            (Or ((Atom (AVar 0 true), Atom (AVar 1 true)), (Atom (AVar 0 false), Atom(AFalse)))).
Proof.
  constructor. constructor; constructor; constructor; discriminate.
Qed.

Example sdd_and_eq:
  forall  (v : vtree) (a : sdd),
    sdd_vtree a v ->
    sdd_apply OAnd a a a.
Proof.
  intros. destruct a. induction H.
  - constructor. constructor. Admitted.
(*  - constructor. constructor.
  - constructor. constructor.
  - constructor. apply TwoSatA1B2.
    + assumption.
    + Admitted.*) (*decomposability*)


(* Apply preserves vtree consistency
  forall v sdd1 sdd2 sddRes, sdd_vtree sdd1 v → sdd_vtree sdd2 v → sdd_apply OAnd sdd1 sdd2 sddRes → sdd_vtree sddRes v.
*)

(* Inductive orList : list bool -> bool -> Prop :=
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
Qed.*)

(* Inductive compile *)


Ltac rewAndInvert :=
  match goal with
  | [ H1: _ = ?x, H2: _ = ?x |- _ ] =>
      rewrite <- H2 in H1; inversion H1
  end.

Check sdd_ind.

Section sdd_ind'.
  Variable P : sdd -> Prop.
  Hypothesis Or_case : forall p1 s1 p2 s2,
      P p1 -> P p2 -> P s1 -> P s2 -> P (Or ((p1,s1),(p2,s2))).
  Hypothesis Atom_case : forall a,  P (Atom a).

  Fixpoint sdd_ind' (s:sdd) : P s :=
    match s with
    | Atom a => Atom_case a
    | Or ((p1,s1),(p2,s2)) => Or_case p1 s1 p2 s2
                                      (sdd_ind' p1) (sdd_ind' p2) (sdd_ind' s1) (sdd_ind' s2)
   end.
End sdd_ind'.

Theorem apply_preserves_vtree :
  forall sdd1 sdd2 sddRes v o,
    sdd_vtree sdd1 v →
    sdd_vtree sdd2 v →
    sdd_apply o sdd1 sdd2 sddRes →
    sdd_vtree sddRes v.
Proof.
  induction sdd1 using sdd_ind'; induction sdd2 using sdd_ind'.
  - intros sddRes v o Hsdd1 Hsdd2 Happ.
    inversion Happ. inversion H9.
    + inversion Hsdd1; inversion Hsdd2. apply OrSingle.
      * rewrite <- H43 in H34. inversion H34. rewrite <- H48 in H42. rewrite <- H48.
        apply (IHsdd1_1 sdd2_1 pRes1 lvtree OAnd H33 H42 H22).
      * 

     
      


  - inversion Happ. rewrite <- H in Hsdd1. rewrite <- H1 in Hsdd2.
    inversion Hsdd1. rewrite <- H9 in Hsdd1. rewrite <- H9 in Hsdd2.
    constructor. inversion H2.
    + 


Theorem compile_correct :
  forall (boolExp:boolExpr) (sdd:sdd) (input:varAssign) (result:bool),
    compile boolExp sdd →
    eval_sdd sdd result input →
    eval boolExp result input.

