Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Bool.Bool.

Require Import VarAssign.

Inductive boolExpr : Type :=
| Atom : nat -> bool -> boolExpr
| And  : boolExpr -> boolExpr -> boolExpr
| Or   : boolExpr -> boolExpr -> boolExpr.

Definition optional_and (a b:option bool) : option bool :=
match a with
| None => None
| Some ba => (match b with
             | None => None
             | Some bb => Some (ba && bb) end)
end.

Definition optional_or (a b:option bool) : option bool :=
match a with
| None => None
| Some ba => (match b with
             | None => None
             | Some bb => Some (ba || bb)
             end)
end.

Definition optional_not (a:option bool) : option bool :=
match a with
| None => None
| Some ba => Some (negb ba)
end.


Fixpoint eval_ (be:boolExpr) (va:varAssign) : option bool :=
match be with
| Atom n same => let value := lookup va n in
                 if same then value else (optional_not value)
| And e1 e2   => optional_and (eval_ e1 va) (eval_ e2 va)
| Or e1 e2    => optional_or (eval_ e1 va) (eval_ e2 va)
end.

Inductive eval : boolExpr -> bool -> varAssign -> Prop :=
| eval_atom_same : forall n va res, (assigns va n res) ->
                                    eval (Atom n true) res va
| eval_atom_neg  : forall n va res, (assigns va n res) ->
                                    eval (Atom n false) (negb res) va
| eval_and       : forall e1 res1 e2 res2 va, (eval e1 res1 va) -> (eval e2 res2 va) ->
                                              eval (And e1 e2) (andb res1 res2) va
| eval_or        : forall e1 res1 e2 res2 va, (eval e1 res1 va) -> (eval e2 res2 va) ->
                                              eval (Or e1 e2) (orb res1 res2) va.


Inductive boolExpr' : Type :=
| Atom' : nat -> boolExpr'
| Not'  : boolExpr' -> boolExpr'
| And'  : boolExpr' -> boolExpr' -> boolExpr'
| Or'  : boolExpr' -> boolExpr' -> boolExpr'.

Fixpoint eval_' (be:boolExpr') (va:varAssign) : option bool :=
match be with
| Atom' n     => lookup va n
| Not' e      => optional_not (eval_' e va)
| And' e1 e2  => optional_and (eval_' e1 va) (eval_' e2 va)
| Or' e1 e2  => optional_or (eval_' e1 va) (eval_' e2 va)
end.

Inductive eval' : boolExpr' -> bool -> varAssign -> Prop :=
| eval'_atom : forall n va res, (assigns va n res) -> eval' (Atom' n) res va
| eval'_not  : forall b' res va, eval' b' res va -> eval' (Not' b') (negb res) va
| eval'_and  : forall b1' res1 b2' res2 va, eval' b1' res1 va ->
                                           eval' b2' res2 va ->
                                           eval' (And' b1' b2') (andb res1 res2) va
| eval'_or   : forall b1' res1 b2' res2 va, eval' b1' res1 va ->
                                           eval' b2' res2 va ->
                                           eval' (Or' b1' b2') (orb res1 res2) va.


Fixpoint b_b'_equivalent (be:boolExpr) (be':boolExpr') : bool :=
match be with
| Atom n same => if same
                 then (match be' with
                       | Atom' n => true
                       | _ => false
                      end)
                 else (match be' with
                       | Not' (Atom' n) => true
                       | _ => false
                       end)
| And e1 e2   => (match be' with
                  | And' e1' e2' => (b_b'_equivalent e1 e1') && (b_b'_equivalent e2 e2')
                  | _ => false
                  end)
| Or e1 e2    => (match be' with
                  | Or' e1' e2' => (b_b'_equivalent e1 e1') && (b_b'_equivalent e2 e2')
                  | _ => false
                  end)
end.

Inductive eq_b_b' : boolExpr -> boolExpr' -> Prop :=
| eq_atom_atom' : forall n, eq_b_b' (Atom n true) (Atom' n)
| eq_natom_not' : forall n, eq_b_b' (Atom n false) (Not' (Atom' n))
| eq_and_and'   : forall b1 b1' b2 b2', eq_b_b' b1 b1' -> eq_b_b' b2 b2' ->
                                        eq_b_b' (And b1 b2) (And' b1' b2')
| eq_or_or'     : forall b1 b1' b2 b2', eq_b_b' b1 b1' -> eq_b_b' b2 b2' ->
                                        eq_b_b' (Or b1 b2) (Or' b1' b2').


Compute (b_b'_equivalent (And (Atom 1 true) (Atom 1 false)) (And' (Atom' 1) (Not' (Atom' 1)))).

Lemma same_assigns :
  forall res res' va n, assigns va n res -> assigns va n res' -> res = res'.
Proof.
  intros. induction va.
  - inversion H.
  - inversion H; inversion H0.
    + rewrite H5 in H10. assumption.
    + unfold not in H11. symmetry in H1. apply H11 in H1. inversion H1.
    + unfold not in H6. symmetry in H8. apply H6 in H8. inversion H8.
    + apply IHva. assumption. assumption.
Qed.

Lemma eqb_and :
  forall a b c d, eqb a c = true -> eqb b d = true -> eqb (a && b) (c && d) = true.
intros. destruct a; destruct b; destruct c; destruct d; simpl;
          try reflexivity; try inversion H; try inversion H0.
Qed.

Lemma eqb_or :
  forall a b c d, eqb a c = true -> eqb b d = true -> eqb (a || b) (c || d) = true.
intros. destruct a; destruct b; destruct c; destruct d; simpl;
          try reflexivity; try inversion H; try inversion H0.
Qed.

Theorem eq_b_b'_sameResult :
  forall b res b' res' va, eq_b_b' b b' -> eval b res va -> eval' b' res' va ->
                           (eqb res res') = true.
Proof.
  intro. intro. intro. intro. intro. intro. generalize res res'.
  induction H; intros.
  - inversion H. inversion H0. apply (same_assigns res0 res'0 va n) in H2.
    + rewrite H2. apply eqb_reflx.
    + assumption.
  - inversion H. inversion H0. inversion H6. apply (same_assigns res1 res2 va n) in H2.
    + rewrite H2. destruct res2; reflexivity.
    + assumption.
  - inversion H1. inversion H2.
     apply (IHeq_b_b'1 res1 res3) in H5. apply (IHeq_b_b'2 res2 res4) in H8.
     apply eqb_and. assumption. assumption. assumption. assumption.
  - inversion H1. inversion H2.
     apply (IHeq_b_b'1 res1 res3) in H5. apply (IHeq_b_b'2 res2 res4) in H8.
     apply eqb_or. assumption. assumption. assumption. assumption.
Qed.


(*-----------------------------------------*)

Definition eqOptBool (a b:option bool) : bool :=
match a with
| None    => (match b with
              | None => true
              | Some _ => false
              end)
| Some ba => (match b with
              | None => false
              | Some bb => (eqb ba bb)
              end)
end.

(*
Lemma eq_atom_atom' :
  forall n n0 b, b_b'_equivalent (Atom n b) (Atom' n0) = true -> ((n = n0) /\ (b = true)).
Admitted.
*)
Lemma eq_atom_false_not' :
  forall n b', b_b'_equivalent (Atom n false) (Not' b') = true ->
                    (b' = (Atom' n)).
Admitted.

Lemma neq_atom_not' :
  forall n n0, b_b'_equivalent (Atom n true) (Not' n0) = false.
Admitted.

Lemma neq_atom_and' :
  forall n b b'1 b'2, b_b'_equivalent (Atom n b) (And' b'1 b'2) = false.
Admitted.

Lemma neq_atom_or' :
  forall n b b'1 b'2, b_b'_equivalent (Atom n b) (Or' b'1 b'2) = false.
Admitted.


Lemma neq_and_atom' :
  forall n b1 b2, b_b'_equivalent (And b1 b2) (Atom' n) = false.
Admitted.

Lemma neq_and_not' :
  forall b1 b2 b', b_b'_equivalent (And b1 b2) (Not' b') = false.
Admitted.
(*
Lemma eq_and_and' :
  forall b1 b2 b'1 b'2, b_b'_equivalent b1 b'1 = true ->
                        b_b'_equivalent b2 b'2 = true ->
                        b_b'_equivalent (And b1 b2) (And' b'1 b'2) = true.
Admitted.
*)
Lemma neq_and_or' :
  forall b1 b2 b'1 b'2, b_b'_equivalent (And b1 b2) (Or' b'1 b'2) = false.
Admitted.


Lemma eqOptBool_lookup :
  forall n va, eqOptBool (lookup va n) (lookup va n) = true.
Proof.
  intros. destruct (lookup va n); simpl.
  - apply eqb_reflx.
  - reflexivity.
Qed.

(*
Theorem b_b'_equivalent_sameResult :
  forall b b' va, (b_b'_equivalent b b') = true ->
                  eqOptBool (eval_ b va) (eval_' b' va) = true.
Proof.
  induction b; induction b'; intros.
  * apply eq_atom_atom' in H. inversion H. rewrite H0. rewrite H1. simpl.
    apply (eqOptBool_lookup n0 va).
  * destruct b.
    + rewrite neq_atom_not' in H. inversion H.
    + apply eq_atom_false_not' in H. rewrite H. simpl. destruct (lookup va n); simpl.
      { destruct b; simpl; reflexivity. }
      { reflexivity. }
  * rewrite neq_atom_and' in H. inversion H.
  * rewrite neq_atom_or'  in H. inversion H.
  * rewrite neq_and_atom' in H. inversion H.
  * rewrite neq_and_not'  in H. inversion H.
  * Admitted.



*)

