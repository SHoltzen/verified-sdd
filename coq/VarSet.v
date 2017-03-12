Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.


Inductive varSet : Type :=
| Empty : varSet
| Var   : nat -> varSet -> varSet.

Fixpoint member_ (vs: varSet) (n:nat) : bool :=
match vs with
| Empty        => false
| Var m rest => if (beq_nat n m) then true else member_ rest n
end.

Inductive member : varSet -> nat -> Prop :=
| member_var : forall n rest,  member (Var n rest) n
| member_rest : forall n1 n2 rest, not (n1 = n2) ->
                                   member rest n1 ->
                                   member (Var n2 rest) n2.

Inductive notMember : varSet -> nat -> Prop :=
| notMember_empty : forall n, notMember Empty n
| notMember_var   : forall n n1 rest, not (n = n1) ->
                                      notMember rest n ->
                                      notMember (Var n1 rest) n.

Fixpoint add_ (vs : varSet) (n: nat) : varSet :=
  if (member_ vs n) then
    vs
  else
    (Var n vs).

Inductive add : varSet -> nat -> varSet -> Prop :=
| IsMember : forall n vs, member vs n -> add vs n vs
| IsNotMember : forall n vs, notMember vs n -> add vs n (Var n vs).

Inductive unique : varSet -> Prop :=
| unique_empty : unique Empty
| unique_var   : forall n rest, notMember rest n ->
                                unique rest ->
                                unique (Var n rest).

Fixpoint union_ (vs1 vs2: varSet) : varSet :=
match vs1 with
| Empty      => vs2
| Var n rest => union_ rest (add_ vs2 n)
end.

Inductive union : varSet -> varSet -> varSet -> Prop :=
| union_empty : forall vs, union Empty vs vs
| union_var   : forall n rest vs vsInt vsRes, add vs n vsInt ->
                                              union rest vsInt vsRes ->
                                              union (Var n rest) vs vsRes.

Theorem union_unique :
  forall vs1 vs2 vsRes, unique vs1 ->
                        unique vs2 ->
                        union vs1 vs2 vsRes -> 
                        unique vsRes.
Proof.
  intros vs1 vs2 vsRes Hvs1 Hvs2 Hunion.
  induction Hunion.
  - assumption.
  - apply IHHunion.
    + inversion Hvs1. subst. assumption.
    + inversion H; subst.
      * assumption.
      * constructor. assumption. assumption.
Qed. 
