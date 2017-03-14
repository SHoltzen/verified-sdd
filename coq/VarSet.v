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

Theorem union_comm :
  forall v1 v2 vRes,
    union v1 v2 vRes ->
    union v2 v1 vRes.
Admitted.

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

Inductive disjoint : varSet -> varSet -> Prop :=
| disjoint_empty : forall vs, disjoint Empty vs
| disjoint_var   : forall n rest vs, notMember vs n ->
                                     disjoint rest vs ->
                                     disjoint (Var n rest) vs.

Inductive subset : varSet -> varSet -> Prop :=
| subset_empty : forall vs, subset Empty vs
| subset_var   : forall n rest vs, member vs n ->
                                   subset rest vs ->
                                   subset (Var n rest) vs.

Theorem subsets_disjoint :
  forall v1 v2 va vb,
  subset v1 va ->
  subset v2 vb ->
  disjoint va vb ->
  disjoint v1 v2.
Proof.
  Admitted.
 

Inductive equal : varSet -> varSet -> Prop :=
| equal_ : forall vs1 vs2, subset vs1 vs2 -> subset vs2 vs1 -> equal vs1 vs2.

Theorem union_lvar :
  forall n rest v2 vInt vRes,
  union rest v2 vInt ->
  union (Var n rest) v2 vRes ->
  equal vRes (Var n vInt).
Admitted.

Theorem union_rvar :
  forall n rest v2 vInt vRes,
  union v2 rest vInt ->
  union v2 (Var n rest) vRes ->
  equal vRes (Var n vInt).
Admitted.

Theorem subsets_union :
  forall v1 v2 v3 va vb vc,
    subset v1 va ->
    subset v2 vb ->
    union v1 v2 v3 ->
    union va vb vc ->
    subset v3 vc.
Admitted.

Theorem self_union :
  forall v,
    union v v v.
Admitted.

Theorem union_implies_subset :
  forall a b c,
    union a b c -> subset a c.
Admitted.

Theorem subset_transitivity :
  forall a b c,
    subset a b -> subset b c -> subset a c.
Admitted.

Theorem union_symmetry :
  forall a b c,
    union a b c -> union b a c.
Admitted.

