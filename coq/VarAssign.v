Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.


Inductive varAssign : Type :=
| Empty : varAssign
| Var   : nat -> bool -> varAssign -> varAssign.

Fixpoint lookup (va:varAssign) (n:nat) : option bool :=
match va with
| Empty        => None
| Var m b rest => if (beq_nat n m) then Some b else lookup rest n
end.

Inductive assigns : varAssign -> nat -> bool -> Prop :=
| assigns_var  : forall n b rest, assigns (Var n b rest) n b
| assigns_rest : forall n1 n2 b1 b2 rest, not (n1 = n2) ->
                                          assigns rest n1 b1 ->
                                          assigns (Var n2 b2 rest) n1 b1.



