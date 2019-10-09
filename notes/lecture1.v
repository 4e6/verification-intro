From mathcomp Require Import ssreflect.

Inductive bool : Type :=
| true
| false.

Check true.

(* bool identity *)
Definition idb := fun b : bool => b.

Compute idb true.

(* bool negation *)
Definition negb (b : bool) :=
  match b with
  | true => false
  | false => true
  end.

Compute negb true.

Variable c : bool.

Compute negb c.

(* bool and *)
Definition andb (b c : bool) : bool :=
  match b with
  | true => c
  | false => false
  end.

Compute andb c false.

(* bool or *)
Definition orb (b c : bool) : bool :=
  match b with
  | true => true
  | false => c
  end.

Compute orb c true.

(* naturals *)
Inductive nat : Type :=
| O
| S of nat.

Check O.
Check S O.
Check S (S O).

(* Definition inc (n : nat) : nat := S n.*)
(* definitionally equal *)
Definition inc := S.

Print inc.
Compute inc (S (S O)).

Definition inc2 (n : nat) : nat := S (S n).

Compute inc2 (S (S O)).

Definition pred (n : nat) : nat :=
  match n with
  | S n' => n'
  | O => O
  end.

(*
   pred : nat -> nat
   pred : nat -> option nat
   pred : forall ( n : nat), n <> O -> nat
 *)

Fixpoint addn (n m : nat) : nat :=
  match n with
  | S n' => S (addn n' m)
  | O => m
  end.

Compute addn (S (S O)) (S (S O)).

Fixpoint muln (n m : nat) : nat:=
  match n with
  | S n' => addn m (muln n' m)
  | O => O
  end.

Compute muln (S (S O)) O.
Compute muln (S (S O)) (S (S (S O))).

Definition square (n : nat) : nat := muln n n.

Definition two := S (S O).
Compute square (square (square two)).
(* strategies: compute, cbn, lazy, cbv, hnf *)
Eval hnf in (square (square (square two))).

Inductive False : Prop := .
Print False.
Check (fun f : False => f).

Fail Fixpoint loop (n : nat) : False :=
  loop n.

Fail Check (loop O : False).
