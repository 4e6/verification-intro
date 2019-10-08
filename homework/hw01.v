From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

(*** Exercise 1 *)

(** 1a. Define [orb_my] function implementing boolean disjunction *)

Definition orb_my (b c : bool) : bool :=
  match b with
  | true => true
  | false => c
  end.

Compute orb_my true false.
Compute orb_my false true.
Compute orb_my false false.

Print orb_my.

(** 1b. Figure out the implementation of [orb] function in the standard library
        using Coq's interactive query mechanism *)

Print orb.

(** 1c. What's the difference between the standard implementation and
        the following one? *)

Definition orb_table (b c : bool) : bool :=
  match b, c with
  | true,  true  => true
  | true,  false => true
  | false, true  => true
  | false, false => false
  end.

(** Note: the above translates into nested pattern-matching, check this *)

Print orb_table.

(** 1d. Define [addb_my] function implementing exclusive boolean disjunction.
        {The name [addb] comes from the fact this operation behaves like addition modulo 2}
        If you are already familiar with proofs in Coq, think of a prover friendly
        definition, if you are not -- experiment with how different implementations
        behave under symbolic execution. *)

Definition addb_my (b1 b2 : bool) : bool :=
  match b1 with
  | false => b2
  | true => ~~ b2
  end.

Variable p : bool.

Compute addb_my true p.

(*** Exercise 2 *)

(** 2a. Implement power function of two arguments [x] and [n],
        raising [x] to the power of [n] *)

Fixpoint power (x n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => x
  | n0.+1 => power (x * x) n0
  end.

Compute power 3 0.
Compute power 3 1.
Compute power 3 2.

(*** Exercise 3 *)

(** 3a. Implement division on unary natural numbers *)

Fixpoint divn_my (n m : nat) : nat :=
  match n, m with
  | 0, _ => 0
  | _, 0 => 0
  | n0.+1, m0.+1 => if n0 >= m0 then 1 + divn_my (n0 - m0) m else 0
  end.

(* Unit tests: *)
Compute divn_my 0 0.  (* = 0 *)
Compute divn_my 1 0.  (* = 0 *)
Compute divn_my 0 3.  (* = 0 *)
Compute divn_my 1 3.  (* = 0 *)
Compute divn_my 2 3.  (* = 0 *)
Compute divn_my 3 3.  (* = 1 *)
Compute divn_my 8 3.  (* = 2 *)
Compute divn_my 42 1. (* = 42 *)
Compute divn_my 42 2. (* = 21 *)
Compute divn_my 42 3. (* = 14 *)
Compute divn_my 42 4. (* = 10 *)


(** 3b. Provide several unit tests using [Compute] vernacular command *)


(*** Exercise 4 *)

(** Use the [applyn] function defined during the lecture
    (or better its Mathcomp sibling called [iter]) define

    4a. addition on natural numbers

    4b. multiplication on natural numbers

    Important: don't use recursion, i.e. no [Fixpoint] / [fix] should be in your solution.
*)

(** Here is out definition of [applyn]: *)
Definition applyn (f : nat -> nat) :=
  fix rec (n : nat) (x : nat) :=
    if n is n'.+1 then rec n' (f x)
    else x.
