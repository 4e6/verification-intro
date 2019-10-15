From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Some basic functions *)

Definition const {A B} (a : A) := fun _ : B => a.

Definition flip {A B C} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Arguments const {A B} a _ /.
Arguments flip {A B C} f b a /.


(* move to logic_exercises *)
Section IntLogic.

Variables A B C D : Prop.

Lemma axiomK :
  A -> B -> A.
Proof.
  exact: const.
Qed.


(* note: flip is more general *)
Lemma contraposition :
  (A -> ~ B) -> (B -> ~ A).
Proof.
  exact: flip.
Qed.


Lemma p_imp_np_iff_np : (A -> ~A)  <->  ~A.
Proof.
  split.
  - move=> a_i_na a.
    exact: (a_i_na a a).
  - exact: const.
Qed.


(* We can generalize the previous lemma into *)
Lemma p_p_q_iff_p_q : (A -> A -> B)  <->  (A -> B).
Proof.
  split.
  - move=> a_i_a_i_b a.
    exact: (a_i_a_i_b a a).
  - move=> a_i_b a.
    exact a_i_b.
Qed.


Lemma p_is_not_equal_not_p :
  ~ (A <-> ~ A).
Proof.
  case.
  move=> a_na na_a.
  apply: (a_na).
  - apply: (na_a). move=> a. by apply: a_na.
  - apply: (na_a). move=> a. by apply: a_na.
Qed.


Lemma not_not_lem :
  ~ ~ (A \/ ~ A).
Proof.
  move=> H.
  apply: (H).
  right.
  move=> a.
  apply: H.
    by left.
Qed.


Lemma constructiveDNE :
  ~ ~ ~ A  ->  ~ A.
Proof.
  move=> H.
  move=> a.
  apply: H.
  move=> H.
    by apply: H.
Qed.

End IntLogic.


(* Boolean logic (decidable fragment enjoys classical laws) *)

Section BooleanLogic.

Lemma LEM_decidable a :
  a || ~~ a.
Proof.
    by case: a.
Qed.

Lemma disj_implb a b :
  a || (a ==> b).
Proof.
    by case: a.
Qed.

Lemma iff_is_if_and_only_if a b :
  (a ==> b) && (b ==> a) = (a == b).
Proof.
  case: a.
    - by case: b.
    - by case: b.
Qed.


Lemma implb_trans : transitive implb.
Proof.
  rewrite /transitive.
  move=> a b c.
  case: a.
    by case: b.
    by case: b.
Qed.


Lemma triple_compb (f : bool -> bool) :
  f \o f \o f =1 f.
Proof.
  case=> /=.
  - case et: (f true).
      by rewrite ?et.
  - case ef: (f false).
      by rewrite ?ef.
  - by rewrite ?ef.
  - case ef: (f false).
  - case et: (f true).
      by [].
  - by [].
  - by rewrite ?ef.
Qed.

(* negb \o odd means "even" *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Admitted.

End BooleanLogic.


(* some properties of functional composition *)

Section eq_comp.
Variables A B C D : Type.

Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Admitted.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Admitted.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Admitted.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof.
Admitted.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof.
Admitted.

End eq_comp.
