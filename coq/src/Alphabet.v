From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type OSYM.
  Parameter A : eqType.

  Parameter cmpA : A -> A -> comparison.

  Axiom cmpA_refl : forall a, cmpA a a = Eq.
  Axiom cmpA_eq_axiom : forall a b, reflect (a = b)
    (if cmpA a b is Eq then true else false).
  Axiom cmpA_trans : forall a b c (x : comparison),
      cmpA a b = x -> cmpA b c = x -> cmpA a c = x.
  Axiom cmpA_neg : forall a b, cmpA b a = CompOpp (cmpA a b).

  Definition leA : rel A :=
    fun a b => if cmpA a b is Gt then false else true.

  Lemma leA_refl : reflexive leA.
  Proof. by move=> a; rewrite /leA cmpA_refl. Qed.

  Lemma leA_total : total leA.
  Proof.
    move=> a b; rewrite /leA cmpA_neg; by case: (cmpA b a).
  Qed.
End OSYM.
