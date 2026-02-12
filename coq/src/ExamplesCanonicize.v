From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import Languages.
From regexderiv Require Import RegexSemantics.
From regexderiv Require Import Nullable.
From regexderiv Require Import Canonicalization.   

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BoolSym <: OSYM.
  Definition A : eqType := Datatypes_bool__canonical__eqtype_Equality.

  Definition cmpA (x y : bool) : comparison :=
    match x, y with
    | false, false => Eq
    | false, true  => Lt
    | true,  false => Gt
    | true,  true  => Eq
    end.

  Lemma cmpA_refl : forall a, cmpA a a = Eq.
  Proof. by case. Qed.

  Lemma cmpA_eq_axiom : forall a b, reflect (a = b)
    (if cmpA a b is Eq then true else false).
  Proof.
    by case; case; constructor.
  Qed.

  Lemma cmpA_trans : forall a b c (x : comparison),
      cmpA a b = x -> cmpA b c = x -> cmpA a c = x.
  Proof.
    by case; case; case; case; simpl; try congruence.
  Qed.

  Lemma cmpA_neg : forall a b, cmpA b a = CompOpp (cmpA a b).
  Proof. by case; case. Qed.

  Definition leA : rel A :=
    fun a b => if cmpA a b is Gt then false else true.

  Lemma leA_refl : reflexive leA.
  Proof. by move=> a; rewrite /leA cmpA_refl. Qed.

  Lemma leA_total : total leA.
  Proof.
    move=> a b; rewrite /leA cmpA_neg; by case: (cmpA b a).
  Qed.
End BoolSym.

Module C := Canonicalization BoolSym.
Import C.

(* Shorthand symbols *)
Definition a : regex := Char false.
Definition b : regex := Char true.

(* Example 1: (a + ∅) + (b + a)  vs  (a + b) *)
Definition r1 : regex := Alt (Alt a Empty) (Alt b a).
Definition s1 : regex := Alt a b.

Compute r1.
Compute (canonize r1).
Compute s1.

Compute (same_syntax r1 s1).
Compute (same_after_canon r1 s1).
Compute (different_but_canon_same r1 s1).

(* Example 2: idempotence: a + a  vs a *)
Definition r2 : regex := Alt a a.
Definition s2 : regex := a.

Compute (canonize r2).
Compute (same_after_canon r2 s2).
Compute (different_but_canon_same r2 s2).

(* Example 3: concat identity: ε·a  vs a *)
Definition r3 : regex := Seq Eps a.
Definition s3 : regex := a.

Compute (canonize r3).
Compute (same_after_canon r3 s3).
Compute (different_but_canon_same r3 s3).
