From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Languages.
From regexderiv Require Import Alphabet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module RegexSemantics (X : OSYM).
  Import X.

  (* words + languages *)
  Definition word := Languages.word A.
  Definition language := Languages.language A.

  (* language operators (computable) *)
  Definition void : language := Languages.void (A:=A).
  Definition eps  : language := Languages.eps  (A:=A).
  Definition atom (a : A) : language := Languages.atom (A:=A) a.

  Definition plus  (L K : language) : language := Languages.plus L K.
  Definition prod  (L K : language) : language := Languages.prod L K.
  Definition compl (L : language)   : language := Languages.compl L.

  Definition conc (L K : language) : language := Languages.conc (A:=A) L K.
  Definition star (L : language)   : language := Languages.star (A:=A) L.

  Definition lang_eq (L K : language) : Prop := L =i K.
  Notation "L ≡ K" := (lang_eq L K) (at level 70).

  Lemma lang_eq_refl : forall L, L ≡ L.
  Proof. by move=> L w. Qed.
  Lemma lang_eq_sym : forall L K, L ≡ K -> K ≡ L.
  Proof. by move=> L K HK w; rewrite HK. Qed.
  Lemma lang_eq_trans : forall L K M, L ≡ K -> K ≡ M -> L ≡ M.
  Proof. by move=> L K M HK HM w; rewrite HK HM. Qed.


  Inductive regex : Type :=
  | Empty : regex
  | Eps   : regex
  | Char  : A -> regex
  | Alt   : regex -> regex -> regex
  | Seq   : regex -> regex -> regex
  | Star  : regex -> regex
  | And   : regex -> regex -> regex
  | Neg   : regex -> regex.


  Fixpoint den (r : regex) : pred word :=
    match r with
    | Empty        => void
    | Eps          => eps
    | Char a       => atom a
    | Alt r1 r2    => plus (den r1) (den r2)
    | And r1 r2    => prod (den r1) (den r2)
    | Seq r1 r2    => conc (den r1) (den r2)
    | Star r1      => star (den r1)
    | Neg r1       => compl (den r1)
    end.


  Canonical Structure regex_predType := PredType den.

  Definition re_equiv (r s : regex) : Prop := r =i s.
  Notation "r ≈ s" := (re_equiv r s) (at level 70).

  Lemma re_equiv_refl : forall r, r ≈ r.
  Proof. by move=> r w. Qed.
  Lemma re_equiv_sym : forall r s, r ≈ s -> s ≈ r.
  Proof. by move=> r s H w; rewrite H. Qed.
  Lemma re_equiv_trans : forall r s t, r ≈ s -> s ≈ t -> r ≈ t.
  Proof. by move=> r s t H1 H2 w; rewrite H1 H2. Qed.

  Lemma re_equiv_Alt : forall r1 r2 s1 s2,
      r1 ≈ s1 -> r2 ≈ s2 -> Alt r1 r2 ≈ Alt s1 s2.
  Proof.
    move=> r1 r2 s1 s2 H1 H2 w.
    rewrite /re_equiv /= /plus.
    exact: (congr2 orb (H1 w) (H2 w)).
  Qed.

  Lemma re_equiv_And : forall r1 r2 s1 s2,
      r1 ≈ s1 -> r2 ≈ s2 -> And r1 r2 ≈ And s1 s2.
  Proof.
    move=> r1 r2 s1 s2 H1 H2 w.
    rewrite /re_equiv /= /prod.
    exact: (congr2 andb (H1 w) (H2 w)).
  Qed.

  Lemma re_equiv_Neg : forall r s, r ≈ s -> Neg r ≈ Neg s.
  Proof.
    move=> r s H w.
    rewrite /re_equiv /= /compl.
    exact: (congr1 negb (H w)).
  Qed.

  Lemma re_equiv_Seq : forall r1 r2 s1 s2,
      r1 ≈ s1 -> r2 ≈ s2 -> Seq r1 r2 ≈ Seq s1 s2.
  Proof.
    move=> r1 r2 s1 s2 H1 H2 w.
    exact: (Languages.conc_ext (A:=A) H1 H2 w).
  Qed.

  Lemma re_equiv_Star : forall r s, r ≈ s -> Star r ≈ Star s.
  Proof.
    move=> r s H w.
    exact: (Languages.star_ext (A:=A) H w).
  Qed.

End RegexSemantics.
