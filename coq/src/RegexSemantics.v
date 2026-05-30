From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import Languages.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module RegexSemantics (X : SYM).
  Import X.

  (* Syntax side of semantic interpretation: the regular expressions over A. *)
  Inductive regex : Type :=
  | Empty : regex
  | Eps   : regex
  | Char  : A -> regex
  | Alt   : regex -> regex -> regex
  | Seq   : regex -> regex -> regex
  | Star  : regex -> regex
  | And   : regex -> regex -> regex
  | Neg   : regex -> regex.

  (* Predicate checking that a regex is restricted, i.e. contains no And or Neg constructors. *)
  Inductive restricted_regex : regex -> Prop :=
  | RestrictedEmpty : restricted_regex Empty
  | RestrictedEps   : restricted_regex Eps
  | RestrictedChar  : forall a, restricted_regex (Char a)
  | RestrictedAlt   : forall r s,
      restricted_regex r -> restricted_regex s -> restricted_regex (Alt r s)
  | RestrictedSeq   : forall r s,
      restricted_regex r -> restricted_regex s -> restricted_regex (Seq r s)
  | RestrictedStar  : forall r,
      restricted_regex r -> restricted_regex (Star r).

  (* Local names for words and languages over the current alphabet A. *)
  Definition word := Languages.word A.
  Definition language := Languages.language A.

  (* Language-side names for regex semantic interpretation. *)
  Definition void : language := Languages.void (A:=A).
  Definition eps  : language := Languages.eps  (A:=A).
  Definition atom (a : A) : language := Languages.atom (A:=A) a.
  Definition plus  (L K : language) : language := Languages.plus L K.
  Definition conc (L K : language) : language := Languages.conc (A:=A) L K.
  Definition star (L : language)   : language := Languages.star (A:=A) L.
  Definition prod  (L K : language) : language := Languages.prod L K.
  Definition compl (L : language)   : language := Languages.compl L.

  (* Semantic interpretation: maps each regex to the language it denotes. *)
  Fixpoint den (r : regex) : pred word :=
    match r with
    | Empty        => void
    | Eps          => eps
    | Char a       => atom a
    | Alt r1 r2    => plus (den r1) (den r2)
    | Seq r1 r2    => conc (den r1) (den r2)
    | Star r1      => star (den r1)
    | And r1 r2    => prod (den r1) (den r2)
    | Neg r1       => compl (den r1)
    end.


  (* Semantic equivalence. *)

  (* Lets Rocq read a regex as its denoted language when using membership and =i. *)
  Canonical Structure regex_predType := PredType den.

  (* Extensional equality of languages. *)
  Definition lang_eq (L K : language) : Prop := L =i K.
  Notation "L ≡ K" := (lang_eq L K) (at level 70).

  (* Language equality is an equivalence relation. *)
  Lemma lang_eq_refl : forall L, L ≡ L.
  Proof. by move=> L w. Qed.
  Lemma lang_eq_sym : forall L K, L ≡ K -> K ≡ L.
  Proof. by move=> L K HK w; rewrite HK. Qed.
  Lemma lang_eq_trans : forall L K M, L ≡ K -> K ≡ M -> L ≡ M.
  Proof. by move=> L K M HK HM w; rewrite HK HM. Qed.

  (* Two regexes are semantically equivalent when their denoted languages are equal. *)
  Definition re_equiv (r s : regex) : Prop := r =i s.
  Definition semantic_equiv := re_equiv.
  Notation "r ≈ s" := (re_equiv r s) (at level 70).

  (* Semantic equivalence is an equivalence relation. *)
  Lemma re_equiv_refl : forall r, r ≈ r.
  Proof. by move=> r w. Qed.
  Lemma re_equiv_sym : forall r s, r ≈ s -> s ≈ r.
  Proof. by move=> r s H w; rewrite H. Qed.
  Lemma re_equiv_trans : forall r s t, r ≈ s -> s ≈ t -> r ≈ t.
  Proof. by move=> r s t H1 H2 w; rewrite H1 H2. Qed.

  (* Semantic equivalence is preserved by regex constructors. *)
  Lemma re_equiv_Alt : forall r1 r2 s1 s2,
      r1 ≈ s1 -> r2 ≈ s2 -> Alt r1 r2 ≈ Alt s1 s2.
  Proof.
    move=> r1 r2 s1 s2 H1 H2 w.
    rewrite /re_equiv /= /plus.
    exact: (congr2 orb (H1 w) (H2 w)).
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

End RegexSemantics.
