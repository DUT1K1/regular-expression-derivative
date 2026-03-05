From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import ssralg ssrnum rat.

From regexderiv Require Import Languages.
From regexderiv Require Import Alphabet.
From regexderiv Require Import RegexSemantics.
From regexderiv Require Import Canonicalization.
From regexderiv Require Import Derivatives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.


Module Similarity (X : OSYM).
  Import X.

  Module D  := Derivatives X.
  Module RS := D.N.RS.
  Module C  := Canonicalization X.

  (* ============================================================ *)
  (* Common numeric layer (values in [0,1])                       *)
  (* ============================================================ *)

  Definition simval := rat.

  (* min T-norm *)
  Definition smin (x y : simval) : simval := if x <= y then x else y.

  Lemma smin_lel (x y : simval) : smin x y <= x.
  Proof.
    rewrite /smin; case: ifP=> hxy; first exact: order.Order.POrderTheory.lexx.
    have /orP [hxy'|hyx] := order.Order.TotalTheory.le_total x y.
    - by move: hxy; rewrite hxy'.
    - exact: hyx.
  Qed.

  Lemma smin_ler (x y : simval) : smin x y <= y.
  Proof.
    rewrite /smin; case: ifP=> hxy.
    - exact: hxy.
    - exact: order.Order.POrderTheory.lexx.
  Qed.

  Lemma le_smin (z x y : simval) : z <= x -> z <= y -> z <= smin x y.
  Proof.
    rewrite /smin; case: ifP=> _ hx hy; first exact: hx.
    exact: hy.
  Qed.

  Lemma sminxx (x : simval) : smin x x = x.
  Proof. by rewrite /smin order.Order.POrderTheory.lexx. Qed.

  Lemma smin_shuffle (a b c d : simval) :
    smin (smin a b) (smin c d) <= smin (smin a c) (smin b d).
  Proof.
    apply: le_smin.
    - apply: le_smin.
      + exact: (order.Order.POrderTheory.le_trans (smin_lel _ _) (smin_lel _ _)).
      + exact: (order.Order.POrderTheory.le_trans (smin_ler _ _) (smin_lel _ _)).
    - apply: le_smin.
      + exact: (order.Order.POrderTheory.le_trans (smin_lel _ _) (smin_ler _ _)).
      + exact: (order.Order.POrderTheory.le_trans (smin_ler _ _) (smin_ler _ _)).
  Qed.

  (* ============================================================ *)
  (* fuzzy relation, cut, proximity, similarity                   *)
  (* ============================================================ *)

  Definition in01 (x : simval) : bool := (0 <= x) && (x <= 1).

  (* 0 < cut <= 1 *)
  Definition cut_value (mu : simval) : Prop := (0 < mu) /\ (mu <= 1).

  Section FuzzyRelationLayer.
    Variable S : Type.

    Definition fuzzy_rel := S -> S -> simval.

    (* R_mu := {(s1,s2) | R(s1,s2) >= mu} *)
    Definition mu_cut (mu : simval) (R : fuzzy_rel) : rel S :=
      fun s1 s2 => mu <= R s1 s2.

    (* proximity = reflexive + symmetric *)
    Record is_proximity (R : fuzzy_rel) : Prop := {
      prox_refl : forall s, R s s = 1;
      prox_sym  : forall s1 s2, R s1 s2 = R s2 s1
    }.

    (* similarity = proximity + transitive wrt min T-norm *)
    Record is_similarity (R : fuzzy_rel) : Prop := {
      sim_prox : is_proximity R;
      sim_trans : forall s1 s2 s,
        smin (R s1 s) (R s s2) <= R s1 s2
    }.
  End FuzzyRelationLayer.


  Definition word := RS.word.
  Definition language := RS.language.
  Definition regex := RS.regex.

  (* ============================================================ *)
  (* Base assumptions: a similarity R on symbols A×A              *)
  (* ============================================================ *)

  Section BaseSymbolSimilarity.

    Variable R : A -> A -> simval.

    Hypothesis R_range : forall a b, (0 <= R a b) && (R a b <= 1).
    Hypothesis R_refl  : forall a, R a a = 1.
    Hypothesis R_sym   : forall a b, R a b = R b a.
    Hypothesis R_trans : forall a b c, smin (R a b) (R b c) <= R a c.

    (* ============================================================ *)
    (* Definition 3.1 (R^ω): similarity on words                    *)
    (* ============================================================ *)

    Fixpoint Rw (w1 w2 : word) : simval :=
      match w1, w2 with
      | [::], [::] => 1
      | [::], _    => 0
      | _   , [::] => 0
      | a1 :: t1, a2 :: t2 =>
          smin (R a1 a2) (Rw t1 t2)
      end.

    (* Helper: Rw stays in [0,1]. *)
    Lemma Rw_range : forall w1 w2, (0 <= Rw w1 w2) && (Rw w1 w2 <= 1).
    Proof.
      elim=> [|a1 t1 IH] [|a2 t2] //=.
      - have /andP [H01a H01b] := R_range a1 a2.
        have /andP [H01t _] := IH t2.
        apply/andP; split.
        + apply: le_smin; first exact: H01a.
          exact: H01t.
        + exact: (order.Order.POrderTheory.le_trans (smin_lel _ _) H01b).
    Qed.

    (* ============================================================ *)
    (* Lemma 3.1: R^ω is reflexive, symmetric, transitive           *)
    (* ============================================================ *)

    Lemma Rw_refl : forall w, Rw w w = 1.
    Proof.
      elim=> [|a w IH] //=.
      by rewrite R_refl IH sminxx.
    Qed.

    Lemma Rw_sym : forall w1 w2, Rw w1 w2 = Rw w2 w1.
    Proof.
      elim=> [|a1 t1 IH] [|a2 t2] //=.
      by rewrite R_sym IH.
    Qed.

    Lemma Rw_trans : forall w1 w2 w,
      smin (Rw w1 w) (Rw w w2) <= Rw w1 w2.
    Proof.
      elim=> [|a1 t1 IH] [|a2 t2] w //=.
      - case: w=> [|a w] //=; by rewrite ler01.
      - case: w=> [|a w].
        + by rewrite /=; exact: smin_ler.
        + by rewrite /=; exact: smin_lel.
      - case: w=> [|a w].
        + by rewrite /=; exact: smin_lel.
        + by rewrite /=; exact: smin_ler.
      - case: w=> [|a t].
        + have /andP [H0a _] := R_range a1 a2.
          have /andP [H0t _] := Rw_range t1 t2.
          by rewrite /=; apply: le_smin.
        + have Hhead : smin (R a1 a) (R a a2) <= R a1 a2 := R_trans a1 a a2.
          have Htail : smin (Rw t1 t) (Rw t t2) <= Rw t1 t2 := IH t2 t.
          have Hsh :
            smin (smin (R a1 a) (Rw t1 t)) (smin (R a a2) (Rw t t2))
              <= smin (smin (R a1 a) (R a a2)) (smin (Rw t1 t) (Rw t t2)).
          { exact: smin_shuffle. }
          apply: (order.Order.POrderTheory.le_trans Hsh).
          apply: le_smin.
          * exact: (order.Order.POrderTheory.le_trans (smin_lel _ _) Hhead).
          * exact: (order.Order.POrderTheory.le_trans (smin_ler _ _) Htail).
    Qed.

    Record is_similarity_on_words : Prop := {
      Rw_is_reflexive : forall w, Rw w w = 1;
      Rw_is_symmetric : forall w1 w2, Rw w1 w2 = Rw w2 w1;
      Rw_is_transitive : forall w1 w2 w,
        smin (Rw w1 w) (Rw w w2) <= Rw w1 w2
    }.

    Lemma Rw_is_similarity : is_similarity_on_words.
    Proof.
      split; [exact: Rw_refl | exact: Rw_sym | exact: Rw_trans].
    Qed.

    (* ============================================================ *)
    (* Definition 3.2 (R^L): similarity on languages                *)
    (* ============================================================ *)

    Parameter SupL : language -> (word -> simval) -> simval.
    Parameter InfL : language -> (word -> simval) -> simval.

    Definition RL (L1 L2 : language) : simval :=
      smin (InfL L1 (fun w1 => SupL L2 (fun w2 => Rw w1 w2)))
           (InfL L2 (fun w2 => SupL L1 (fun w1 => Rw w1 w2))).

    (* Lemma 3.2 (TODO): inf/sup ???? *)
    Lemma RL_is_similarity :
      (forall L, RL L L = 1) /\
      (forall L1 L2, RL L1 L2 = RL L2 L1) /\
      (forall L1 L2 L3, smin (RL L1 L2) (RL L2 L3) <= RL L1 L3).
    Admitted.

    (* ============================================================ *)
    (* Definition 3.3 (R^r): syntactic similarity on regex          *)
    (* ============================================================ *)

    Fixpoint eq_regex (r s : regex) : bool :=
      match r, s with
      | RS.Empty, RS.Empty => true
      | RS.Eps, RS.Eps => true
      | RS.Char a, RS.Char b => a == b
      | RS.Alt r1 r2, RS.Alt s1 s2 => eq_regex r1 s1 && eq_regex r2 s2
      | RS.And r1 r2, RS.And s1 s2 => eq_regex r1 s1 && eq_regex r2 s2
      | RS.Seq r1 r2, RS.Seq s1 s2 => eq_regex r1 s1 && eq_regex r2 s2
      | RS.Star r1, RS.Star s1 => eq_regex r1 s1
      | RS.Neg r1, RS.Neg s1 => eq_regex r1 s1
      | _, _ => false
      end.

    Fixpoint rs_to_c_regex (r : RS.regex) : C.RS.regex :=
      match r with
      | RS.Empty => C.RS.Empty
      | RS.Eps => C.RS.Eps
      | RS.Char a => C.RS.Char a
      | RS.Alt r1 r2 => C.RS.Alt (rs_to_c_regex r1) (rs_to_c_regex r2)
      | RS.And r1 r2 => C.RS.And (rs_to_c_regex r1) (rs_to_c_regex r2)
      | RS.Seq r1 r2 => C.RS.Seq (rs_to_c_regex r1) (rs_to_c_regex r2)
      | RS.Star r1 => C.RS.Star (rs_to_c_regex r1)
      | RS.Neg r1 => C.RS.Neg (rs_to_c_regex r1)
      end.

    Record regex_similarity : Type := {
      Rr : regex -> regex -> simval;

      Rr_lang_eq_1 : forall r1 r2, RS.re_equiv r1 r2 -> Rr r1 r2 = 1;

      Rr_empty : forall s,
        Rr RS.Empty s = if eq_regex s RS.Empty then 1 else 0;

      Rr_eps : forall s,
        Rr RS.Eps s = if eq_regex s RS.Eps then 1 else 0;

      Rr_char : forall a1 a2,
        Rr (RS.Char a1) (RS.Char a2) = R a1 a2;

      Rr_star : forall r s, Rr (RS.Star r) (RS.Star s) = Rr r s;

      Rr_seq_right : forall r1 r2 s,
        Rr (RS.Seq r1 s) (RS.Seq r2 s) = Rr r1 r2;

      Rr_seq_left : forall s r1 r2,
        Rr (RS.Seq s r1) (RS.Seq s r2) = Rr r1 r2;

      Rr_alt_right : forall r s1 s2,
        Rr r (RS.Alt s1 s2) = smin (Rr r s1) (Rr r s2);

      Rr_and_right : forall r s1 s2,
        Rr r (RS.And s1 s2) =
          if eq_regex r RS.Empty &&
             C.isEmpty (C.canonize (rs_to_c_regex (RS.And s1 s2)))
          then 1
          else smin (Rr r s1) (Rr r s2);

    (* Lemma 3.3 properties are included as fields *)
      Rr_refl : forall r, Rr r r = 1;
      Rr_sym  : forall r s, Rr r s = Rr s r;
      Rr_trans : forall r1 r2 r,
        smin (Rr r1 r) (Rr r r2) <= Rr r1 r2
    }.

    (* Lemma 3.3: immediate because reflexive/symmetric/transitive are fields. *)
    Lemma Rr_is_similarity (S : regex_similarity) :
      (forall r, Rr S r r = 1) /\
      (forall r s, Rr S r s = Rr S s r) /\
      (forall r1 r2 r, smin (Rr S r1 r) (Rr S r r2) <= Rr S r1 r2).
    Proof.
      split.
      - exact: (Rr_refl S).
      split.
      - exact: (Rr_sym S).
      - exact: (Rr_trans S).
    Qed.

    (* ============================================================ *)
    (* Conjecture 3.1                                               *)
    (* ============================================================ *)

    Theorem regex_similarity_matches_language_similarity :
      forall (S : regex_similarity) (r1 r2 : regex),
        Rr S r1 r2 = RL (RS.den r1) (RS.den r2).
    Proof.
      (* TODO: T depends on RL (inf/sup). *)
      Admitted.

    (* ============================================================ *)
    (* Conjecture 3.2                                               *)
    (* ============================================================ *)
    (* TODO. *)

  End BaseSymbolSimilarity.

End Similarity.
