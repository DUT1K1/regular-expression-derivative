From regexderiv Require Import RegexBasics.
From Stdlib Require Import List.
From Stdlib Require Import Ascii.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Correctness of derivatives                                          *)
(* ------------------------------------------------------------------ *)

(* star_cons_split:
   If a word s is in L* (star_lang L s) and s starts with the letter a
   (so s = a :: w), then we can "peel" that leading a into the first block
   coming from L. Concretely, there exist u and v such that:
     w = u ++ v,
     L (a :: u)          (the first block from L begins with that a),
     star_lang L v.      (the remainder stays in L-star).
   Intuition: a proof that s ∈ L* is built by concatenating blocks u₁,u₂,… ∈ L.
   If u₁ is empty, skip it and look at the tail; if u₁ = a::u, then we’re done. *)

Lemma star_cons_split :
  forall (L : language) (s : word),
    star_lang L s ->
    forall (a : ascii) (w : word),
      s = a :: w ->
      exists u v, w = u ++ v /\ L (a :: u) /\ star_lang L v.
Proof.
  intros L s H.
  induction H as [| u v Lu Hv IH].
  - (* s = [] *) intros a w Heq; discriminate Heq.
  - (* s = u ++ v with Lu : L u and Hv : star_lang L v *)
    intros a w Heq.
    destruct u as [| a' u'].
    + (* u = [] ⇒ s = v *) simpl in Heq. eapply IH; eauto.
    + (* u = a' :: u' *)
      simpl in Heq. inversion Heq; subst.
      (* now a' = a and w = u' ++ v *)
      exists u', v. repeat split; auto.
Qed.
(*  *)

Lemma D_char_correct :
  forall a r w, Lang (D_char a r) w <-> Lang r (a :: w).
Proof.
  induction r; intros w; simpl.
  - tauto.
  - split; [tauto| intros H; inversion H].
  - destruct (ascii_eq_dec a a0) as [->|neq]; simpl; firstorder congruence.
  - specialize (IHr1 w). specialize (IHr2 w). tauto.
  - specialize (IHr1 w). specialize (IHr2 w). tauto.
  - (* Seq *)
    split.
    + intros H; destruct H as [H|H].
      * destruct H as [u [v [Hw [Hu Hv]]]]. subst w.
        exists (a :: u), v. split; [reflexivity|].
        split; [apply IHr1 in Hu; exact Hu | exact Hv].
      * destruct H as [u [v [Hw [Hnu Hv]]]]. subst w.
        unfold nu in Hnu.
        destruct (nullable r1) eqn:En; simpl in Hnu.
        -- apply nullable_correct in En. simpl in Hnu. subst u.
           exists [], (a :: v). split; [reflexivity|].
           split; [exact En | apply IHr2 in Hv; exact Hv].
        -- contradiction.
    + intros [u [v [Huv [Hur Hvr]]]].
      destruct u as [|a' u'].
      * simpl in Huv. right.
        exists [], w. split; [reflexivity|].
        split.
        { unfold nu. apply (proj2 (nullable_correct r1)) in Hur. now rewrite Hur. }
        { rewrite <- Huv in Hvr. apply IHr2. exact Hvr. }
      * inversion Huv as [Htail]. subst a' w.
        left. exists u', v. split; [reflexivity|].
        split; [apply IHr1; exact Hur | exact Hvr].
  - (* Star *)
    split.
    + (* -> *)
      intros [u [v [Hw [Hud Hsv]]]].
      subst w. specialize (IHr u). apply IHr in Hud.
      change (star_lang (Lang r) ((a :: u) ++ v)).
      apply star_app; [assumption|assumption].
    + (* <- *)
      intros Hstar.
      edestruct (star_cons_split (Lang r) (a :: w) Hstar)
        as [u [v [Hw' [Lu Hv']]]]; [reflexivity|].
      exists u, v. split; [exact Hw'|].
      split; [apply IHr; exact Lu | exact Hv'].
  - (* Neg *)
    split; intro H.
    + intro Hr0. apply H. apply IHr. exact Hr0.
    + intro Hr0. apply H. apply IHr. exact Hr0.
Qed.

(* Fuzzy derivative as a union of classic derivatives. *)
Lemma D_mu_char_union :
  forall (R : ascii_sim) (a : ascii) (r : regex) (w : word),
    D_mu_char R a r w <-> exists r', Re R r r' /\ Lang (D_char a r') w.
Proof.
  intros R a r w.
  apply D_mu_char_spec.
Qed.


(* Word derivative correctness by induction on u *)
Lemma D_correct :
  forall u r w, Lang (D u r) w <-> Lang r (u ++ w).
Proof.
  induction u as [| a v IHv]; intros r w; simpl.
  - tauto.
  - rewrite IHv. apply D_char_correct.
Qed.

(* ------------------------------------------------------------------ *)
(* Regular languages and Theorem 4.1                                   *)
(* ------------------------------------------------------------------ *)

Definition regular (L : language) : Prop :=
  exists r, forall w, Lang r w <-> L w.

(* helper: semantics of dlang *)
Lemma dlang_correct :
  forall (u : word) (L : language) (w : word),
    dlang u L w <-> L (u ++ w).
Proof.
  induction u as [|a v IHv]; intros L w; simpl.
  - tauto.
  - rewrite IHv. unfold dlang_char. simpl. tauto.
Qed.

Theorem derivative_regular :
  forall (L : language) (u : word),
    regular L -> regular (dlang u L).
Proof.
  intros L u [r Hr].
  exists (D u r). intro w.
  split.
  - (* -> *)
    intro H.                             (* Lang (D u r) w *)
    apply D_correct in H.                (* Lang r (u ++ w) *)
    apply (proj1 (Hr (u ++ w))) in H.    (* L (u ++ w) *)
    apply (proj2 (dlang_correct u L w)); exact H.
  - (* <- *)
    intro H.                             (* dlang u L w *)
    apply (proj1 (dlang_correct u L w)) in H.  (* L (u ++ w) *)
    apply (proj2 (Hr (u ++ w))) in H.          (* Lang r (u ++ w) *)
    apply D_correct; exact H.                  (* Lang (D u r) w *)
Qed.
