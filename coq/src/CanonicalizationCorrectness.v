From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import Languages.
From regexderiv Require Import RegexSemantics.
From regexderiv Require Import Canonicalization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CanonicalizationCorrectness (X : OSYM).
  Import X.

  Module Export RS := RegexSemantics X.
  Module Export C  := Canonicalization X.


  Lemma conc_void_l (K : language) :
    Languages.conc (A:=A) (Languages.void (A:=A)) K =i Languages.void (A:=A).
  Proof.
    move=> w; rewrite /Languages.void.
    apply/negP => H.
    have [u [v [_ [Hu _]]]] := Languages.concP (A:=A) H.
    by rewrite /pred0 in Hu.
  Qed.

  Lemma conc_void_r (L : language) :
    Languages.conc (A:=A) L (Languages.void (A:=A)) =i Languages.void (A:=A).
  Proof.
    move=> w; rewrite /Languages.void.
    apply/negP => H.
    have [u [v [_ [_ Hv]]]] := Languages.concP (A:=A) H.
    by rewrite /pred0 in Hv.
  Qed.

  Lemma conc_eps_l (L : language) :
    Languages.conc (A:=A) (Languages.eps (A:=A)) L =i L.
  Proof.
    move=> w; apply/idP/idP.
    - move=> H; have [u [v [Huv [Hu Hv]]]] := Languages.concP (A:=A) H.
      move: Hu; rewrite /Languages.eps.
      move/eqP => Hu; subst u.
      by rewrite cat0s in Huv; subst v.
    - move=> Hw.
      apply: (Languages.concP_inv (A:=A)).
      exists [::], w; split; first by [].
      split; first by rewrite /Languages.eps eqxx.
      exact Hw.
  Qed.

  Lemma conc_eps_r (L : language) :
    Languages.conc (A:=A) L (Languages.eps (A:=A)) =i L.
  Proof.
    move=> w; apply/idP/idP.
    - move=> H; have [u [v [Huv [Hu Hv]]]] := Languages.concP (A:=A) H.
      move: Hv; rewrite /Languages.eps.
      move/eqP => Hv; subst v.
      by rewrite cats0 in Huv; subst u.
    - move=> Hw.
      apply: (Languages.concP_inv (A:=A)).
      exists w, [::]; split; first by rewrite cats0.
      split; first exact Hw.
      by rewrite /Languages.eps eqxx.
  Qed.

  Lemma conc_assoc (L K M : language) :
    Languages.conc (A:=A) (Languages.conc (A:=A) L K) M =i
    Languages.conc (A:=A) L (Languages.conc (A:=A) K M).
  Proof.
    move=> w; apply/idP/idP.
    - move=> H.
      have [u [v [Huv [Hu Hv]]]] := Languages.concP (A:=A) H.
      have [u1 [u2 [Hu12 [Hu1 Hu2]]]] := Languages.concP (A:=A) Hu.
      subst u.
      apply: (Languages.concP_inv (A:=A)).
      exists u1, (u2 ++ v); split; first by rewrite catA.
      split; first exact Hu1.
      apply: (Languages.concP_inv (A:=A)).
      exists u2, v; split; first by [].
      by split.
    - move=> H.
      have [u [v [Huv [Hu Hv]]]] := Languages.concP (A:=A) H.
      have [v1 [v2 [Hv12 [Hv1 Hv2]]]] := Languages.concP (A:=A) Hv.
      subst v.
      apply: (Languages.concP_inv (A:=A)).
      exists (u ++ v1), v2; split.
      + by rewrite catA in Huv.
      split.
      + apply: (Languages.concP_inv (A:=A)).
        exists u, v1; split; first by [].
        by split.
      + exact Hv2.
  Qed.

  Lemma star_id (L : language) : Languages.star (A:=A) (Languages.star (A:=A) L) =i Languages.star (A:=A) L.
  Proof.
    have star_cat :
      forall u v, Languages.star (A:=A) L u -> Languages.star (A:=A) L v ->
        Languages.star (A:=A) L (u ++ v).
    {
      have aux :
        forall n, forall u, size u <= n -> forall v,
          Languages.star (A:=A) L u -> Languages.star (A:=A) L v ->
          Languages.star (A:=A) L (u ++ v).
      {
        elim=> [|n IH] u.
        - case: u => [|a u].
          + move=> _ v _ Hv. by rewrite cat0s.
          + move=> Hle v Hu Hv. by rewrite /= in Hle.
        - case: u => [|a u].
          + move=> _ v _ Hv. by rewrite cat0s.
          + move=> Hle v Hu Hv.
            have [p [q [Heq [Hp Hq]]]] :=
              Languages.star_cons_split (A:=A) (L:=L) (a:=a) Hu.
            have Hpq : size p + size q < n.+1.
            { move: Hle. by rewrite /= Heq size_cat. }
            have Hpq' : size p + size q <= n.
            { move: Hpq. by rewrite ltnS. }
            have Hqp : size q + size p <= n by rewrite addnC Hpq'.
            have Hleq : size q <= n.
            { exact: leq_trans (leq_addr (size p) (size q)) Hqp. }
            have Hqv : Languages.star (A:=A) L (q ++ v) :=
              IH q Hleq v Hq Hv.
            rewrite /= Heq.
            have -> : a :: ((p ++ q) ++ v) = a :: (p ++ (q ++ v)) by rewrite catA.
            apply: (Languages.star_cons_split_inv (A:=A) (L:=L) (a:=a)
                                                  (w:=p ++ (q ++ v))).
            exists p, (q ++ v); split; first by [].
            by split.
      }
      move=> u v Hu Hv.
      exact (aux (size u) u (leqnn _) v Hu Hv).
    }
    have lift_piece :
      forall x, L x -> Languages.star (A:=A) L x.
    {
      move=> x Hx; case: x Hx => [|a x] Hx.
      - exact (Languages.star_nil (A:=A) L).
      - apply: (Languages.star_cons_split_inv (A:=A) (L:=L) (a:=a) (w:=x)).
        exists x, [::]; split; first by rewrite cats0.
        split; first exact Hx.
        exact (Languages.star_nil (A:=A) L).
    }
    move=> w; apply/idP/idP.
    - move=> H.
      have [xs [_ [Hflat Hall]]] := Languages.starP (A:=A) H.
      have Hfold :
        forall ys, Languages.all_in (A:=A) (Languages.star (A:=A) L) ys ->
          Languages.star (A:=A) L (Languages.flatten_words ys).
      { elim=> [|x ys IH].
        - move=> _. exact (Languages.star_nil (A:=A) L).
        - move=> /= /andP [Hx Hys].
          exact (star_cat _ _ Hx (IH Hys)).
      }
      have : Languages.star (A:=A) L (Languages.flatten_words xs) := Hfold xs Hall.
      by move/eqP: Hflat => <-.
    - move=> H.
      have [xs [Hxs [Hflat Hall]]] := Languages.starP (A:=A) H.
      have Hall_star :
        forall ys, Languages.all_in (A:=A) L ys ->
          Languages.all_in (A:=A) (Languages.star (A:=A) L) ys.
      { elim=> [|x ys IH].
        - by [].
        - move=> /= /andP [Hx Hys].
          by rewrite (lift_piece x Hx) (IH Hys).
      }
      have Hall' : Languages.all_in (A:=A) (Languages.star (A:=A) L) xs := Hall_star xs Hall.
      exact: (Languages.starP_inv (A:=A) (L:=Languages.star (A:=A) L) (w:=w) (xs:=xs)
                                  Hxs Hflat Hall').
  Qed.


  Lemma cmpR_eq : forall r s, cmpR r s = Eq -> r = s.
  Proof.
    elim=> [| |a |r1 IH1 r2 IH2 |r1 IH1 r2 IH2 |r IH |r1 IH1 r2 IH2 |r IH]
          [| |b |s1 s2 |s1 s2 |s |s1 s2 |s] //= H;
      try by move: H; discriminate.
    - (* Char *)
      have Hab : is_true (if cmpA a b is Eq then true else false).
      { by rewrite H. }
      move: (elimT (cmpA_eq_axiom a b) Hab) => ->.
      by [].
    - (* Alt *)
      case E: (cmpR r1 s1) H => [| |] //= H.
      have -> : r1 = s1 := IH1 _ E.
      have -> : r2 = s2 := IH2 _ H.
      by [].
    - (* Seq *)
      case E: (cmpR r1 s1) H => [| |] //= H.
      have -> : r1 = s1 := IH1 _ E.
      have -> : r2 = s2 := IH2 _ H.
      by [].
    - (* Star *)
      by have -> : r = s := IH _ H.
    - (* And *)
      case E: (cmpR r1 s1) H => [| |] //= H.
      have -> : r1 = s1 := IH1 _ E.
      have -> : r2 = s2 := IH2 _ H.
      by [].
    - (* Neg *)
      by have -> : r = s := IH _ H.
  Qed.

  Lemma eqR_sound r s : eqR r s -> r = s.
  Proof.
    move=> H.
    rewrite /eqR in H.
    case E: (cmpR r s) H => //= _.
    apply: cmpR_eq.
    by rewrite E.
  Qed.


  Lemma mem_Top (w : word) : (w \in Top) = true.
  Proof. by rewrite /Top -topredE /= /Languages.void. Qed.

  Lemma mem_mkPlus_list (xs : seq regex) (w : word) :
    (w \in mkPlus_list xs) = has (fun r => w \in r) xs.
  Proof.
    have aux : forall r ys,
      (w \in mkPlus_list (r :: ys)) = (w \in r) || has (fun t => w \in t) ys.
    {
      move=> r ys; elim: ys r => [|s ys IH] r.
      - by rewrite /= orbF.
      - change ((w \in r) || (w \in mkPlus_list (s :: ys)) =
                (w \in r) || has (fun t => w \in t) (s :: ys)).
        change (has (fun t => w \in t) (s :: ys))
          with ((w \in s) || has (fun t => w \in t) ys).
        by rewrite (IH s) orbA.
    }
    case: xs => [|r xs] /=.
    - by [].
    - by rewrite aux.
  Qed.

  Lemma mem_plus_terms (r : regex) (w : word) :
    has (fun t => w \in t) (plus_terms r) = (w \in r).
  Proof.
    elim: r w => [| |a |r1 IH1 r2 IH2 |r1 IH1 r2 IH2 |r IH |r1 IH1 r2 IH2 |r IH] w.
    - by rewrite /plus_terms has_seq1 /=.
    - by rewrite /plus_terms has_seq1 /=.
    - by rewrite /plus_terms has_seq1 /=.
    - rewrite /plus_terms /= has_cat IH1 IH2.
      by [].
    - by rewrite /plus_terms has_seq1 /=.
    - by rewrite /plus_terms has_seq1 /=.
    - by rewrite /plus_terms has_seq1 /=.
    - by rewrite /plus_terms has_seq1 /=.
  Qed.

  Lemma has_insertR (P : pred regex) (x : regex) (xs : seq regex) :
    has P (insertR x xs) = P x || has P xs.
  Proof.
    elim: xs => [|y ys IH].
    - by [].
    - rewrite /=.
      case: (leR x y) => /=.
      + by [].
      + by rewrite IH; case: (P x); case: (P y); case: (has P ys).
  Qed.

  Lemma has_sortR (P : pred regex) (xs : seq regex) :
    has P (sortR xs) = has P xs.
  Proof.
    elim: xs => [|x xs IH] //=.
    by rewrite has_insertR IH.
  Qed.

  Lemma has_dedup_adj (P : pred regex) (xs : seq regex) :
    (forall x y, eqR x y -> P x = P y) ->
    has P (dedup_adj xs) = has P xs.
  Proof.
    move=> Pext.
    elim: xs => [|x xs IH] //=.
    case: xs IH => [|y ys IH] //=.
    case Exy: (eqR x y).
    - have -> : P x = P y by apply: Pext; exact Exy.
      change (has P (dedup_adj (y :: ys)) = P y || has P (y :: ys)).
      by rewrite IH /=; case: (P y); case: (has P ys).
    - change (has P (x :: dedup_adj (y :: ys)) = P x || has P (y :: ys)).
      by rewrite /= IH.
  Qed.

  Lemma has_filter_notEmpty (w : word) (xs : seq regex) :
    has (fun t => w \in t) (filter (fun t => ~~ isEmpty t) xs) =
    has (fun t => w \in t) xs.
  Proof.
    elim: xs => [|x xs IH] //=.
    case: x => //=; by rewrite IH.
  Qed.

  Lemma mkPlus_correct (r s : regex) (w : word) :
    (w \in mkPlus r s) = ((w \in r) || (w \in s)).
  Proof.
    rewrite /mkPlus.
    set xs0 := plus_terms r ++ plus_terms s.
    set xs1 := filter (fun t => ~~ isEmpty t) xs0.
    set xs2 := sortR xs1.
    set xs3 := dedup_adj xs2.
    rewrite (mem_mkPlus_list xs3 w).
    have -> : has (fun t => w \in t) xs3 = has (fun t => w \in t) xs2.
    { apply: (has_dedup_adj (P:=fun t => w \in t)).
      move=> x y /eqR_sound ->; by [].
    }
    rewrite (has_sortR (fun t => w \in t) xs1).
    rewrite /xs1 (has_filter_notEmpty w xs0).
    rewrite /xs0 has_cat (mem_plus_terms r w) (mem_plus_terms s w).
    by [].
  Qed.

  Lemma mem_mkAnd_list (xs : seq regex) (w : word) :
    (w \in mkAnd_list xs) = all (fun r => w \in r) xs.
  Proof.
    have aux : forall r ys,
      (w \in mkAnd_list (r :: ys)) = (w \in r) && all (fun t => w \in t) ys.
    {
      move=> r ys; elim: ys r => [|s ys IH] r.
      - by rewrite /= andbT.
      - change ((w \in r) && (w \in mkAnd_list (s :: ys)) =
                (w \in r) && all (fun t => w \in t) (s :: ys)).
        change (all (fun t => w \in t) (s :: ys))
          with ((w \in s) && all (fun t => w \in t) ys).
        by rewrite (IH s) andbA.
    }
    case: xs => [|r xs] /=.
    - by rewrite /Top mem_Top.
    - by rewrite aux.
  Qed.

  Lemma mem_and_terms (r : regex) (w : word) :
    all (fun t => w \in t) (and_terms r) = (w \in r).
  Proof.
    elim: r w => [| |a |r1 IH1 r2 IH2 |r1 IH1 r2 IH2 |r IH |r1 IH1 r2 IH2 |r IH] w.
    - by rewrite /and_terms all_seq1 /=.
    - by rewrite /and_terms all_seq1 /=.
    - by rewrite /and_terms all_seq1 /=.
    - by rewrite /and_terms all_seq1 /=.
    - by rewrite /and_terms all_seq1 /=.
    - by rewrite /and_terms all_seq1 /=.
    - rewrite /and_terms /= all_cat IH1 IH2.
      by [].
    - by rewrite /and_terms all_seq1 /=.
  Qed.

  Lemma all_insertR (P : pred regex) (x : regex) (xs : seq regex) :
    all P (insertR x xs) = P x && all P xs.
  Proof.
    elim: xs => [|y ys IH].
    - by [].
    - rewrite /=.
      case: (leR x y) => /=.
      + by [].
      + by rewrite IH; case: (P x); case: (P y); case: (all P ys).
  Qed.

  Lemma all_sortR (P : pred regex) (xs : seq regex) :
    all P (sortR xs) = all P xs.
  Proof.
    elim: xs => [|x xs IH] //=.
    by rewrite all_insertR IH.
  Qed.

  Lemma all_dedup_adj (P : pred regex) (xs : seq regex) :
    (forall x y, eqR x y -> P x = P y) ->
    all P (dedup_adj xs) = all P xs.
  Proof.
    move=> Pext.
    elim: xs => [|x xs IH] //=.
    case: xs IH => [|y ys IH] //=.
    case Exy: (eqR x y).
    - have -> : P x = P y by apply: Pext; exact Exy.
      change (all P (dedup_adj (y :: ys)) = P y && all P (y :: ys)).
      by rewrite IH /=; case: (P y); case: (all P ys).
    - change (all P (x :: dedup_adj (y :: ys)) = P x && all P (y :: ys)).
      by rewrite /= IH.
  Qed.

  Lemma all_filter_notTop (w : word) (xs : seq regex) :
    all (fun t => w \in t) (filter (fun t => ~~ isTop t) xs) =
    all (fun t => w \in t) xs.
  Proof.
    elim: xs => [|x xs IH] //=.
    case: x => //=; try by rewrite IH.
    case=> //=.
    - by rewrite /= IH.
    all: by rewrite IH.
  Qed.

  Lemma mkAnd_correct (r s : regex) (w : word) :
    (w \in mkAnd r s) = ((w \in r) && (w \in s)).
  Proof.
    rewrite /mkAnd.
    set xs0 := and_terms r ++ and_terms s.
    case Hempt: (has isEmpty xs0).
    - (* return Empty *)
      have : all (fun t => w \in t) xs0 = false.
      { have Hall_false :
            forall ys, has isEmpty ys -> all (fun t => w \in t) ys = false.
        { elim=> [|t ys IH] //=.
          case Et: (isEmpty t) => //= H.
          - move: Et; rewrite /isEmpty; case: t => //=.
          - case Hwt: (w \in t) => //=.
            exact (IH H).
        }
        have Hhas : has isEmpty xs0 by rewrite Hempt.
        exact: (Hall_false xs0 Hhas).
      }
      move=> Hfalse.
      have -> : ((w \in r) && (w \in s)) = false.
      { move: Hfalse.
        by rewrite /xs0 all_cat (mem_and_terms r w) (mem_and_terms s w).
      }
      by [].
    - (* non-empty branch *)
      set xs1 := filter (fun t => ~~ isTop t) xs0.
      set xs2 := sortR xs1.
      set xs3 := dedup_adj xs2.
      rewrite (mem_mkAnd_list xs3 w).
      have -> : all (fun t => w \in t) xs3 = all (fun t => w \in t) xs2.
      { apply: (all_dedup_adj (P:=fun t => w \in t)).
        move=> x y /eqR_sound ->; by [].
      }
      rewrite (all_sortR (fun t => w \in t) xs1).
      rewrite /xs1 (all_filter_notTop w xs0).
      rewrite /xs0 all_cat (mem_and_terms r w) (mem_and_terms s w).
      by [].
  Qed.


  Lemma Seq_Eps_l (r : regex) : (forall w, (w \in Seq Eps r) = (w \in r)).
  Proof.
    move=> w.
    rewrite -topredE /=.
    exact: (conc_eps_l (den r) w).
  Qed.

  Lemma Seq_Eps_r (r : regex) : (forall w, (w \in Seq r Eps) = (w \in r)).
  Proof.
    move=> w.
    rewrite -topredE /=.
    exact: (conc_eps_r (den r) w).
  Qed.

  Lemma Seq_assoc (r1 r2 r3 : regex) : Seq (Seq r1 r2) r3 ≈ Seq r1 (Seq r2 r3).
  Proof.
    move=> w.
    rewrite -!topredE /=.
    exact: (conc_assoc (den r1) (den r2) (den r3) w).
  Qed.

  Lemma mkConc_list_cat (xs zs : seq regex) :
    mkConc_list (xs ++ zs) ≈ Seq (mkConc_list xs) (mkConc_list zs).
  Proof.
    have aux : forall us vs,
      mkConc_list (us ++ vs) ≈ Seq (mkConc_list us) (mkConc_list vs).
    {
      elim=> [|x us IH] vs w /=.
      - by rewrite (Seq_Eps_l (mkConc_list vs) w).
      - case: us IH => [|x2 us' IH] /=.
        + case: vs => [|y vs] /=.
          * by rewrite (Seq_Eps_r x w).
          * by [].
        + have Hseq :
              Seq x (mkConc_list ((x2 :: us') ++ vs)) ≈
              Seq x (Seq (mkConc_list (x2 :: us')) (mkConc_list vs)).
          { apply: re_equiv_Seq.
            - exact: re_equiv_refl.
            - exact: (IH vs).
          }
          move: (Hseq w).
          rewrite -(Seq_assoc x (mkConc_list (x2 :: us')) (mkConc_list vs) w).
          by [].
    }
    exact: (aux xs zs).
  Qed.

  Lemma conc_terms_correct (r : regex) : mkConc_list (conc_terms r) ≈ r.
  Proof.
    elim: r => //=.
    - move=> r1 IH1 r2 IH2 w.
      (* conc_terms (Seq r1 r2) flattens *)
      rewrite /conc_terms /=.
      have Hcat := mkConc_list_cat (conc_terms r1) (conc_terms r2) w.
      (* combine IHs *)
      have := (RS.re_equiv_Seq IH1 IH2) w.
      by rewrite Hcat.
  Qed.

  Lemma mkConc_list_filter_eps (xs : seq regex) :
    mkConc_list (filter (fun t => ~~ isEps t) xs) ≈ mkConc_list xs.
  Proof.
    elim: xs => [|x xs IH] //=.
    case: xs IH => [|y ys IH] //=.
    - case: x => //=; by move=> * w.
    - case Ex: (isEps x) => //=.
      + (* drop leading Eps *)
        have -> : x = Eps.
        { move: Ex; rewrite /isEps; by case: x. }
        move=> w.
        rewrite (Seq_Eps_l (mkConc_list (y :: ys)) w).
        exact: (IH w).
      + (* keep x *)
        move=> w.
        rewrite (mkConc_list_cat [:: x] (filter (fun t => ~~ isEps t) (y :: ys)) w).
        rewrite (mkConc_list_cat [:: x] (y :: ys) w).
        exact: ((RS.re_equiv_Seq (re_equiv_refl x) IH) w).
  Qed.

  Lemma mkConc_list_has_empty (xs : seq regex) (w : word) :
    has isEmpty xs -> (w \in mkConc_list xs) = false.
  Proof.
    have aux : forall ys, has isEmpty ys -> mkConc_list ys ≈ Empty.
    {
      elim=> [|x ys IH] //=.
      case: ys IH => [|y ys IH] //=.
      - move=> H.
        destruct x; simpl in H; try discriminate.
        by move=> w0.
      - case Ex: (isEmpty x).
        + destruct x; simpl in Ex; try discriminate.
          move=> _ w0.
          change ((w0 \in Seq Empty (mkConc_list (y :: ys))) = false).
          rewrite -[w0 \in Seq Empty (mkConc_list (y :: ys))]topredE /=.
          apply/negP => Hc.
          have [u [v [_ [Hu _]]]] := Languages.concP (A:=A) Hc.
          by rewrite /pred0 in Hu.
        + move=> H.
          have Htail : has isEmpty (y :: ys) := H.
          have Hseq : Seq x (mkConc_list (y :: ys)) ≈ Seq x Empty.
          { apply: re_equiv_Seq.
            - exact: re_equiv_refl.
            - exact: (IH Htail).
          }
          move=> w0.
          rewrite (Hseq w0) -topredE /=.
          exact: (conc_void_r (den x) w0).
    }
    move=> H.
    have Hempty : mkConc_list xs ≈ Empty := aux xs H.
    move: (Hempty w).
    by rewrite -topredE /= /Languages.void.
  Qed.

  Lemma mkConc_list_seq_terms (r s : regex) (w : word) :
    (w \in Seq r s) = (w \in mkConc_list (conc_terms r ++ conc_terms s)).
  Proof.
    have Hr : mkConc_list (conc_terms r) ≈ r := conc_terms_correct r.
    have Hs : mkConc_list (conc_terms s) ≈ s := conc_terms_correct s.
    have Hcat := mkConc_list_cat (conc_terms r) (conc_terms s) w.
    have Hseq := (RS.re_equiv_Seq Hr Hs) w.
    rewrite -Hseq.
    exact: (esym Hcat).
  Qed.

  Lemma mkConc_correct (r s : regex) (w : word) :
    (w \in mkConc r s) = (w \in Seq r s).
  Proof.
    rewrite /mkConc.
    set xs0 := conc_terms r ++ conc_terms s.
    case Hempt: (has isEmpty xs0).
    - (* mkConc returns Empty *)
      have Hseq := mkConc_list_seq_terms r s w.
      rewrite Hseq.
      by rewrite (mkConc_list_has_empty (xs:=xs0) w Hempt).
    - (* mkConc returns mkConc_list (filter notEps xs0) *)
      set xs1 := filter (fun t => ~~ isEps t) xs0.
      have Hseq := mkConc_list_seq_terms r s w.
      rewrite Hseq.
      (* filter eps does not change *)
      have Heps : mkConc_list xs1 ≈ mkConc_list xs0 := mkConc_list_filter_eps xs0.
      by rewrite Heps.
  Qed.

  Lemma mkStar_correct (r : regex) (w : word) :
    (w \in mkStar r) = (w \in Star r).
  Proof.
    case: r => //=.
    - (* Empty *)
      rewrite -topredE /=.
      (* star void = eps *)
      by rewrite (Languages.star_void (A:=A) w).
    - (* Eps *)
      rewrite -topredE /=.
      by rewrite (Languages.star_eps (A:=A) w).
    - (* Star r *)
      move=> r.
      rewrite -topredE /=.
      (* star of a star language is idempotent *)
      exact: (esym (star_id (den r) w)).
  Qed.

  Lemma mkNot_correct (r : regex) (w : word) :
    (w \in mkNot r) = (w \in Neg r).
  Proof.
    case: r => //=.
    move=> r.
    change (w \in Neg (Neg r)) with (~~ ~~ (w \in r)).
    by rewrite negbK.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Main theorem: canonicalization preserves denotation                *)
  (* ------------------------------------------------------------------ *)

  Theorem canonize_correct (r : regex) (w : word) :
    (w \in canonize r) = (w \in r).
  Proof.
    elim: r w => [| |a |r1 IH1 r2 IH2 |r1 IH1 r2 IH2 |r IH |r1 IH1 r2 IH2 |r IH] w //=.
    - (* Alt *)
      rewrite (mkPlus_correct (canonize r1) (canonize r2) w).
      by rewrite IH1 IH2.
    - (* Seq *)
      rewrite (mkConc_correct (canonize r1) (canonize r2) w).
      exact: (Languages.conc_ext (A:=A) IH1 IH2 w).
    - (* Star *)
      rewrite (mkStar_correct (canonize r) w).
      exact: (Languages.star_ext (A:=A) IH w).
    - (* And *)
      rewrite (mkAnd_correct (canonize r1) (canonize r2) w).
      by rewrite IH1 IH2.
    - (* Neg *)
      rewrite (mkNot_correct (canonize r) w).
      exact: ((RS.re_equiv_Neg IH) w).
  Qed.


  Lemma canonize_equiv (r : regex) : canonize r ≈ r.
  Proof. by move=> w; exact: canonize_correct. Qed.

  Lemma canonize_idem_lang (r : regex) : canonize (canonize r) ≈ canonize r.
  Proof.
    move=> w; rewrite !canonize_correct.
    reflexivity.
  Qed.

End CanonicalizationCorrectness.
