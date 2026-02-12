From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Languages.

Section Lang.
  Variable A : eqType.

  Definition word := seq A.
  Definition language := pred word. (* word -> bool *)

  (* basic languages *)
  Definition void : language := pred0.
  Definition eps  : language := fun w => w == [::].
  Definition atom (a : A) : language := fun w => w == [:: a].

  (* boolean connectives *)
  Definition plus (L K : language) : language := fun w => L w || K w.
  Definition prod (L K : language) : language := fun w => L w && K w.
  Definition compl (L : language)  : language := fun w => ~~ L w.

  (* concatenation: exists split w = u ++ v with L u and K v *)
  Definition conc (L K : language) : language :=
    fun w => has (fun i =>
      let u := take i w in
      let v := drop i w in
      L u && K v) (iota 0 (size w).+1).

  Lemma concP (L K : language) (w : word) :
    conc L K w ->
    exists u v, w = u ++ v /\ L u /\ K v.
  Proof.
    move=> /hasP [i Hi] /=.
    set u := take i w.
    set v := drop i w.
    move=> /andP [Hu Hv].
    exists u, v; split.
    - by rewrite /u /v cat_take_drop.
    - by split.
  Qed.

  Lemma concP_inv (L K : language) (w : word) :
    (exists u v, w = u ++ v /\ L u /\ K v) -> conc L K w.
  Proof.
    move=> [u [v [-> [Hu Hv]]]].
    apply/hasP.
    exists (size u).
    - 
      rewrite mem_iota add0n.
      apply/andP; split.
      + exact: leq0n.
      + 
        have Hle : size u <= size (u ++ v) by rewrite size_cat leq_addr.
        by rewrite -ltnS.
    - 
      rewrite /conc /=.
      rewrite take_size_cat ?leqnn //.
      rewrite drop_size_cat ?leqnn //.
      by rewrite Hu Hv.
  Qed.

  Fixpoint all_in (L : language) (xs : seq word) : bool :=
    match xs with
    | [::] => true
    | x :: xs' => L x && all_in L xs'
    end.

  Fixpoint flatten_words (xs : seq word) : word :=
    match xs with
    | [::] => [::]
    | x :: xs' => x ++ flatten_words xs'
    end.

  Fixpoint splits (w : word) : seq (seq word) :=
    match w with
    | [::] => [:: [::] ]
    | a :: w' =>
      flatten [seq
        match ds with
        | [::] => [:: [:: [:: a] ] ]
        | x :: xs => [:: [:: a] :: ds; (a :: x) :: xs]
        end
      | ds <- splits w']
    end.

  Definition star (L : language) : language :=
    fun w => has (fun xs => (flatten_words xs == w) && all_in L xs) (splits w).

  Lemma conc_ext (L1 L2 K1 K2 : language) :
  (L1 =i L2) -> (K1 =i K2) -> conc L1 K1 =i conc L2 K2.
Proof.
  move=> HL HK w.
  rewrite /conc.
  apply: eq_has => i /=.
  have Hab : L1 (take i w) = L2 (take i w) := HL (take i w).
  have Hcd : K1 (drop i w) = K2 (drop i w) := HK (drop i w).
  by rewrite Hab Hcd.
Qed.


  Lemma all_in_ext (L1 L2 : language) :
    (L1 =i L2) -> forall xs, all_in L1 xs = all_in L2 xs.
  Proof.
    move=> HL; elim=> [|x xs IH] //=.
    set a := L1 x.
    set b := L2 x.
    have Hab : a = b by rewrite /a /b; exact: HL.
    by rewrite Hab IH.
  Qed.

  Lemma star_ext (L1 L2 : language) :
    (L1 =i L2) -> star L1 =i star L2.
  Proof.
    move=> HL w; rewrite /star.
    apply: eq_has => xs /=.
    set a := all_in L1 xs.
    set b := all_in L2 xs.
    have Hab : a = b by rewrite /a /b (all_in_ext HL xs).
    by rewrite Hab.
  Qed.

  Lemma conc_nil (L K : language) :
  conc L K [::] = (L [::] && K [::]).
Proof.
  apply/idP/idP.
  - move=> H.
    have [u [v [Huv [Hu Hv]]]] := concP H.
    have /andP [Hu0 Hv0] : (size u == 0) && (size v == 0).
    { move: (congr1 size Huv); rewrite size_cat /=.
      move/eqP; rewrite eq_sym addn_eq0.
      by []. }
    have Hu_nil : u = [::] by apply/eqP; rewrite -size_eq0 Hu0.
    have Hv_nil : v = [::] by apply/eqP; rewrite -size_eq0 Hv0.
    move: Hu Hv; rewrite Hu_nil Hv_nil.
    by move=> Hu Hv; rewrite Hu Hv.
  - move=> /andP [Hu Hv].
    apply: concP_inv.
    exists [::], [::]; split; first by [].
    by split.
Qed.


  Lemma star_nil (L : language) : star L [::].
  Proof.
    by rewrite /star /=.
  Qed.

  Lemma starP (L : language) (w : word) :
    star L w ->
    exists xs,
      xs \in splits w /\
      flatten_words xs == w /\
      all_in L xs.
  Proof.
    move=> /hasP [xs Hxs /andP [Hflat Hall]].
    exists xs; split=> //; split=> //.
  Qed.

  Lemma starP_inv (L : language) (w : word) (xs : seq word) :
    xs \in splits w ->
    flatten_words xs == w ->
    all_in L xs ->
    star L w.
  Proof.
    move=> Hxs Hflat Hall.
    rewrite /star.
    apply/hasP.
    exists xs => //.
    by apply/andP; split.
  Qed.

  Lemma splits_cons_shape (a : A) (w : word) (xs : seq word) :
    xs \in splits (a :: w) -> exists t ys, xs = (a :: t) :: ys.
  Proof.
    move=> Hxs; rewrite /= in Hxs.
    move/flattenP: Hxs => [ys Hys Hxsin].
    move/mapP: Hys => [ds Hds Hys].
    move: Hxsin; rewrite Hys.
    clear Hds Hys.
    case: ds => [|x ds] /=.
    - rewrite in_cons.
      move/orP=> [/eqP ->|].
      + by exists [::], [::].
      + by rewrite in_nil.
    - rewrite !in_cons.
      move/orP=> [/eqP ->|].
      + by exists [::], (x :: ds).
      + move/orP=> [/eqP ->|].
        * by exists x, ds.
        * by rewrite in_nil.
  Qed.


  Lemma splits_start_new (a : A) (w : word) (ds : seq word) :
    ds \in splits w -> ([:: a] :: ds) \in splits (a :: w).
  Proof.
    move=> Hds; rewrite /=.
    apply/flattenP.
    exists (match ds with
            | [::] => [:: [:: [:: a] ] ]
            | x :: xs => [:: [:: a] :: ds; (a :: x) :: xs]
            end).
    - apply/mapP; exists ds => //.
    - case: ds Hds => [|x xs] Hds //=; by rewrite in_cons eqxx.
  Qed.

  Lemma splits_extend_head (a : A) (w : word) (x : word) (xs : seq word) :
    (x :: xs) \in splits w -> ((a :: x) :: xs) \in splits (a :: w).
  Proof.
    move=> Hx; rewrite /=.
    apply/flattenP.
    exists ([:: [:: a] :: (x :: xs); (a :: x) :: xs]).
    - apply/mapP; exists (x :: xs) => //.
    - rewrite in_cons.
      apply/orP; right.
      by rewrite in_cons eqxx.
  Qed.

  Lemma splits_head_cat (u v : word) (ys : seq word) :
    u != [::] -> ys \in splits v -> (u :: ys) \in splits (u ++ v).
  Proof.
    elim: u ys => [|a [|b u] IH] ys //=.
    - move=> _ Hys.
      exact: (@splits_start_new a v ys Hys).
    - move=> _ Hys.
      have Hih : ((b :: u) :: ys) \in splits ((b :: u) ++ v).
      { apply: IH; first by [].
        exact: Hys. }
      exact: (@splits_extend_head a ((b :: u) ++ v) (b :: u) ys Hih).
  Qed.

    Lemma splits_tail (w : word) (x : word) (xs : seq word) :
    (x :: xs) \in splits w -> xs \in splits (drop (size x) w).
  Proof.
    elim: w x xs => [|a w IH] x xs /=.
    - move=> H; move: H; rewrite in_cons; move/orP=> [/eqP H|];
        last by rewrite in_nil.
      by case: H.
    - move=> Hmem.
      move/flattenP: Hmem => [zs Hzs Hinx].
      move/mapP: Hzs => [ds Hds Hzs].
      move: Hinx; rewrite Hzs.
      clear Hzs.
      case: ds Hds => [|y ys] Hds Hinx /=.
      + rewrite in_cons in Hinx.
        move/orP: Hinx => [/eqP Hcase|]; last by rewrite in_nil.
        have Hx : x = [:: a] := congr1 (head [::]) Hcase.
        have Hxs : xs = [::] := congr1 behead Hcase.
        subst x xs.
        rewrite /= drop0 in Hds *.
        exact: Hds.
      + rewrite !in_cons in Hinx.
        move/orP: Hinx => [/eqP Hcase1|Hinx].
        * have Hx : x = [:: a] := congr1 (head [::]) Hcase1.
          have Hxs : xs = y :: ys := congr1 behead Hcase1.
          subst x xs.
          rewrite /= drop0 in Hds *.
          exact: Hds.
        * move/orP: Hinx => [/eqP Hcase2|]; last by rewrite in_nil.
          have Hx : x = a :: y := congr1 (head [::]) Hcase2.
          have Hxs : xs = ys := congr1 behead Hcase2.
          subst x xs.
          have Hih : ys \in splits (drop (size y) w) := IH y ys Hds.
          rewrite /=.
          exact Hih.
  Qed.

    Lemma star_cons_split (L : language) (a : A) (w : word) :
    star L (a :: w) ->
    exists u v, w = u ++ v /\ L (a :: u) /\ star L v.
  Proof.
    move=> Hs.
    have [xs [Hxs [Hflat Hall]]] := starP Hs.
    have [t [ys Hshape]] := splits_cons_shape Hxs.
    subst xs.
    move/andP: Hall => [HLhead HLtail].

    (* flatten_words ((a::t)::ys) = a::w *)
    have Hcat0 : (a :: t) ++ flatten_words ys = a :: w.
    { have := eqP Hflat. by rewrite /=. }

    (* turn (a::t)++... into a::(t++...) so we can take tails *)
    have Hcat1 : a :: (t ++ flatten_words ys) = a :: w.
    { by move: Hcat0; rewrite -cat_cons. }

    have Hw : t ++ flatten_words ys = w := congr1 behead Hcat1.

    exists t, (flatten_words ys); split; first by rewrite Hw.
    split; first exact HLhead.

    apply: starP_inv.
    - (* ys ∈ splits (flatten_words ys) *)
      have Hy0 : ys \in splits (drop (size (a :: t)) (a :: w)) :=
        splits_tail Hxs.
      have Hdrop : drop (size (a :: t)) (a :: w) = flatten_words ys.
      { (* rewrite a::w as (a::t)++flatten_words ys via Hcat0 *)
        by rewrite -Hcat0 drop_size_cat ?leqnn. }
      rewrite Hdrop in Hy0.
      exact Hy0.
    - by rewrite eqxx.
    - exact HLtail.
  Qed.


  Lemma star_cons_split_inv (L : language) (a : A) (w : word) :
    (exists u v, w = u ++ v /\ L (a :: u) /\ star L v) ->
    star L (a :: w).
  Proof.
    move=> [u [v [-> [Hu Hv]]]].
    have [ys [Hys [Hflat Hall]]] := starP Hv.

    have Hspl : ((a :: u) :: ys) \in splits ((a :: u) ++ v).
    { apply: (splits_head_cat (u:=(a :: u)) (v:=v) (ys:=ys)).
      - by [].
      - exact Hys. }
    have Hspl' : ((a :: u) :: ys) \in splits (a :: (u ++ v)).
    { by rewrite cat_cons in Hspl. }

    apply: (starP_inv (xs := (a :: u) :: ys)).
    - exact Hspl'.
    - have Hfv : flatten_words ys = v.
      { by move/eqP: Hflat. }
      rewrite /= Hfv.
      by rewrite eqxx.
    - apply/andP; split.
      + exact Hu.
      + exact Hall.
  Qed.


  Lemma star_eps : star eps =i eps.
  Proof.
    move=> w; case: w => [|a w].
    - by rewrite /star /eps /splits /= /flatten_words /all_in.
    - rewrite /star /eps /=.
      apply/negP => /hasP [xs Hxs /andP [_ Hall]].
      have [t [ys Hshape]] := splits_cons_shape Hxs.
      by move: Hall; rewrite Hshape /= /eps.
  Qed.

  Lemma star_void : star void =i eps.
  Proof.
    move=> w; case: w => [|a w].
    - by rewrite /star /void /eps /splits /= /flatten_words /all_in.
    - rewrite /star /void /eps /=.
      apply/negP => /hasP [xs Hxs /andP [_ Hall]].
      have [t [ys Hshape]] := splits_cons_shape Hxs.
      by move: Hall; rewrite Hshape /= /void.
  Qed.

End Lang.

End Languages.
Export Languages.
