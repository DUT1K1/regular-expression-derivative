From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import Languages.
From regexderiv Require Import RegexSemantics.
From regexderiv Require Import Nullable.
From regexderiv Require Import Derivatives.
From regexderiv Require Import Canonicalization.
From regexderiv Require Import CanonicalizationCorrectness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Automata (X : OSYM).
  Import X.

  Module Export D := Derivatives X.
  Module CC := CanonicalizationCorrectness X.


  Fixpoint to_c_regex (r : regex) : CC.C.RS.regex :=
    match r with
    | Empty      => CC.C.RS.Empty
    | Eps        => CC.C.RS.Eps
    | Char a     => CC.C.RS.Char a
    | Alt r1 r2  => CC.C.RS.Alt (to_c_regex r1) (to_c_regex r2)
    | Seq r1 r2  => CC.C.RS.Seq (to_c_regex r1) (to_c_regex r2)
    | Star r1    => CC.C.RS.Star (to_c_regex r1)
    | And r1 r2  => CC.C.RS.And (to_c_regex r1) (to_c_regex r2)
    | Neg r1     => CC.C.RS.Neg (to_c_regex r1)
    end.

  Fixpoint from_c_regex (r : CC.C.RS.regex) : regex :=
    match r with
    | CC.C.RS.Empty      => Empty
    | CC.C.RS.Eps        => Eps
    | CC.C.RS.Char a     => Char a
    | CC.C.RS.Alt r1 r2  => Alt (from_c_regex r1) (from_c_regex r2)
    | CC.C.RS.Seq r1 r2  => Seq (from_c_regex r1) (from_c_regex r2)
    | CC.C.RS.Star r1    => Star (from_c_regex r1)
    | CC.C.RS.And r1 r2  => And (from_c_regex r1) (from_c_regex r2)
    | CC.C.RS.Neg r1     => Neg (from_c_regex r1)
    end.

  Lemma to_c_regex_correct (r : regex) (w : word) :
    CC.C.RS.den (to_c_regex r) w = (w \in r).
  Proof.
    elim: r w => [| |a |r1 IH1 r2 IH2 |r1 IH1 r2 IH2 |r IH |r1 IH1 r2 IH2 |r IH] w //=.
    - exact: (congr2 orb (IH1 w) (IH2 w)).
    - exact: (Languages.conc_ext (A:=A) IH1 IH2 w).
    - exact: (Languages.star_ext (A:=A) IH w).
    - exact: (congr2 andb (IH1 w) (IH2 w)).
    - exact: (congr1 negb (IH w)).
  Qed.

  Lemma from_c_regex_correct (r : CC.C.RS.regex) (w : word) :
    (w \in from_c_regex r) = CC.C.RS.den r w.
  Proof.
    elim: r w => [| |a |r1 IH1 r2 IH2 |r1 IH1 r2 IH2 |r IH |r1 IH1 r2 IH2 |r IH] w //=.
    - exact: (congr2 orb (IH1 w) (IH2 w)).
    - exact: (Languages.conc_ext (A:=A) IH1 IH2 w).
    - exact: (Languages.star_ext (A:=A) IH w).
    - exact: (congr2 andb (IH1 w) (IH2 w)).
    - exact: (congr1 negb (IH w)).
  Qed.

  Definition canonize (r : regex) : regex :=
    from_c_regex (CC.C.canonize (to_c_regex r)).

  Definition eq_regex (r s : regex) : bool :=
    CC.C.eq_regex (to_c_regex r) (to_c_regex s).

  Lemma canonize_correct_local (r : regex) (w : word) :
    (w \in canonize r) = (w \in r).
  Proof.
    rewrite /canonize from_c_regex_correct.
    have Hc : CC.C.RS.den (CC.C.canonize (to_c_regex r)) w =
              CC.C.RS.den (to_c_regex r) w.
    exact: (CC.canonize_correct (to_c_regex r) w).
    rewrite Hc.
    exact: to_c_regex_correct.
  Qed.

  (*
    ------------------------------------------------------------
      M = <Q, Sigma, delta, q0, F>
    ------------------------------------------------------------
  *)
  Record dfa := {
    Q     : Type;
    q0    : Q;
    delta : Q -> A -> Q;
    F     : Q -> bool
  }.

  Arguments q0 : clear implicits.
  Arguments delta : clear implicits.
  Arguments F : clear implicits.

  (*
    Extension of delta to words.
  *)
  Fixpoint delta_star (M : dfa) (q : Q M) (w : word) : Q M :=
    if w is a :: w' then @delta_star M (@delta M q a) w' else q.

  Arguments delta_star : clear implicits.

  Definition accepts (M : dfa) (w : word) : bool :=
    F M (delta_star M (q0 M) w).

  Definition dfa_lang (M : dfa) : language :=
    fun w => accepts M w.


  Definition constructed_dfa (r : regex) : dfa :=
    {| Q     := regex;
       q0    := canonize r;
       delta := fun q a => canonize (D_char a q);
       F     := has_eps |}.

  (*
    After reading u, the reached state accepts exactly the suffixes v
    such that the original regex q accepts u ++ v.
  *)
  Lemma delta_star_constructed_lang (r q : regex) (u v : word) :
    (v \in delta_star (constructed_dfa r) q u) =
    ((u ++ v) \in q).
  Proof.
    elim: u q v => [|a u IH] q v //=.
    rewrite IH.
    rewrite canonize_correct_local.
    exact: D_char_correct.
  Qed.

  (*
    After reading u from the start state, the reached DFA state denotes
    the same language as the derivative D u r.
  *)
  Theorem delta_star_constructed_derivative_equiv (r : regex) (u : word) :
    delta_star (constructed_dfa r) (q0 (constructed_dfa r)) u ≈ D u r.
  Proof.
    move=> v.
    rewrite (delta_star_constructed_lang r (canonize r) u v).
    rewrite canonize_correct_local.
    exact: (esym (D_correct u r v)).
  Qed.

  (*
      L(M) = L(r)
  *)
  Theorem dfa_correctness (r : regex) :
    dfa_lang (constructed_dfa r) ≡ den r.
  Proof.
    move=> u.
    change (has_eps (delta_star (constructed_dfa r) (q0 (constructed_dfa r)) u) =
            (u \in r)).
    rewrite nullable_correct.
    rewrite (delta_star_constructed_lang r (canonize r) u [::]).
    rewrite cats0.
    exact: canonize_correct_local.
  Qed.


End Automata.
