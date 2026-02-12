From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import RegexSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Nullable (X : OSYM).

  Module Export RS := RegexSemantics X.
  Import X.

  Fixpoint has_eps (r : regex) : bool :=
    match r with
    | Empty       => false
    | Eps         => true
    | Char _      => false
    | Alt r1 r2   => has_eps r1 || has_eps r2
    | And r1 r2   => has_eps r1 && has_eps r2
    | Seq r1 r2   => has_eps r1 && has_eps r2
    | Star _      => true
    | Neg r1      => ~~ has_eps r1
    end.

  Definition nullable := has_eps.

  Definition nu (r : regex) : regex :=
    if has_eps r then Eps else Empty.

  Lemma bool_true_eq (b : bool) : b -> b = true.
  Proof. by case: b. Qed.

  Lemma nullable_correct : forall r, has_eps r = ([::] \in r).
  Proof.
    elim=> /=.
    - by [].
    - by [].
    - by move=> a.
    - move=> r1 IH1 r2 IH2; by rewrite IH1 IH2.
    - move=> r1 IH1 r2 IH2.
      rewrite IH1 IH2.
      change (([::] \in r1) && ([::] \in r2) =
              conc (den r1) (den r2) [::]).
      by rewrite /conc (regexderiv.Languages.Languages.conc_nil (A:=A) (den r1) (den r2)).
    - move=> r IH.
      have H : star (den r) [::] := regexderiv.Languages.Languages.star_nil (A:=A) (den r).
      by rewrite -(bool_true_eq H).
    - move=> r1 IH1 r2 IH2; by rewrite IH1 IH2.
    - move=> r IH; by rewrite IH.
  Qed.

  Lemma mem_nu (r : regex) (w : word) :
    (w \in nu r) = (w == [::]) && has_eps r.
  Proof.
    rewrite /nu; case E: (has_eps r) => /=.
    - (* nu r = Eps *)
      by rewrite /eps andbT.
    - (* nu r = Empty *)
      by rewrite /void andbF.
  Qed.

End Nullable.
