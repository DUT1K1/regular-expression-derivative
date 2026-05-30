From mathcomp Require Import ssreflect ssrbool eqtype seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import Languages.
From regexderiv Require Import RegexSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Nullable (X : SYM).

  Module Export RS := RegexSemantics X.
  Import X.

  (* Boolean test for whether ε belongs to the language of a regex. *)
  Fixpoint has_eps (r : regex) : bool :=
    match r with
    | Empty       => false
    | Eps         => true
    | Char _      => false
    | Alt r1 r2   => has_eps r1 || has_eps r2
    | Seq r1 r2   => has_eps r1 && has_eps r2
    | Star _      => true
    | And r1 r2   => has_eps r1 && has_eps r2
    | Neg r1      => ~~ has_eps r1
    end.

  (* The ν function returns ε when the regex is nullable, and ∅ otherwise. *)
  Definition nu (r : regex) : regex :=
    if has_eps r then Eps else Empty.

  (* The boolean test has_eps r agrees with the semantic definition of nullable [::] \in r. *)
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
      by rewrite /conc (Languages.conc_nil (A:=A) (den r1) (den r2)).
    - move=> r IH.
      have H : star (den r) [::] := Languages.star_nil (A:=A) (den r).
      by case: (star (den r) [::]) H.
    - move=> r1 IH1 r2 IH2; by rewrite IH1 IH2.
    - move=> r IH; by rewrite IH.
  Qed.

  (* Membership in nu r holds exactly for the empty word, and only when r is nullable. *)
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
