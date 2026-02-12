From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import RegexSemantics.
From regexderiv Require Import Nullable.
From regexderiv Require Import Languages.
From regexderiv Require Import Derivatives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------------------------------------------------ *)
(* A concrete alphabet: {a,b,c}                                 *)
(* ------------------------------------------------------------ *)

Module ABC.

Inductive sym := a | b | c.

Definition sym_eq (x y : sym) : bool :=
  match x, y with
  | a, a => true | b, b => true | c, c => true
  | _, _ => false
  end.

Lemma sym_eqP : Equality.axiom sym_eq.
Proof. by do 2 case; constructor. Qed.

Canonical sym_eqMixin := Equality.Mixin sym_eqP.
Canonical sym_eqType := Equality.Pack (Equality.Class sym_eqMixin).

Definition A := sym_eqType.

Definition cmpA (x y : A) : comparison :=
  match x, y with
  | a, a | b, b | c, c => Eq
  | a, _ => Lt
  | b, a => Gt
  | b, c => Lt
  | c, _ => Gt
  end.

End ABC.

Module X <: OSYM.
  Definition A := ABC.A.
  Definition cmpA := ABC.cmpA.

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
End X.

Module D := Derivatives X.
Import X D.

(* shorthand symbols *)
Definition aa : A := ABC.a.
Definition bb : A := ABC.b.
Definition cc : A := ABC.c.

(* words *)
Definition w0  : word := [::].
Definition wa  : word := [:: aa].
Definition wb  : word := [:: bb].
Definition wab : word := [:: aa; bb].
Definition wba : word := [:: bb; aa].

(* regexes *)
Definition r_ab     : regex := Seq (Char aa) (Char bb).
Definition r_a_or_b : regex := Alt (Char aa) (Char bb).
Definition r_star   : regex := Star r_a_or_b.

(* ------------------------------------------------------------ *)
(* Membership tests                                             *)
(* ------------------------------------------------------------ *)

Compute (wab \in r_ab).   (* expected: true *)
Compute (wba \in r_ab).   (* expected: false *)
Compute (wa  \in r_a_or_b). (* true *)
Compute (wb  \in r_a_or_b). (* true *)
Compute (w0  \in r_a_or_b). (* false *)

Compute (w0  \in r_star).   (* true: star always has epsilon *)
Compute (wa  \in r_star).   (* true *)
Compute (wab \in r_star).   (* true *)

(* ------------------------------------------------------------ *)
(* Derivatives (structure + membership)                         *)
(* ------------------------------------------------------------ *)

Compute (D_char aa r_ab).     (* should simplify to (Char bb) essentially *)
Compute (D_char bb r_ab).     (* should be Empty *)
Compute (D wa r_ab).          (* word derivative by "a" *)

(* checks of correctness equalities (compute to true) *)
Compute (((w0 \in D_char aa r_ab) == ((aa :: w0) \in r_ab))).
Compute (((wb \in D wa r_ab) == ((wa ++ wb) \in r_ab))).

(* ------------------------------------------------------------ *)
(* Semantic derivatives on languages (using den r)                *)
(* ------------------------------------------------------------ *)

Definition L_ab : language := den r_ab.

Compute (dlang_char aa L_ab wb).  (* true: "a"++"b" is "ab" *)
Compute (dlang wa L_ab wb).       (* same as above *)
Compute (dlang wb L_ab w0).       (* false: "b" not prefix of "ab" *)
