From Stdlib Require Import Ascii List Bool.
Import ListNotations.
Export ListNotations.

(* A word is a finite list of symbols from Σ (here: ASCII) *)
Definition word := list ascii.

Inductive regex : Type :=
| Empty   : regex                      (* ∅ : empty language *)
| Epsilon : regex                      (* ε : language {ε} *)
| Char    : ascii -> regex             (* a ∈ Σ : singleton {a} *)
| Alt     : regex -> regex -> regex    (* r + s : union *)
| And     : regex -> regex -> regex    (* r & s : intersection *)
| Seq     : regex -> regex -> regex    (* r · s : concatenation *)
| Star    : regex -> regex             (* r* : Kleene star *)
| Neg     : regex -> regex.            (* ¬r : complement *)

(* Union: ∅ is neutral (∅ + r = r). Otherwise keep Alt. *)
Definition alt (r1 r2 : regex) : regex :=
  match r1, r2 with
  | Empty, r | r, Empty => r
  | _, _ => Alt r1 r2
  end.


(* Intersection: ∅ is absorbing (∅ & r = ∅). Otherwise keep And. *)
Definition and_ (r1 r2 : regex) : regex :=
  match r1, r2 with
  | Empty, _ | _, Empty => Empty
  | _, _ => And r1 r2
  end.

(* Concatenation: ∅ is absorbing; ε is neutral (ε·r = r = r·ε). *)
Definition cat (r1 r2 : regex) : regex :=
  match r1, r2 with
  | Empty, _ | _, Empty => Empty
  | Epsilon, r | r, Epsilon => r
  | _, _ => Seq r1 r2
  end.

(* Star: ∅* = ε and ε* = ε; collapse nested stars. *)
Definition star (r : regex) : regex :=
  match r with
  | Empty | Epsilon => Epsilon
  | Star r' => Star r'
  | _ => Star r
  end.

(* Complement: push negation using De Morgan; eliminate double negation. *)
Definition neg(r : regex) : regex :=
  match r with
  | Neg r' => r'
  | Alt r1 r2 => and_ (Neg r1) (Neg r2)
  | And r1 r2 => alt (Neg r1) (Neg r2)
  | _ => Neg r
  end.

Fixpoint nullable (r : regex) : bool :=
  match r with
  | Empty        => false                      (* ε ∉ ∅ *)
  | Epsilon      => true                       (* ε ∈ {ε} *)
  | Char _       => false                      (* ε ∉ {a} *)
  | Alt r1 r2    => nullable r1 || nullable r2 (* ε ∈ L(r1) ∪ L(r2) *)
  | And r1 r2    => nullable r1 && nullable r2 (* ε ∈ L(r1) ∩ L(r2) *)
  | Seq r1 r2    => nullable r1 && nullable r2 (* ε ∈ L(r1)·L(r2) *)
  | Star _       => true                       (* ε ∈ L(r) *)
  | Neg r1       => negb (nullable r1)         (* ε ∈ ¬L(r) iff ε ∉ L(r) *)
  end.

(* Regex-valued ν(r): (returns ε or ∅)*)
Definition nu (r : regex) : regex :=
  if nullable r then Epsilon else Empty.


(* ------------------------------------------------------------------ *)
(* Semantics of regular expressions                                    *)
(* ------------------------------------------------------------------ *)

(* A language over Σ is represented as a membership predicate on words. *)
Definition language := word -> Prop.

(* Inductive (least) definition of Kleene star for an arbitrary language L.
   - star_nil: ε is in L*.
   - star_app: if u ∈ L and v ∈ L* then u ++ v ∈ L*.
   Here "++" is list (word) concatenation. *)
Inductive star_lang (L : language) : language :=
| star_nil  : star_lang L []
| star_app  : forall u v, L u -> star_lang L v -> star_lang L (u ++ v).

(*Lang maps a regex to its language, i.e. a predicate that,
given a word, says whether that word is denoted by the regex.*)
Fixpoint Lang (r : regex) : language :=
  match r with
  | Empty     =>
      (* ∅ : no word is a member *)
      fun _ => False
  | Epsilon   =>
      (* {ε} : only the empty word is a member *)
      fun w => w = []
  | Char a    =>
      (* {a} : only the one-symbol word [a] is a member *)
      fun w => w = [a]
  | Alt r s   =>
      (* r + s : union of languages *)
      fun w => Lang r w \/ Lang s w
  | And r s   =>
      (* r & s : intersection of languages *)
      fun w => Lang r w /\ Lang s w
  | Seq r s   =>
      (* r · s : concatenation; w splits as u ++ v with u ∈ Lang r and v ∈ Lang s *)
      fun w => exists u v, w = u ++ v /\ Lang r u /\ Lang s v
  | Star r    =>
      (* r* : Kleene star of Lang r *)
      star_lang (Lang r)
  | Neg r     =>
      (* ¬r : complement of Lang r (relative to all words) *)
      fun w => ~ Lang r w
  end.

(* ------------------------------------------------------------------ *)
(* Derivative on languages - Semantic                                 *)
(* ------------------------------------------------------------------ *)

(*Semantic derivative with respect to a single character*)
Definition dlang_char (a : ascii) (L : language) : language :=
  fun w => L (a :: w).

(*Semantic derivative with respect to a word*)
Fixpoint dlang (u : word) (L : language) : language :=
  match u with
  | []     => L
  | a :: v => dlang v (dlang_char a L)
  end.

(* ------------------------------------------------------------------ *)
(* Derivative on regex - Syntactic                                    *)
(* ------------------------------------------------------------------ *)

Definition ascii_eq_dec := Ascii.ascii_dec.

(*Syntactic derivative with respect to a single character*)
Fixpoint D_char (a : ascii) (r : regex) : regex :=
  match r with
  | Empty      => Empty   (* D_a(∅) = ∅ : no word in ∅ starts with a *)
  | Epsilon    => Empty   (* D_a({ε}) = ∅ : ε does not start with a *)
  | Char c     => if ascii_eq_dec a c then Epsilon else Empty    (* D_a({c}) = {ε} if a = c, else ∅ *)
  | Alt r s    => Alt (D_char a r) (D_char a s)    (* D_a(r + s) = D_a(r) + D_a(s) : derivative distributes over union *)
  | And r s    => And (D_char a r) (D_char a s)    (* D_a(r & s) = D_a(r) & D_a(s) : derivative distributes over intersection *)
  | Seq r s    => Alt (Seq (D_char a r) s) (Seq (nu r) (D_char a s))
      (* Concatenation rule:
         D_a(r · s) = D_a(r) · s  +  ν(r) · D_a(s)
         - First term: a is consumed by the left factor r, remainder must still match s.
         - Second term: if r is nullable (ν(r)=ε), a can be consumed by s. *)
  | Star r     => Seq (D_char a r) (Star r)     (* D_a(r* = D_a(r) · r* : first block comes from r, rest stays in r* *)
  | Neg r      => Neg (D_char a r)       (* D_a(¬r) = ¬(D_a(r)) : complement commutes with left quotient *)
  end.

(*Syntactic derivative with respect to a word*)
Fixpoint D (u : word) (r : regex) : regex :=
  match u with
  | []     => r
  | a :: v => D v (D_char a r)
  end.

(* ------------------------------------------------------------------ *)
(* Nullability correctness                                             *)
(* ------------------------------------------------------------------ *)

(* nullable_correct: the boolean test nullable r is true exactly when r accepts ε
   (i.e., Lang r [] holds).
   so when nullable r is true language denoted by r contains the empty word *)
Lemma nullable_correct : forall r, nullable r = true <-> Lang r [].
Proof.
  induction r; simpl. (*divide iff into two goals*)
  (*r = Empyy | nullable Empty = true -> Lang Empty [], false = true, discriminate solves impossible equalities
  Lang Empty [] is False. and inversion closes contradictions| *)
  - split; [discriminate | intro H; inversion H].
  (*r = Epsilon, trivial true = true*)
  - split; [reflexivity | intro H; now subst].
  (*r = Char _*)
  - split; [discriminate | intro H; inversion H].
  - (* Alt *)
    rewrite Bool.orb_true_iff.
    split.
    + intros [H|H]; [left; apply IHr1 in H | right; apply IHr2 in H]; assumption.
    + intros [Hr|Hs]; [left; apply (proj2 IHr1) in Hr | right; apply (proj2 IHr2) in Hs]; assumption.
  - (* And *)
    rewrite Bool.andb_true_iff.
    split.
    + intros [H1 H2]; split; [apply IHr1 in H1 | apply IHr2 in H2]; assumption.
    + intros [Hr Hs]; split; [apply (proj2 IHr1) in Hr | apply (proj2 IHr2) in Hs]; assumption.
  - (* Seq *)
    rewrite Bool.andb_true_iff.
    split.
    + intros [H1 H2].
      apply IHr1 in H1. apply IHr2 in H2.
      exists [], []; repeat split; auto.
    + intros [u [v [Huv [Hu Hv]]]].
      symmetry in Huv.
      apply app_eq_nil in Huv as [-> ->].
      split; [apply (proj2 IHr1) in Hu | apply (proj2 IHr2) in Hv]; assumption.
    - (* Star *)
    split.
    + intros _. constructor.
    + intros _. reflexivity.
  - (* Neg *)
    rewrite Bool.negb_true_iff.
    split.
    + intros Hneg Hr. apply (proj2 IHr) in Hr. now rewrite Hr in Hneg.
    + intro Hnot. destruct (nullable r) eqn:E.
      * exfalso. apply Hnot. apply (proj1 IHr). reflexivity.
      * reflexivity.
Qed.
