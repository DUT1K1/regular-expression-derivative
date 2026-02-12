From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import RegexSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Canonicalization (X : OSYM).
  Import X.

  Module Export RS := RegexSemantics X.

  Definition isEmpty (r : regex) : bool :=
    match r with Empty => true | _ => false end.

  Definition isEps (r : regex) : bool :=
    match r with Eps => true | _ => false end.

  Definition Top : regex := Neg Empty.

  Definition isTop (r : regex) : bool :=
    match r with
    | Neg Empty => true
    | _ => false
    end.


  Definition tag (r : regex) : nat :=
    match r with
    | Empty     => 0
    | Eps       => 1
    | Char _    => 2
    | Star _    => 3
    | Seq _ _   => 4
    | And _ _   => 5
    | Alt _ _   => 6
    | Neg _     => 7
    end.

  Fixpoint cmpR (r s : regex) : comparison :=
    match r, s with
    | Empty, Empty => Eq
    | Eps,   Eps   => Eq
    | Char a, Char b => cmpA a b
    | Star r1, Star s1 => cmpR r1 s1
    | Neg  r1, Neg  s1 => cmpR r1 s1

    | Seq r1 r2, Seq s1 s2 =>
        let c := cmpR r1 s1 in if c is Eq then cmpR r2 s2 else c
    | And r1 r2, And s1 s2 =>
        let c := cmpR r1 s1 in if c is Eq then cmpR r2 s2 else c
    | Alt r1 r2, Alt s1 s2 =>
        let c := cmpR r1 s1 in if c is Eq then cmpR r2 s2 else c

    | _, _ =>
        let tr := tag r in
        let ts := tag s in
        if tr < ts then Lt else if ts < tr then Gt else Eq
    end.

  Definition leR (r s : regex) : bool :=
    match cmpR r s with Gt => false | _ => true end.

  Definition eqR (r s : regex) : bool :=
    match cmpR r s with Eq => true | _ => false end.


  Fixpoint insertR (r : regex) (xs : seq regex) : seq regex :=
    match xs with
    | [::] => [:: r]
    | x :: xs' => if leR r x then r :: x :: xs' else x :: insertR r xs'
    end.

  Fixpoint sortR (xs : seq regex) : seq regex :=
    match xs with
    | [::] => [::]
    | x :: xs' => insertR x (sortR xs')
    end.

  Fixpoint dedup_adj (xs : seq regex) : seq regex :=
    match xs with
    | [::] => [::]
    | x :: xs' =>
        match xs' with
        | [::] => [:: x]
        | y :: zs =>
            if eqR x y then dedup_adj xs'
            else x :: dedup_adj xs'
        end
    end.


  Fixpoint plus_terms (r : regex) : seq regex :=
    match r with
    | Alt r1 r2 => plus_terms r1 ++ plus_terms r2
    | _ => [:: r]
    end.

  Fixpoint and_terms (r : regex) : seq regex :=
    match r with
    | And r1 r2 => and_terms r1 ++ and_terms r2
    | _ => [:: r]
    end.

  Fixpoint conc_terms (r : regex) : seq regex :=
    match r with
    | Seq r1 r2 => conc_terms r1 ++ conc_terms r2
    | _ => [:: r]
    end.


  Fixpoint mkPlus_list (xs : seq regex) : regex :=
    match xs with
    | [::] => Empty
    | [:: r] => r
    | r :: rs => Alt r (mkPlus_list rs) (* right-associated *)
    end.

  Fixpoint mkAnd_list (xs : seq regex) : regex :=
    match xs with
    | [::] => Top
    | [:: r] => r
    | r :: rs => And r (mkAnd_list rs) (* right-associated *)
    end.

  Fixpoint mkConc_list (xs : seq regex) : regex :=
    match xs with
    | [::] => Eps
    | [:: r] => r
    | r :: rs => Seq r (mkConc_list rs) (* right-associated *)
    end.


  Definition mkPlus (r s : regex) : regex :=
    let xs := plus_terms r ++ plus_terms s in
    let xs := filter (fun t => ~~ isEmpty t) xs in  (* E + ∅ = E *)
    let xs := dedup_adj (sortR xs) in               (* AC + idempotent *)
    mkPlus_list xs.

  Definition mkAnd (r s : regex) : regex :=
    let xs := and_terms r ++ and_terms s in
    if has isEmpty xs then Empty else               (* E & ∅ = ∅ *)
    let xs := filter (fun t => ~~ isTop t) xs in    (* E & Top = E *)
    let xs := dedup_adj (sortR xs) in               (* AC + idempotent *)
    mkAnd_list xs.

  Definition mkConc (r s : regex) : regex :=
    let xs := conc_terms r ++ conc_terms s in
    if has isEmpty xs then Empty else               (* ∅ · E = ∅, E · ∅ = ∅ *)
    let xs := filter (fun t => ~~ isEps t) xs in    (* ε · E = E, E · ε = E *)
    mkConc_list xs.                                 (* assoc normalized *)

  Definition mkStar (r : regex) : regex :=
    match r with
    | Empty => Eps                                  (* ∅* = ε *)
    | Eps   => Eps                                  (* ε* = ε *)
    | Star r' => Star r'                             (* star(star r) = star r *)
    | _ => Star r
    end.

  Definition mkNot (r : regex) : regex :=
    match r with
    | Empty => Top                                  (* ¬∅ = Top *)
    | Neg r' => r'                                  (* ¬¬r = r; also ¬Top = ∅ *)
    | _ => Neg r
    end.


  Fixpoint canonize (r : regex) : regex :=
    match r with
    | Empty => Empty
    | Eps   => Eps
    | Char a => Char a
    | Alt r1 r2 => mkPlus (canonize r1) (canonize r2)
    | And r1 r2 => mkAnd  (canonize r1) (canonize r2)
    | Seq r1 r2 => mkConc (canonize r1) (canonize r2)
    | Star r1   => mkStar (canonize r1)
    | Neg r1    => mkNot  (canonize r1)
    end.

      Fixpoint eq_regex (r s : regex) : bool :=
    match r, s with
    | Empty, Empty => true
    | Eps,   Eps   => true
    | Char a, Char b => a == b
    | Alt r1 r2, Alt s1 s2 => eq_regex r1 s1 && eq_regex r2 s2
    | And r1 r2, And s1 s2 => eq_regex r1 s1 && eq_regex r2 s2
    | Seq r1 r2, Seq s1 s2 => eq_regex r1 s1 && eq_regex r2 s2
    | Star r1, Star s1 => eq_regex r1 s1
    | Neg  r1, Neg  s1 => eq_regex r1 s1
    | _, _ => false
    end.

  Definition same_syntax (r s : regex) : bool :=
    eq_regex r s.

  Definition same_after_canon (r s : regex) : bool :=
    eq_regex (canonize r) (canonize s).

  Definition different_but_canon_same (r s : regex) : bool :=
    ~~ same_syntax r s && same_after_canon r s.


End Canonicalization.
