From mathcomp Require Import ssreflect ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A plain alphabet of symbols. This is the minimal interface needed for
   words, languages, regular-expression syntax, and semantics. *)
Module Type SYM.
  Parameter A : eqType.
End SYM.

(* A plain alphabet plus an ordering on symbols. This is not part of the paper's
   basic alphabet definition; it is only needed to sort symbols while building
   canonical regular expressions. *)
Module Type OSYM.
  Include SYM.

  Parameter cmpA : A -> A -> comparison.

  Axiom cmpA_eq_axiom : forall a b, reflect (a = b)
    (if cmpA a b is Eq then true else false).
End OSYM.

(* A finite nonempty alphabet. Enumerates all symbols exactly once. *)
Module Type FINSYM.
  Include SYM.

  Parameter alphabet : seq A.

  Axiom alphabet_uniq : uniq alphabet.
  Axiom alphabet_nonempty : alphabet != [::].
  Axiom alphabet_complete : forall a : A, a \in alphabet.
End FINSYM.

(* A finite alphabet that also has an ordering on symbols. Automata construction
   uses the finite list to enumerate transitions and canonicalization uses the
   comparison to sort regular expressions. *)
Module Type OFINSYM.
  Include FINSYM.

  Parameter cmpA : A -> A -> comparison.

  Axiom cmpA_eq_axiom : forall a b, reflect (a = b)
    (if cmpA a b is Eq then true else false).
End OFINSYM.
