From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Alphabet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type OFINSYM.
  Include OSYM.

  Parameter alphabet : seq A.

  Axiom alphabet_uniq : uniq alphabet.
  Axiom alphabet_complete : forall a : A, a \in alphabet.

End OFINSYM.
