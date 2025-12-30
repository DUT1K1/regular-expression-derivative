From Coq Require Import List.
Import ListNotations.

Section Derivative_DFA_Main_Theorem.

    Variable Sigma : Type.
    Definition word := list Sigma.

    Parameter regex : Type.
    
    (**re_lang r w means that word is in lang denoted by r *)
    Parameter re_lang : regex -> word -> Prop.

    Parameter deriv : regex -> Sigma -> regex.

    Parameter nullable : regex -> Prop.

    Axiom nullable_correct :
        forall r : regex,
        nullable r <-> re_lang r [].


    Axiom deriv_correct :
        forall (r : regex) (a : Sigma) (w : word),
        re_lang (deriv r a) w <-> re_lang r (a :: w).


    Record dfa := {
        Q    : Type;                      (* set of states *)
        q0   : Q;                         (* start state *)
        delta : Q -> Sigma -> Q;          (* transition function δ *)
        F    : Q -> Prop                  (* accepting states predicate *)
    }.

    (** Construction: DFA from a regular expression r*)
    Definition derivative_dfa (r : regex) : dfa := {|
        Q    := regex;
        q0   := r;
        delta := fun q a => deriv q a;
        F    := nullable
    |}.


    (** Extended transition function δ* : Q × Σ* → Q
        δ*(q, ε)   = q
        δ*(q, wa)  = δ(δ*(q, w), a)
    *)
    (** Q M is current state or a staet we end up in*)
    Fixpoint delta_star (M : dfa) (q : Q M) (w : word) : Q M :=
        match w with
        | [] => q
        | a :: w' => delta_star M (delta M q a) w'
    end.


    (** Acceptance: w is accepted by M  ⇔  δ*(q0, w) ∈ F. *)
    (** F M (q) means q is accepting*)
    Definition accepts (M : dfa) (w : word) : Prop :=
        F M (delta_star M (q0 M) w).


    (** Derivative w.r.t. a whole word (syntactic D_w(r)):
            D_ε(r)    = r
            D_{a::u}(r) = D_u(D_a(r))
    *)
    Fixpoint deriv_word (r : regex) (w : word) : regex :=
        match w with
        | [] => r
        | a :: w' => deriv_word (deriv r a) w'
        end.


    (** Helper lemma for concat unfolding *)
    Lemma concat_helper :
        forall (a : Sigma) (u v : word),
        (a :: u) ++ v = a :: (u ++ v).
    Proof. reflexivity. Qed.


    (** Semantic characterization of D_w(r):
            L(deriv_word r u) = { v | u ++ v ∈ L(r) }
            i.e. re_lang (deriv_word r u) v  <->  re_lang r (u ++ v).
    *)
    Lemma deriv_word_correct :
        forall (r : regex) (u v : word),
        re_lang (deriv_word r u) v <-> re_lang r (u ++ v).
    Proof.
        intros r u; revert r.
        induction u as [| a u' IH]; intros r v.
        - (* u = [] *)
        simpl. (* deriv_word r [] = r, [] ++ v = v *)
        split; intro H; assumption.
        - (* u = a :: u' *)
        simpl. (* deriv_word r (a :: u') = deriv_word (deriv r a) u' *)
        specialize (IH (deriv r a) v).
        (* IH : re_lang (deriv_word (deriv r a) u') v
                <-> re_lang (deriv r a) (u' ++ v) *)
        rewrite IH.
        (* Now we have:
            re_lang (deriv r a) (u' ++ v)
            <-> re_lang r ((a :: u') ++ v)
            after using deriv_correct and list algebra. *)
        rewrite deriv_correct.
        (* re_lang r (a :: (u' ++ v)) *)
        rewrite <- concat_helper.
        (* re_lang r ((a :: u') ++ v) *)
        reflexivity.
    Qed.

    (** delta_star and deriv_word coincide for the derivative-based DFA:
            δ*_{M_r}(r, w) = D_w(r)
        where M_r = derivative_dfa r.
    *)
    Lemma delta_star_deriv_word :
    forall (r : regex) (q : regex) (w : word),
        delta_star (derivative_dfa r) q w = deriv_word q w.
    Proof.
    intros r q w; revert q.
    induction w as [| a w' IH]; intros q; simpl.
    - (* w = [] *)
        reflexivity.
    - (* w = a :: w' *)
        (* goal: delta_star (derivative_dfa r) (deriv q a) w'
                = deriv_word (deriv q a) w' *)
        apply IH.
    Qed.


    (** Main theorem: the DFA built from r recognizes exactly L(r). *)
    Theorem dfa_correctness :
        forall (r : regex) (w : word),
        accepts (derivative_dfa r) w <-> re_lang r w.
    Proof.
    intros r w.
    unfold accepts.
    simpl.  (* unfold derivative_dfa: q0 = r, F = nullable *)
    rewrite (delta_star_deriv_word r r w).
    (* Goal: nullable (deriv_word r w) <-> re_lang r w *)
    rewrite nullable_correct.
    (* Goal: re_lang (deriv_word r w) [] <-> re_lang r w *)
    pose proof (deriv_word_correct r w []) as H.
    rewrite app_nil_r in H.  
    exact H.
    Qed.

    
End Derivative_DFA_Main_Theorem.

