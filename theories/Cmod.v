From Coq Require Import Sint63.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Verith Require Import ZDivides.

Open Scope Z.

(* This file describes the properrties of cmod, which is very 
annoying to unfold as it spreads "wB/2" expressions everywhere.
The theorems proven here should therefore be used as blackbox
utilities to avoid dealing with the internals of cmod directly. *)

Lemma wb0 : wB > 0. (* comes up a lot because of div_is_mod *)
Proof.
    unfold wB, size. lia.
Qed.

Theorem cmod_means_mod : forall a b, cmod a wB = cmod b wB <-> a mod wB = b mod wB.
Proof.
    split; intros H.
    - unfold cmod in H.
        assert (((a + wB / 2) mod wB) = (b + wB / 2) mod wB) by lia.
        clear H.
        apply div_is_mod in H0.
        replace (b + wB / 2 - (a + wB / 2)) with (b - a) in H0 by lia.
        apply div_is_mod. apply wb0.
        assumption.
        apply wb0.
    - unfold cmod.
        f_equal.
        apply div_is_mod. exact wb0.
        replace (b + wB / 2 - (a + wB / 2)) with (b - a) by lia.
        apply div_is_mod. exact wb0.
        assumption.
Qed.

Theorem cmod_idempotent : forall a, cmod (cmod a wB) wB = cmod a wB.
Proof.
    intros.
    apply cmod_means_mod.
    unfold cmod.
    rewrite Zminus_mod_idemp_l.
    f_equal.
    lia.
Qed. 

Lemma cmod_add_l : forall a b, cmod (cmod a wB + b) wB = cmod (a + b) wB.
Proof.
    intros.
    unfold cmod.
    rewrite <- Z.add_assoc.
    rewrite Z.sub_cancel_r.
    replace (((a + wB / 2) mod wB - wB / 2 + (b + wB / 2))) 
        with ((a + wB / 2) mod wB + b) by lia.
    rewrite Zplus_mod_idemp_l.
    f_equal.
    lia.
Qed.

Lemma cmod_add_r : forall a b, cmod (b + cmod a wB) wB = cmod (b + a) wB.
Proof.
    intros. 
    rewrite Z.add_comm.
    rewrite cmod_add_l.
    f_equal. 
    lia.
Qed.

Lemma cmod_mul_l : forall a b, cmod (cmod a wB * b) wB = cmod (a * b) wB.
Proof.
    intros.
    apply cmod_means_mod.
    unfold cmod.
    apply div_is_mod. apply wb0.
    rewrite Z.mul_sub_distr_r.
    rewrite Z.sub_sub_distr.
    rewrite <- Z.add_sub_swap.
    replace ((a + wB / 2) mod wB * b) 
        with (b * ((a + wB / 2) mod wB)) by lia.
    apply div_is_mod. apply wb0.
    rewrite Zmult_mod_idemp_r. 
    f_equal.
    lia.
Qed.

Lemma cmod_mul_r : forall a b, cmod (b * cmod a wB) wB = cmod (b * a) wB.
Proof.
    intros. 
    rewrite Z.mul_comm.
    rewrite cmod_mul_l.
    f_equal. 
    lia.
Qed.

Lemma cmod_mul_assoc : forall a b c, cmod (cmod (a * b) wB * c) wB = cmod (a * cmod (b * c) wB) wB.
Proof.
    intros.
    rewrite cmod_mul_l.
    symmetry.
    rewrite Z.mul_comm.
    rewrite cmod_mul_l.
    f_equal.
    lia.
Qed.

Lemma cmod_mul_add_distr : forall a b c, cmod (cmod (a * b) wB + cmod (a * c) wB) wB = cmod (a * cmod (b + c) wB) wB.
Proof.
    intros.
    rewrite cmod_add_l.
    rewrite Z.add_comm.
    rewrite cmod_add_l.
    replace (a * cmod (b + c) wB) with (cmod (b + c) wB * a) by lia.
    rewrite cmod_mul_l.
    f_equal.
    lia.
Qed.

    
    

    
    
    
