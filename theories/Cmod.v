From Coq Require Import Sint63.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Verith Require Import ZDivides.

Open Scope Z.

Lemma cmod_add : forall a b c, cmod (cmod (a + b) wB + c) wB = cmod (a + b + c) wB.
Proof.
    intros.
    unfold cmod.
    rewrite <- Z.add_assoc.
    rewrite Z.sub_cancel_r.
    replace (((a + b + wB / 2) mod wB - wB / 2 + (c + wB / 2))) 
        with ((a + b + wB / 2) mod wB + c) by lia.
    rewrite Zplus_mod_idemp_l.
    f_equal.
    lia.
Qed.

Lemma cmod_mult : forall a b c, cmod (cmod (a * b) wB * c) wB = cmod (a * b * c) wB.
Proof.
    intros.
    unfold cmod.
    apply Z.sub_cancel_r.
    apply div_is_mod. unfold wB, size. lia.
    replace (a * b * c + wB / 2 -
    (((a * b + wB / 2) mod wB - wB / 2) * c + wB / 2)) with 
    (a * b * c - (((a * b + wB / 2) mod wB - wB / 2) * c)) by lia.
    rewrite Z.mul_sub_distr_r.
    rewrite Z.sub_sub_distr.
    rewrite <- Z.add_sub_swap.
    replace ((a * b + wB / 2) mod wB * c) with (c * ((a * b + wB / 2) mod wB)) by lia.
    apply div_is_mod. unfold wB, size. lia. 
    rewrite Zmult_mod_idemp_r. 
    f_equal.
    lia.
Qed.

Lemma cmod_mul_assoc : forall a b c, cmod (cmod (a * b) wB * c) wB = cmod (a * cmod (b * c) wB) wB.
Proof.
    intros.
    rewrite cmod_mult.
    symmetry.
    rewrite Z.mul_comm .
    rewrite cmod_mult.
    f_equal.
    lia.
Qed.