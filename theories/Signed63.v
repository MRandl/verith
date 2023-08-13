From Coq Require Import Sint63.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Verith Require Import ZDivides.
From Verith Require Import Cmod.

Open Scope sint63.

Theorem add_comm : forall a b, a + b = b + a.
Proof.
    intros.
    rewrite <- of_to_Z.
    rewrite -> add_spec.
    rewrite Z.add_comm.
    rewrite <- add_spec.
    rewrite -> of_to_Z.
    reflexivity.
Qed.

Theorem add_assoc : forall a b c, a + b + c = a + (b + c).
Proof.
    intros.
    rewrite <- of_to_Z.
    rewrite <- of_to_Z at 1.
    do 4 rewrite -> add_spec.
    replace (to_Z a + cmod (to_Z b + to_Z c) wB)%Z 
        with (cmod (to_Z b + to_Z c) wB + to_Z a)%Z by lia.
    do 2 rewrite cmod_add_l.
    do 2 f_equal.
    lia.
Qed.

Theorem add_0_l : forall a, 0 + a = a.
Proof.
    intro a.
    rewrite <- of_to_Z at 1.
    rewrite -> add_spec.
    rewrite Z.add_0_l.
    rewrite of_Z_cmod.
    apply of_to_Z.
Qed.

Theorem add_0_r : forall a, a + 0 = a.
Proof.
    intro a.
    rewrite add_comm.
    apply add_0_l.
Qed.

Theorem add_opp_l : forall a, a + (-a) = 0.
Proof.
    intro a.
    rewrite <- of_to_Z at 1.
    rewrite -> add_spec.
    rewrite opp_spec.
    rewrite <- of_to_Z.
    rewrite to_Z_0.
    unfold cmod.
    rewrite <- Z.add_assoc.
    rewrite Z.sub_add.
    rewrite Zplus_mod_idemp_r.
    rewrite Z.add_assoc.
    rewrite Z.add_opp_diag_r.
    fold (cmod 0 wB).
    apply of_Z_cmod.
Qed.

Theorem add_opp_r : forall a, (-a) + a = 0.
Proof.
    intros.
    rewrite add_comm.
    apply add_opp_l.
Qed.

(* ( SInt63, + ) is associative, commutative, has a neutral element 
and an inverse operation : it is an abelian group :) 

can we push it to a field ? unfortunately, no. Multiplication in Z/nZ is 
invertible iff n is prime, which is not the case of wB = 2 ^ 63. 
As a consolation prize, we can still make ( SInt63, +, * ) a commutative ring. *)


Theorem mul_comm : forall a b, a * b = b * a.
Proof.
    intros.
    rewrite <- of_to_Z.
    rewrite -> mul_spec.
    rewrite Z.mul_comm.
    rewrite <- mul_spec.
    rewrite -> of_to_Z.
    reflexivity.
Qed.    

Theorem mul_assoc : forall a b c, a * b * c = a * (b * c).
Proof.
    intros.
    rewrite <- of_to_Z.
    do 2 rewrite -> mul_spec.
    rewrite <- of_to_Z at 1.
    do 2 rewrite -> mul_spec at 1.
    rewrite cmod_mul_assoc.
    reflexivity.
Qed.

Theorem mul_add_distr_l: forall a b c, a * (b + c) = a * b + a * c.
Proof.
    intros.
    rewrite <- of_to_Z.
    rewrite add_spec.
    do 2 rewrite mul_spec.
    rewrite <- of_to_Z at 1.
    rewrite mul_spec.
    rewrite add_spec.
    rewrite cmod_add_l, cmod_add_r.
    rewrite <- Z.mul_add_distr_l.
    rewrite cmod_mul_r.
    reflexivity.
Qed.

Theorem mul_add_distr_r: forall a b c, (b + c) * a = b * a + c * a.
Proof.
    intros.
    rewrite mul_comm.
    rewrite mul_add_distr_l.
    rewrite mul_comm; f_equal; apply mul_comm.
Qed.

Theorem mul_1_l : forall a, 1 * a = a.
Proof.
    intros.
    rewrite <- of_to_Z at 1.
    rewrite mul_spec.
    rewrite Z.mul_1_l.
    rewrite of_Z_cmod.
    apply of_to_Z.
Qed.

Theorem mul_1_r : forall a, a * 1 = a.
Proof.
    intros.
    rewrite mul_comm.
    apply mul_1_l.
Qed.
    

(* Sint63 is an abelian group when associated with addition. It also 
has a multiplication which is associative, distributes over addition 
and has a neutral element. The multiplication also happens to be 
commutative, therefore Sint63 forms a commutative ring! *)

    