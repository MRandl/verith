From Coq Require Import Uint63.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Verith Require Import ZDivides.

Open Scope uint63.

(* UInt63 has more proven lemmas than its cousin SInt63,
making our job here easier. Also, avoiding shifting everything 
by wB/2 everywhere makes for some more manageable equations. *)

Theorem add_comm : forall a b, a + b = b + a.
Proof.
    apply Uint63.add_comm.
Qed.


Theorem add_assoc : forall a b c, a + b + c = a + (b + c).
Proof.
    intros. symmetry.
    apply Uint63.add_assoc.
Qed.

Theorem add_0_l : forall a, 0 + a = a.
Proof.
    intro a.
    rewrite <- of_to_Z at 1.
    rewrite -> add_spec.
    rewrite Z.add_0_l.
    rewrite <- of_Z_spec.
    do 2 rewrite of_to_Z.
    reflexivity.
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
    rewrite Zplus_mod_idemp_r.
    rewrite Z.add_opp_diag_r.
    reflexivity.
Qed.

Theorem add_opp_r : forall a, (-a) + a = 0.
Proof.
    intros.
    rewrite add_comm.
    apply add_opp_l.
Qed.

(* ( UInt63, + ) is associative, commutative, has a neutral element 
and an inverse operation : it is an abelian group.
As with SInt63, we can get a commutative ring, but not a field *) 


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
    rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r.
    f_equal. f_equal. lia.
    easy. easy.
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
    rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r.
    rewrite Z.mul_mod_idemp_r.
    rewrite <- Z.mul_add_distr_l.
    reflexivity.
    easy. easy. easy.
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
    rewrite <- of_Z_spec.
    do 2 rewrite of_to_Z.
    reflexivity.
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

    