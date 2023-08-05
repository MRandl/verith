From Coq Require Import ZArith.
From Coq Require Import Lia.
Open Scope Z.

(* The goal of this file is to establish that Z can be seen
 as two copies of N glued at 0, meaning we can prove stuff 
 by induction over Z by "inducting over both N's" *)

Definition restrictionPositive(P : Z -> Prop) : positive -> Prop :=
    fun p : positive => P (Zpos p).

Definition restrictionNegative(P : Z -> Prop) : positive -> Prop :=
    fun p : positive => P (Zneg p).

Theorem Z_induction_two_N : forall P : Z -> Prop, P 0 -> P 1 -> P (- 1) -> 
  (forall p, P(Zpos p) -> P (Z.succ (Zpos p))) -> (forall p, P(Zneg p) -> P (Z.pred (Zneg p))) -> 
  (forall z : Z, P z).
Proof.
    intros P P0 P1 Pm1 recpos recneg z.
    destruct z.
    - exact P0.
    - pose proof (Pos.peano_rec (restrictionPositive P) P1) as H.
      unfold restrictionPositive in H. 
      apply H. intros p' hyp. rewrite Pos2Z.inj_succ.
      apply recpos, hyp.
    - pose proof (Pos.peano_rec (restrictionNegative P) Pm1) as H.
      unfold restrictionNegative in H.
      apply H. intros p' hyp. replace (Z.neg (Pos.succ p')) with (Z.pred (Z.neg p')) by lia.
      apply recneg, hyp.
Qed.
