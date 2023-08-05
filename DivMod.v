From Coq Require Import ZArith.
Require Import Lia. (* dieu merci que lia existe *)
Require Import ZInduction.
Open Scope Z.

Lemma mult_pos_bigger : forall a b, a > 0 -> b > 0 -> a * b >= b.
Proof.
    apply (Z_induction_two_N (fun a => forall b : Z, a > 0 -> b > 0 -> a * b >= b)); lia.
Qed.

Lemma mult_neg_smaller : forall a b, a < 0 -> b > 0 -> - b >= a * b .
Proof.
    apply (Z_induction_two_N (fun a => forall b, a < 0 -> b > 0 -> - b >= a * b )); lia.
Qed.

Lemma divides_smaller : forall a b, b > 0 -> (b | a) -> (-b < a < b) -> a = 0.
Proof.
    intros a b bpos b_div_a a_bound.
    destruct b_div_a.
    destruct x.
    - lia.
    - exfalso. pose proof (mult_pos_bigger (Z.pos p) b (Zgt_pos_0 p) bpos). lia.
    - exfalso. pose proof (mult_neg_smaller (Z.neg p) b (Zlt_neg_0 p) bpos). lia.
Qed.

Theorem div_is_mod : forall (a b c : Z), c > 0 -> (a mod c = b mod c <-> (c | b - a)).
Proof.
    intros a b c cpos.
    split; intro hyp.
    - unfold Z.divide. unfold Z.modulo in hyp.
      assert (c <> 0) as nonzero by lia.
      remember (Z.div_eucl a c) as tmp eqn:divac. destruct tmp as [k' r'].
      remember (Z.div_eucl b c) as tmp eqn:divbc. destruct tmp as [k r].
      subst.
      pose proof (Z.div_eucl_eq a c nonzero) as decomp_a. rewrite <- divac in decomp_a.
      pose proof (Z.div_eucl_eq b c nonzero) as decomp_b. rewrite <- divbc in decomp_b.
      subst.
      exists (k - k').
      lia.
    - unfold Z.modulo. destruct hyp.
      remember (Z.div_eucl a c) as tmp eqn:divac. destruct tmp as [k' r'].
      remember (Z.div_eucl b c) as tmp eqn:divbc. destruct tmp as [k r].

      pose proof (Z_div_mod a c cpos) as decomp_a.
      rewrite <- divac in decomp_a. destruct decomp_a as [decomp_a rem_a]. 
      pose proof (Z_div_mod b c cpos) as decomp_b. 
      rewrite <- divbc in decomp_b. destruct decomp_b as [decomp_b rem_b].

      rewrite decomp_a, decomp_b in H.
      assert (c * (k - k' - x) = r' - r) as tmp by lia. clear H.
      assert (-c < r' - r < c) by lia.
      apply Z.sub_move_0_r.
      apply divides_smaller with c.
      assumption.
      exists (k - k' - x). lia.
      assumption.
Qed.
