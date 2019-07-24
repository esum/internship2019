From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq div prime.
From mathcomp Require Import path fintype bigop.
Add LoadPath "~/git/git.graillo.tf/stage/2019-06/src".
Require Import seq2 arith.


Lemma legendre_formula :
  forall n p, prime p
  -> logn p (n`!) = \sum_(1 <= a < (trunc_log p n).+1) n %/ p ^ a.
Proof.
  move=> n p p_prime.
  assert (
    \sum_(1 <= a < (trunc_log p n).+1) n %/ p ^ a
    = \sum_(1 <= a < (trunc_log p n).+1) \sum_(1 <= i < n.+1) (p ^ a %| i)
    ) as step1.
  apply eq_big ; first by [].
  move=> i _ ; rewrite divn_count_dvd //.
  rewrite step1.
  rewrite exchange_big /= fact_prod logn_prod_f.
  apply eq_big_nat.
  move=> m H.
  move/andP in H.
  destruct H as [m_gt_0 m_lt_Sn].
  rewrite (big_cat_nat _ _ _ (ltn0Sn (trunc_log p m))) /=.
  rewrite -(addn0 (logn p m)).
  congr addn.
  rewrite logn_count_dvd //.
  rewrite (big_cat_nat _ _ _ (ltn0Sn (trunc_log p m))) /=.
  rewrite -{2}(addn0 (\sum_(1 <= i < (trunc_log p m).+1) (p ^ i %| m))).
  congr addn.
  apply/eqP.
  rewrite eqn_0_sum.
  apply/allP.
  move=> f f_in.
  move/nthP in f_in.
  destruct (f_in 0) as [i Hi Hf].
  rewrite size_map in Hi.
  rewrite (nth_map 0) // in Hf.
  rewrite size_iota in Hi.
  rewrite nth_iota // in Hf.
  rewrite eqnE eq_sym -Hf pfactor_dvdn //.
  assert (forall b : bool, (nat_of_bool b == 0) = ~~ b) as H by by case.
  rewrite H -ltnNge.
  apply ltn_addr.
  rewrite ltnS.
  apply leq_logn_trunc_log ; first by [].
  by apply prime_gt1.
  apply expn_ltn_exp with p ; first by apply prime_gt1.
  by apply trunc_logP ; first by apply prime_gt1.
  apply/eqP.
  rewrite eq_sym eqn_0_sum.
  apply/allP.
  move=> f f_in.
  move/nthP in f_in.
  destruct (f_in 0) as [i Hi Hf].
  rewrite size_map in Hi.
  rewrite (nth_map 0) // in Hf.
  rewrite size_iota in Hi.
  rewrite nth_iota // in Hf.
  rewrite eqnE eq_sym -Hf pfactor_dvdn //.
  assert (forall b : bool, (nat_of_bool b == 0) = ~~ b) as H by by case.
  rewrite H -ltnNge.
  apply ltn_addr.
  rewrite ltnS.
  apply leq_logn_trunc_log ; first by [].
  by apply prime_gt1.
  apply leq_trunc_log ; first by apply prime_gt1.
  apply/andP ; by split.
  apply/allP.
  move=> i Hi.
  rewrite map_id mem_iota in Hi.
  move/andP in Hi.
  by destruct Hi.
Qed.
