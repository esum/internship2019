From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq ssreflect.prime div.
From mathcomp Require Import path fintype bigop.
Add LoadPath "~/git/git.graillo.tf/stage/2019-06/src".
Require Import seq2 arith ssrz sumz primes_induction.

(* Definition and properties of the M\u00f6bius function.
 *)


Definition mobius n :=
  if n == 0 then Znn 0
  else if n == 1 then Znn 1
  else if all (eq_op 1) (unzip2 (prime_decomp n)) then
    if odd (size (prime_decomp n)) then Zne 0
    else Znn 1
  else Znn 0.

Notation "\mu ( n )" := (mobius n).

Lemma mobius_mul_coprime : forall m n, coprime m n -> \mu(m * n) = mulz \mu(m) \mu(n).
Proof.
  move=> [|[|m]] [|[|n]] m_coprime_n // ; first rewrite mul1n mul1z // ; first rewrite muln1 mulz1 //.
  unfold mobius.
  rewrite ?muln_eq0 ?muln_eq1 /=.
  pose proof (prime_decomp_coprime _ _ (ltn0Sn m.+1) (ltn0Sn n.+1) m_coprime_n).
  apply (perm_map snd) in H as H2.
  rewrite (perm_all (eq_op 1) H2) map_cat all_cat.
  case: (all (eq_op 1) (unzip2 (prime_decomp m.+2))) ; case: (all (eq_op 1) (unzip2 (prime_decomp n.+2))) ; rewrite ?mulz0 //=.
  rewrite (perm_size H) size_cat odd_add.
  by case: (odd (size (prime_decomp m.+2))) ; case: (odd (size (prime_decomp n.+2))).
Qed.

Lemma mobius_sum : forall n, n > 0 -> \sumz_(d %| n) \mu(d) = Znn (n == 1).
Proof.
  apply primespow_induction ; first rewrite BigOp.bigopE //=.
  move=> m n m_gt_0 n_gt_0 m_coprime_n sum_div_m sum_div_n.
    rewrite muln_eq1.
    assert (Znn ((m == 1) && (n == 1)) = mulz (Znn (m == 1)) (Znn (n == 1))) as H
      by by [case (m == 1) ; case (n == 1) ; by rewrite ?muln1 //].
    rewrite H -sum_div_m -sum_div_n -sumzDl sumz_div_mul.
    apply eq_big_seq ; move=> d1 d1_dvd_m ; rewrite -sumzDr.
    apply eq_big_seq ; move=> d2 d2_dvd_n.
    rewrite -?dvdn_divisors // in d1_dvd_m, d2_dvd_n.
    rewrite mobius_mul_coprime //.
    apply coprime_dvdl with m ; first by [] ;
    by apply coprime_dvdr with n.
  move=> p [|[|a]] p_prime a_gt_0 ; rewrite BigOp.bigopE //.
    rewrite expn1 divisors_prime //= addz0.
    unfold mobius.
    rewrite /= eq_sym (ltn_eqF (prime_gt0 p_prime)) eq_sym (ltn_eqF (prime_gt1 p_prime)).
    unfold prime in p_prime.
    destruct (prime_decomp p) as [|[p' [|[|a]]] [|]] ; by [].
    assert (p ^ a.+2 != 1) as result_0.
      apply/negP.
      move=> H.
      rewrite expn_eq1 eq_sym (ltn_eqF (prime_gt1 p_prime)) -eqnE // in H.
    destruct (p ^ a.+2 == 1) ; first by [] ; clear result_0.
    pose proof (primepow_prime_exp p a.+2 p_prime a_gt_0) as H.
    apply primepow_divisors in H.
    rewrite prime_decompE primes_exp // primes_prime //= lognX lognn p_prime muln1 //= in H.
    rewrite H /= expn0 expn1 addzA.
    unfold mobius.
    rewrite /=.
      rewrite /= eq_sym (ltn_eqF (prime_gt0 p_prime)) eq_sym (ltn_eqF (prime_gt1 p_prime)).
      rewrite prime_decomp_prime in p_prime.
      move/eqP in p_prime.
      rewrite ?p_prime /=.
      move/eqP in p_prime.
      rewrite -prime_decomp_prime in p_prime.
      rewrite ?prime_decomp_primepow //= expn_eq0 expn_eq1 -eqnE //= eqnE orbF
        add0z ltn0Sn andbT
        eq_sym (ltn_eqF (prime_gt0 p_prime))
        eq_sym (ltn_eqF (prime_gt1 p_prime)) add0z.
      rewrite -BigOp.bigopE.
      apply sumz0.
      apply/allP.
      move=> d Hd.
      rewrite -map_comp in Hd.
      move/nthP in Hd.
      pose proof (Hd (Znn 0)) as Hd.
      destruct Hd as [i Hi Hd].
      rewrite size_map in Hi.
      rewrite (nth_map 0) // in Hd.
      destruct (nth 0 (iota 3 a) i) as [|[|n]]eqn:Hn ;
        apply (mem_nth 0) in Hi as Hi0 ; rewrite mem_iota Hn // in Hi0.
      rewrite -Hd //= expn_eq0 expn_eq1 -eqnE /= ltn0Sn
        orbF andbT eqnE !eqn0Ngt (prime_gt0 p_prime) /=
        eqn_leq leqNgt (prime_gt1 p_prime) /=
        prime_decomp_primepow //.
Qed.

Lemma mobius_inversion :
  forall f n, 0 < n
  -> f n = \sumz_(d %| n) mulz \mu(d) (\sumz_(d' %| n %/ d) f d').
Proof.
  move=> f n n_gt_0.
  rewrite sumz_div_inv.
  assert (
    \sumz_ (d %| n) mulz \mu (n %/ d) (\sumz_ (d' %| n %/ (n %/ d)) f d')
    = \sumz_ (d %| n) mulz \mu (n %/ d) (\sumz_ (d' %| d) f d')
    ) as step1.
    rewrite ?BigOp.bigopE /=.
    unfold reducebig.
    apply foldr_eq_in.
    move=> d m d_dvd_n.
    simpl.
    congr addz ; congr mulz ; congr foldr ; congr divisors.
    rewrite divnA.
    rewrite -divn_mulAC.
    rewrite divnn n_gt_0 mul1n //.
    rewrite dvdnn //.
    rewrite dvdn_divisors //.
  rewrite step1.
  assert (
    \sumz_ (d %| n) mulz \mu (n %/ d) (\sumz_ (d' %| d) f d')
    =  \sumz_ (d %| n) (\sumz_ (d' %| d) mulz \mu (n %/ d) (f d'))
    ) as step2.
  apply eq_big ; first by [] ;
    move=> d _.
  by rewrite -sumzDr.
  rewrite step2.
  rewrite (sumz_div_div (fun m d' => mulz \mu(m) (f d'))) //.
  assert (
    \sumz_ (d' %| n) \sumz_ (d %| n %/ d') mulz \mu (d) (f d')
    = \sumz_ (d' %| n) mulz (f d') (\sumz_ (d %| n %/ d') \mu (d))
    ) as step3.
  apply eq_big ; first by [] ;
    move=> d _.
  by rewrite mulzC sumzDl.
  rewrite step3.
  assert (
    \sumz_ (d' %| n) mulz (f d') (\sumz_ (d %| n %/ d') \mu (d))
    = \sumz_ (d' %| n) mulz (f d') (Znn (n == d'))
    ) as step4.
  apply eq_big_seq ;
    move=> d d_dvd_n.
  rewrite -dvdn_divisors // in d_dvd_n.
  assert (0 < d) as d_gt_0 by by apply dvdn_gt0 with n.
  rewrite mobius_sum //.
  rewrite -(eqn_pmul2r d_gt_0).
  rewrite dvdn_eq in d_dvd_n.
  move/eqP in d_dvd_n.
  by rewrite d_dvd_n mul1n.
  rewrite divn_gt0 // dvdn_leq //.
  rewrite step4.
  rewrite sumz_kronecker -big_filter (bigD1_seq n) /=.
  rewrite -big_filter -filter_predI.
  assert ((predI (fun i : nat => i != n) (eq_op n)) =1 (fun n => false)) as H.
    move=> m /=.
    rewrite eq_sym ; by case (n == m).
  by rewrite (eq_filter H) filter_pred0 big_nil addz0.
  rewrite mem_filter eq_refl divisors_id //.
  rewrite filter_uniq //.
  apply divisors_uniq.
Qed.
