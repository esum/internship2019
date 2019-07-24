From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq ssreflect.prime div.
From mathcomp Require Import path fintype bigop.
From mathcomp Require Import ssralg ssrint.
Add LoadPath "~/git/git.graillo.tf/stage/2019-06/src".
Require Import seq2 arith sumz primes_induction.


(* Definition and properties of the M\u00f6bius function.
 *)


Definition squarefree n := 
  if n == 0 then false
  else all (eq_op 1) (unzip2 (prime_decomp n)).


Lemma squarefree_mul :
  forall m n, 0 < m -> 0 < n
  -> coprime m n
  -> squarefree m -> squarefree n
  -> squarefree (m * n).
Proof.
  move=> m n m_gt_0 n_gt_0 m_coprime_n m_squarefree n_squarefree.
  unfold squarefree in *.
  rewrite ?eqn0Ngt ?m_gt_0 ?n_gt_0 /= in m_squarefree, n_squarefree.
  rewrite eqn0Ngt.
  assert (0 < m * n) as m_n_gt_0 by by [rewrite -(muln0 0) ; apply ltn_mul].
  rewrite m_n_gt_0 /=.
  pose proof (prime_decomp_coprime m n m_gt_0 n_gt_0 m_coprime_n) as H.
  by rewrite all_map (perm_all _ H) all_cat -?all_map m_squarefree n_squarefree.
Qed.

Import intZmod.
Import intRing.

Local Open Scope ring_scope.
Local Open Scope int_scope.
Bind Scope ring_scope with int.

Import GRing.


Definition mobius (n : nat) :=
  if n == 0%N then 0
  else if n == 1%N then 1
  else if all (eq_op 1%N) (unzip2 (prime_decomp n)) then
    if odd (size (prime_decomp n)) then Negz 0
    else 1
  else 0.

Lemma big_all_eq :
   forall {R : eqType} {zero : R} {times : Monoid.mul_law zero}
     {plus : Monoid.add_law zero times} {I : eqType} {r : seq I}
     (a : R) (P : pred I) (F : I -> R),
   all (eq_op a) [seq F i | i <- r & P i] ->
   \big[plus/zero]_(i <- r | P i) F i =
   iter (size ([seq i <- r | P i])) (plus a) zero.
Proof.
  move=> R zero times plus I r a P F ; move: r ;
  elim=> [|h r IHr] Ha ; first by rewrite big_nil.
  rewrite big_cons size_filter /=.
  move/allP in Ha.
  pose proof (Ha (F h)) as Ha2.
  assert (P h -> F h \in [seq F i | i <- h :: r & P i]) as H
    by by move=> P_h ; rewrite /= P_h mem_head.
  move: H ; case: (P h) ; move=> H.
    apply Ha2 in H ; last by [].
    move/eqP in H.
    rewrite add1n /= -H IHr //.
      by rewrite size_filter.
      apply/allP.
      move=> i Hi.
      apply Ha.
      rewrite /=.
      by case (P h) ; first apply mem_behead.
   rewrite add0n IHr ; first by rewrite size_filter.
   apply/allP.
   move=> i Hi.
     apply Ha.
     rewrite /=.
     by case (P h); first apply mem_behead.
Qed.

Notation "\mu ( n )" := (mobius n).

Lemma mobius_mul_coprime : forall m n, coprime m n -> \mu(m * n)%N = \mu(m) * \mu(n).
Proof.
  move=> [|[|m]] [|[|n]] m_coprime_n // ; first rewrite mul1n mul1r // ; first rewrite muln1 mulr1 //.
  unfold mobius.
  rewrite ?muln_eq0 ?muln_eq1 /=.
  pose proof (prime_decomp_coprime _ _ (ltn0Sn m.+1) (ltn0Sn n.+1) m_coprime_n).
  apply (perm_map snd) in H as H2.
  rewrite (perm_all (eq_op 1%N) H2) map_cat all_cat.
  case: (all (eq_op 1%N) (unzip2 (prime_decomp m.+2))) ; case: (all (eq_op 1%N) (unzip2 (prime_decomp n.+2))) ; rewrite ?mulr0 ?mul0r //=.
  rewrite (perm_size H) size_cat odd_add.
  by case: (odd (size (prime_decomp m.+2))) ; case: (odd (size (prime_decomp n.+2))).
Qed.

Lemma sumz0 {T : Type} :
  forall (f : T -> int) (s : seq T), all (eq_op 0) [seq f x | x <- s]
  -> \sum_(x <- s) f x = 0.
Proof.
  move=> f ; elim=> [|h s IHs] ; move=> all_eq_0 ; rewrite BigOp.bigopE //=.
  rewrite /= in all_eq_0.
  move/andP in all_eq_0.
  destruct all_eq_0 as [f_h_eq_0 all_eq_0].
  move/eqP in f_h_eq_0.
  rewrite -f_h_eq_0 add0r -BigOp.bigopE.
  by apply: IHs.
Qed.


Lemma mobius_sum : forall n, n > 0 -> \sum_(d %| n) \mu(d) = Posz (n == 1%N).
Proof.
  apply primespow_induction ; first rewrite BigOp.bigopE //=.
  move=> m n m_gt_0 n_gt_0 m_coprime_n sum_div_m sum_div_n.
    rewrite muln_eq1.
    assert (Posz ((m == 1%N) && (n == 1%N)) = (Posz (m == 1%N)) * (Posz (n == 1%N))) as H
      by by [case (m == 1%N) ; case (n == 1%N) ; by rewrite ?muln1 //].
    rewrite H -sum_div_m -sum_div_n big_distrl /= sumz_div_mul //.
    apply eq_big_seq ; move=> d1 d1_dvd_m ; rewrite big_distrr /=.
    apply eq_big_seq ; move=> d2 d2_dvd_n.
    rewrite -?dvdn_divisors // in d1_dvd_m, d2_dvd_n.
    rewrite mobius_mul_coprime //.
    apply coprime_dvdl with m ; first by [] ;
    by apply coprime_dvdr with n.
  move=> p [|[|a]] p_prime a_gt_0 ; rewrite BigOp.bigopE //.
    rewrite expn1 divisors_prime //= addr0.
    unfold mobius.
    rewrite /= eq_sym (ltn_eqF (prime_gt0 p_prime)) eq_sym (ltn_eqF (prime_gt1 p_prime)).
    unfold prime in p_prime.
    destruct (prime_decomp p) as [|[p' [|[|a]]] [|]] ; by [].
    assert (p ^ a.+2 != 1)%N as result_0.
      apply/negP.
      move=> H.
      rewrite expn_eq1 eq_sym (ltn_eqF (prime_gt1 p_prime)) -eqnE // in H.
    destruct (p ^ a.+2 == 1)%N ; first by [] ; clear result_0.
    pose proof (primepow_prime_exp p a.+2 p_prime a_gt_0) as H.
    apply primepow_divisors in H.
    rewrite prime_decompE primes_exp // primes_prime //= lognX lognn p_prime muln1 //= in H.
    rewrite H /= expn0 expn1 addrA.
    unfold mobius.
    rewrite /=.
      rewrite /= eq_sym (ltn_eqF (prime_gt0 p_prime)) eq_sym (ltn_eqF (prime_gt1 p_prime)).
      rewrite prime_decomp_prime in p_prime.
      move/eqP in p_prime.
      rewrite ?p_prime /=.
      move/eqP in p_prime.
      rewrite -prime_decomp_prime in p_prime.
      rewrite ?prime_decomp_primepow //= expn_eq0 expn_eq1 -eqnE //= eqnE orbF
        add0r ltn0Sn andbT
        eq_sym (ltn_eqF (prime_gt0 p_prime))
        eq_sym (ltn_eqF (prime_gt1 p_prime)) add0r.
      rewrite -BigOp.bigopE.
      apply sumz0.
      apply/allP.
      move=> d Hd.
      rewrite -map_comp in Hd.
      move/nthP in Hd.
      pose proof (Hd 0) as Hd.
      destruct Hd as [i Hi Hd].
      rewrite size_map in Hi.
      rewrite (nth_map 0%N) // in Hd.
      destruct (nth 0%N (iota 3 a) i) as [|[|n]]eqn:Hn ;
        apply (mem_nth 0%N) in Hi as Hi0 ; rewrite mem_iota Hn // in Hi0.
      rewrite -Hd //= expn_eq0 expn_eq1 -eqnE /= ltn0Sn
        orbF andbT eqnE !eqn0Ngt (prime_gt0 p_prime) /=
        eqn_leq leqNgt (prime_gt1 p_prime) /=
        prime_decomp_primepow //.
Qed.

Lemma mobius_inversion :
  forall f n, 0 < n
  -> f n = \sum_(d %| n) mulz \mu(d) (\sum_(d' %| n %/ d) f d').
Proof.
  move=> f n n_gt_0.
  rewrite sumz_div_inv //.
  assert (
    \sum_(d %| n) \mu(n %/ d) * (\sum_(d' %| n %/ (n %/ d)) f d')
    = \sum_(d %| n) \mu(n %/ d) * (\sum_(d' %| d) f d')
    ) as step1.
    rewrite ?BigOp.bigopE /=.
    unfold reducebig.
    apply foldr_eq_in.
    move=> d m d_dvd_n.
    simpl.
    congr add ; congr mul ; congr foldr ; congr divisors.
    rewrite divnA.
    rewrite -divn_mulAC.
    rewrite divnn n_gt_0 mul1n //.
    rewrite dvdnn //.
    rewrite dvdn_divisors //.
  rewrite step1.
  assert (
    \sum_(d %| n) \mu(n %/ d) * (\sum_(d' %| d) f d')
    =  \sum_(d %| n) (\sum_(d' %| d) \mu(n %/ d) * (f d'))
    ) as step2.
  apply eq_big ; first by [] ;
    move=> d _.
  by rewrite big_distrr.
  rewrite step2.
  rewrite (sumz_div_div (fun m d' => \mu(m) * (f d'))) //.
  assert (
    \sum_(d' %| n) \sum_(d %| n %/ d') \mu(d) * (f d')
    = \sum_(d' %| n) (f d') * (\sum_(d %| n %/ d') \mu(d))
    ) as step3.
  apply eq_big ; first by [] ;
    move=> d _.
  by rewrite mulrC -big_distrl.
  rewrite step3.
  assert (
    \sum_(d' %| n) (f d') * (\sum_(d %| n %/ d') \mu(d))
    = \sum_(d' %| n) (f d') * (Posz (n == d'))
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
  by rewrite (eq_filter H) filter_pred0 big_nil addr0.
  rewrite mem_filter eq_refl divisors_id //.
  rewrite filter_uniq //.
  apply divisors_uniq.
Qed.
