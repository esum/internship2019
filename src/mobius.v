From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq ssreflect.prime div.
From mathcomp Require Import path fintype bigop.
Add LoadPath "~/git/git.graillo.tf/stage/2019-06/src".
Require Import seq2 arith ssrz sumz.

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

Lemma primespow_induction : forall P,
  P 1
  -> (forall m n, m > 0 -> n > 0 -> coprime m n -> P m -> P n -> P (m * n))
  -> (forall p a, prime p -> 0 < a -> P (p^a))
  -> (forall n, P n).
Admitted.

Lemma mobius_sum : forall n, \sumz_(d %| n) \mu(d) = Znn (n == 1).
Proof.
  apply primespow_induction ; first rewrite BigOp.bigopE //=.
  move=> m n m_gt_0 n_gt_0 m_coprime_n sum_div_m sum_div_n.
    admit.
  move=> p [|[|a]] p_prime a_gt_0 ; rewrite BigOp.bigopE //.
    rewrite expn1 divisors_prime //= addz0.
    unfold mobius.
    rewrite /= eq_sym (ltn_eqF (prime_gt0 p_prime)) eq_sym (ltn_eqF (prime_gt1 p_prime)).
    unfold prime in p_prime.
    destruct (prime_decomp p) as [|[p' [|[|a]]] [|]] ; by [].
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
      rewrite ?prime_decomp_primepow //= expn_eq0 expn_eq1 -eqnE //= eqnE orbF.
Admitted.

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
Admitted.