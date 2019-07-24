From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq prime div.
From mathcomp Require Import path fintype bigop.
Add LoadPath "~/git/git.graillo.tf/stage/2019-06/src".
Require Import seq2.

Lemma equiv_eqP : forall P Q x y, reflect P x -> reflect Q y
  -> reflect (P <-> Q) (x == y).
Proof.
  move=> P Q [|] [|] reflect_P_x reflect_Q_y ; inversion reflect_P_x as [p|np] ; inversion reflect_Q_y as [q|nq].
  apply Bool.ReflectT ; by split.
  apply Bool.ReflectF ; move=> [P_Q _] ; apply nq ; by apply P_Q.
  apply Bool.ReflectF ; move=> [_ Q_P] ; apply np ; by apply Q_P.
  apply Bool.ReflectT ; by split.
Qed.

Lemma anti_ltn : antisymmetric ltn.
Proof.
  move=> m n H.
  move/andP in H.
  rewrite /= in H.
  destruct H as [m_lt_n n_lt_m].
  pose proof (ltn_trans m_lt_n n_lt_m) as absurd.
  by rewrite ltnn in absurd.
Qed.

Lemma expn_eq1 : forall m n, (m ^ n == 1) = (m == 1) || (n == 0).
Proof.
  move=> m ; elim=> [|n IHn].
    rewrite expn0 -eqnE orbC //.
    rewrite expnS muln_eq1 IHn.
    case: (m == 1) ; first by [].
    rewrite (eqn0Ngt n.+1) ltn0Sn //.
Qed.

Lemma ltn_leq_trans : forall x y z, ltn x y -> leq y z -> ltn x z.
Proof.
  move=> x y z x_lt_y y_le_z.
  unfold ltn in *.
  simpl in *.
  by apply leq_trans with y.
Qed.

Lemma ltn_0_prod_f {T : Type} :
  forall s (f : T -> nat), all (ltn 0) [seq f x | x <- s]
  -> 0 < \prod_(n <- s) f n.
Proof.
  elim=> [|m s IHs] f s_gt_0 ; rewrite BigOp.bigopE //.
  rewrite /= in s_gt_0.
  move/andP in s_gt_0.
  destruct s_gt_0 as [m_gt_0 s_gt_0].
  simpl.
  rewrite {1}[0]/(0 * 0) -mulnE.
  apply ltn_mul.
    by [].
  rewrite -BigOp.bigopE.
  by apply IHs.
Qed.

Lemma ltn_0_prod : forall s, all (ltn 0) s -> 0 < \prod_(n <- s) n.
Proof.
  elim=> [|m s IHs] s_gt_0 ; rewrite BigOp.bigopE //.
  rewrite /= in s_gt_0.
  move/andP in s_gt_0.
  destruct s_gt_0 as [m_gt_0 s_gt_0].
  simpl.
  rewrite {1}[0]/(0 * 0) -mulnE.
  apply ltn_mul.
    by [].
  rewrite -BigOp.bigopE.
  by apply IHs.
Qed.

Lemma logn_prod_f {T : Type} : forall s p (f : T -> nat), all (ltn 0) [seq f x | x <- s]
  -> logn p (\prod_(x <- s) f x) = \sum_(x <- s) logn p (f x).
Proof.
  elim=> [|m s IHs] p f s_gt_0 ; rewrite BigOp.bigopE.
  rewrite logn1 //.
  rewrite /= in s_gt_0.
  move/andP in s_gt_0.
  destruct s_gt_0 as [m_gt_0 s_gt_0].
  rewrite /= lognM //.
  rewrite -BigOp.bigopE IHs //.
  rewrite -BigOp.bigopE.
  by apply ltn_0_prod_f.
Qed.


Lemma eqn_0_sum {T : Type} :
  forall s (f : T -> nat), (\sum_(x <- s) f x == 0) = (all (eqn 0) [seq f x | x <- s]).
Proof.
  elim=> [|y s IHs] f ; rewrite BigOp.bigopE //=.
  rewrite -BigOp.bigopE addn_eq0 IHs eq_sym //.
Qed.


Definition primepow n := size (prime_decomp n) == 1.

Lemma primepow_prime_exp : forall p e, prime p -> 0 < e -> primepow (p ^ e).
Proof.
  move=> p e p_prime e_gt_0.
  unfold primepow.
  rewrite prime_decompE primes_exp // primes_prime //.
Qed.

Lemma lognn : forall n, logn n n = prime n.
Proof.
  move=> n.
  destruct (prime n)eqn:n_prime ; unfold logn ; rewrite n_prime //.
  destruct n as [|n] ; first inversion n_prime.
  rewrite /= edivn_def /= divnn modnn /=.
  by destruct n as [|n] ; first inversion n_prime.
Qed.

Lemma prime_decomp_prime : forall p, prime p = (prime_decomp p == [:: (p, 1)]).
Proof.
  move=> p.
  apply/eqP/equiv_eqP ; first apply idP ; first apply idP.
  split ; [move=> p_prime|move=> p_decomp].
    apply primes_prime in p_prime as primes_p.
    rewrite prime_decompE primes_p /= lognn p_prime //.
  unfold prime.
    move/eqP in p_decomp.
    by rewrite p_decomp.
Qed.

Lemma prime_decomp_primepow : forall p e, prime p -> 0 < e -> prime_decomp (p ^ e) = [:: (p, e)].
Proof.
  move=> p e p_prime e_gt_0.
  apply primes_prime in p_prime as primes_p.
  rewrite prime_decompE primes_exp // primes_p /= lognX lognn p_prime muln1 //.
Qed.

Lemma divisors_prime : forall p, prime p -> divisors p = [:: 1; p].
Proof.
  move=> p p_prime.
  unfold divisors.
  rewrite prime_decompE primes_prime //= lognn p_prime /= NatTrec.mulE muln1 prime_gt0 //.
Qed.

Lemma pfactor_le_dvdnn : forall p n a, a <= logn p n -> p ^ a %| n.
Proof.
  move=> p n a ; move: n.
  elim: a => [|a IHa] ; move=> n a_lt_log ; first apply: dvd1n.
  rewrite expnS.
  destruct a as [|a].
    rewrite expn0 muln1 ; rewrite logn_gt0 mem_primes in a_lt_log ;
    move/and3P in a_lt_log ; by destruct a_lt_log.
  assert (p %| n).
    apply dvdn_trans with (p ^ a.+1).
    apply dvdn_exp ; first by [] ; apply dvdnn.
    apply IHa.
      apply ltn_trans with a.+1. apply ltnSn.
      by [].
    rewrite -(divnK H) mulnC.
    apply: dvdn_mul ; last apply: dvdnn.
    apply: IHa.
    rewrite logn_div // lognn.
    case: (prime p) ; rewrite ltn_subRL //= add0n.
    apply ltn_trans with a.+1.
      apply ltnSn.
    by [].
Qed.

Lemma mem_primes2 :
  forall n p, (p \in primes n) = (0 < logn p n).
Proof.
  move=> n p.
  rewrite mem_primes lognE.
  apply/eqP/equiv_eqP.
  apply/idP.
  apply/idP.
  split.
  move=> H ; by rewrite H.
  by case ([&& prime p, 0 < n & p %| n]).
Qed.

Section primepow_divisors.

Local Lemma primepow_divisors_aux : forall p a b, [seq (muln p \o expn p) i | i <- iota b a] = [seq p ^ i | i <- iota b.+1 a].
Proof.
  move=> p ; elim=> [|a IHa] //.
  move=> b /=.
  rewrite IHa.
  congr cons.
  by rewrite expnS.
Qed.

Lemma primepow_divisors n : primepow n ->
  let (p, a) := head (0, 0) (prime_decomp n) in
  divisors n = [seq p ^ i | i <- iota 0 a.+1].
Proof.
  destruct (prime_decomp n) as [|[p a] t]eqn:n_decomp ; first unfold primepow ; first by rewrite n_decomp.
    destruct t ; last unfold primepow ; last by rewrite n_decomp.
  move=> _ ; simpl head ; simpl fst ; simpl snd.
  assert (n = p ^ a) as n_eq_pa.
  destruct n ; first by [].
  pose proof (prime_decomp_correct (ltn0Sn n)) as [n_eq_prod _].
  rewrite n_decomp bigop.BigOp.bigopE /= muln1 // in n_eq_prod.
  assert (prime p) as p_prime.
    assert (p \in primes n) as p_primes_n ; unfold primes ; first rewrite n_decomp mem_seq1 //.
    rewrite mem_primes in p_primes_n.
    move/and3P in p_primes_n ; by destruct p_primes_n.
  move: n p n_eq_pa n_decomp p_prime.
  elim: a => [|a IHa] ; move=> n p n_eq_pa n_decomp p_prime.
    rewrite expn0 in n_eq_pa ; rewrite n_eq_pa //.
    destruct a as [|a]. unfold divisors ; rewrite n_decomp /= NatTrec.mulE muln1 (prime_gt0 p_prime) //.
    assert (prime_decomp (p ^ a.+1) = [:: (p, a.+1)]) as pa_decomp.
      rewrite prime_decompE primes_exp ; last apply: ltnS ;
      rewrite primes_prime //= lognX lognn p_prime muln1 //.
    pose proof (IHa (p ^ a.+1) p (Logic.eq_refl (p ^ a.+1)) pa_decomp p_prime) as IH.
      unfold divisors in IH ; rewrite pa_decomp /foldr/PrimeDecompAux.add_divisors/iter in IH.
      unfold divisors ; rewrite n_decomp /foldr/PrimeDecompAux.add_divisors/iter.
      rewrite IH /=.
      rewrite ?NatTrec.mulE expn1 expn0 muln1 (prime_gt0 p_prime) [p ^ 2]/(p * p) ;
        do 3 congr cons.
      rewrite -map_comp.
      rewrite -primepow_divisors_aux.
      by apply eq_map ; move=> m /= ; rewrite NatTrec.mulE.
Qed.

End primepow_divisors.


Lemma mem_cons {T : eqType} : forall x h (t : seq T), x \in t -> x \in h::t.
Proof.
  move=> a h t H.
  rewrite -[h::t]/([:: h] ++ t) mem_cat H.
  by case: (a \in [:: h]).
Qed.

Lemma mem_exp_prime_decomp : forall n e, e \in unzip2 (prime_decomp n) -> 0 < e.
Proof.
  move=> n e e_in_exp.
  move/mapP in e_in_exp.
  destruct e_in_exp as [[p a] H e_eq_a].
  apply mem_prime_decomp in H.
  subst.
  by destruct H.
Qed.

Lemma prime_decomp_nil : forall n, prime_decomp n = [::] -> n <= 1.
Proof.
  case=> n //; case: n ; first by [] ; move=> n H.
  assert (prime (pdiv n.+2)) as pdiv_n_prime ; first by apply: pdiv_prime.
  unfold prime, pdiv, primes in pdiv_n_prime.
  by rewrite H /= in pdiv_n_prime.
Qed.

Lemma prime_decomp_uniq : forall n, uniq (prime_decomp n).
Proof.
  move=> n.
  apply: (map_uniq (primes_uniq n)).
Qed.

Lemma logn_coprime : forall p m, prime p -> coprime p m -> logn p m = 0.
Proof.
  move=> p m p_prime p_coprime_n.
  destruct (logn p m)eqn:logn_p_m ; first by [].
  rewrite -logn_p_m.
  assert (0 < logn p m) as logn_p_m_gt_0 ; rewrite logn_p_m.
    apply ltn0Sn.
  rewrite logn_gt0 mem_primes in logn_p_m_gt_0.
  move/and3P in logn_p_m_gt_0.
  destruct logn_p_m_gt_0 as [_ m_gt_0 p_div_m].
  rewrite prime_coprime // in p_coprime_n.
  absurd (p %| m) ; last by [].
  by move/negP in p_coprime_n.
Qed.

Lemma eqn0_negb : forall (b : bool), (nat_of_bool b == 0) = ~~ b.
Proof.
  by move=> [|].
Qed.

Lemma dvdn_mul2l : forall m n p, (m * n) %| p -> m %| p.
Proof.
  move=> m n p m_n_dvd_p //.
  apply dvdn_trans with (m * n) ; last by [].
  rewrite -{1}(muln1 m).
  apply dvdn_mul.
  apply dvdnn.
  apply dvd1n.
Qed.

Lemma dvdn_mul2r : forall m n p, (m * n) %| p -> n %| p.
Proof.
  move=> m n p m_n_dvd_p //.
  apply dvdn_trans with (m * n) ; last by [].
  rewrite -{1}(mul1n n).
  apply dvdn_mul.
  apply dvd1n.
  apply dvdnn.
Qed.

Lemma dvdn_exp2 : forall m n p, 0 < p -> m ^ p %| n -> m %| n.
Proof.
  move=> m n [|p] p_gt_0 m_p_dvd_n //.
  rewrite expnS in m_p_dvd_n.
  by apply dvdn_mul2l with (m ^ p).
Qed.

Lemma prime_coprime_logn : forall p m, prime p -> 0 < m -> (coprime p m) == (logn p m == 0).
Proof.
  move=> p m p_prime m_gt_0.
  rewrite logn_count_dvd // eqn_0_sum prime_coprime //.
  apply/equiv_eqP.
    apply/negP.
    apply/allP.
  split.
    move=> n_p_dvd_m b b_in.
      rewrite eqnE eq_sym.
      move/nthP in b_in.
      destruct (b_in 0) as [i H H0].
      rewrite size_map in H.
      rewrite (nth_map 1) // in H0.
      rewrite -H0 eqn0_negb.
      apply/negP.
      move=> H1.
      apply n_p_dvd_m.
      apply dvdn_exp2 with (nth 1 (index_iota 1 m) i) ; last by [].
      assert (nth 1 (index_iota 1 m) i \in (index_iota 1 m)) as e_in_iota ; first by apply mem_nth.
      rewrite mem_index_iota in e_in_iota.
      move/andP in e_in_iota.
      by destruct e_in_iota.
    move=> H.
      destruct m as [|[|m]] ; first by [].
      apply/negP.
      rewrite -prime_coprime // coprimen1 //.
      apply/negP.
      pose proof (H (p %| m.+2)) as H.
      rewrite /= eqnE eq_sym eqn0_negb in H.
      apply H.
      rewrite expn1.
      apply mem_head.
Qed.

Lemma all_spred {T : Type} : forall (a : T -> bool) (s : seq T),
  all a s = all (eq_op true) [seq a x | x <- s].
Proof.
  move=> a ; elim=> [|h s IHs] //.
  rewrite /= IHs //.
Qed.

Lemma bool_eq_true : forall b : bool, b == true = b.
Proof.
  by case.
Qed.

Lemma coprime_logn_or : forall m n, m > 0 -> n > 0
  -> coprime m n
  -> forall p, (logn p m == 0) || (logn p n == 0).
Proof.
  move=> m n m_gt_0 n_gt_0 m_coprime_n p.
  destruct (prime p)eqn:p_prime ; last by unfold logn ; rewrite p_prime.
  rewrite (prod_prime_decomp m_gt_0) (prod_prime_decomp n_gt_0) ?logn_prod_f ?eqn_0_sum.
  rewrite all_spred orbC all_spred orbC -?map_comp.
  assert (forall k, {in prime_decomp k, (fun x => 0 == logn p (x.1 ^ x.2)) =1 (fun x => coprime p x.1)}) as H.
    move=> k [q b] H.
    rewrite lognX /= eq_sym muln_eq0 eq_sym ltn_eqF.
    rewrite orbC orbF.
    assert (0 < q) as q_gt_0.
      apply prime_gt0.
      apply (map_f fst) in H.
      rewrite /= mem_primes in H.
      move/and3P in H.
      by destruct H.
    pose proof (prime_coprime_logn p q p_prime q_gt_0) as H0.
    move/eqP in H0.
    rewrite H0 //.
    apply mem_exp_prime_decomp with k.
    rewrite -[b]/(snd (q, b)) map_f //.
  pose proof (H m) as Hm.
  apply eq_in_map in Hm.
  pose proof (H n) as Hn.
  apply eq_in_map in Hn.
  rewrite Hm Hn.
  destruct (coprime p m)eqn:p_coprime_m.
    apply/orP.
    left.
    apply/allP.
    move=> b b_in.
    move/nthP in b_in.
    destruct (b_in false) as [i Hb Hb0].
    rewrite size_map in Hb.
    rewrite (nth_map (0, 0) false) // in Hb0.
    remember (nth (0, 0) (prime_decomp m) i) as q ; destruct q as [q a].
    rewrite -Hb0 eq_sym bool_eq_true.
    apply coprime_dvdr with m ; last by [].
    apply (mem_nth (0, 0)) in Hb.
    rewrite -Heqq in Hb.
    apply mem_prime_decomp in Hb.
    apply dvdn_exp2 with a ; by destruct Hb.
  destruct (coprime p n)eqn:p_coprime_n.
    apply/orP.
    right.
    apply/allP.
    move=> b b_in.
    move/nthP in b_in.
    destruct (b_in false) as [i Hb Hb0].
    rewrite size_map in Hb.
    rewrite (nth_map (0, 0) false) // in Hb0.
    remember (nth (0, 0) (prime_decomp n) i) as q ; destruct q as [q a].
    rewrite -Hb0 eq_sym bool_eq_true.
    apply coprime_dvdr with n ; last by [].
    apply (mem_nth (0, 0)) in Hb.
    rewrite -Heqq in Hb.
    apply mem_prime_decomp in Hb.
    apply dvdn_exp2 with a ; by destruct Hb.
  rewrite prime_coprime // in p_coprime_m.
  apply negbRL in p_coprime_m.
  rewrite prime_coprime // in p_coprime_n.
  apply negbRL in p_coprime_n.
  pose proof (coprime_dvdr p_coprime_n m_coprime_n) as m_coprime_p.
  pose proof (coprime_dvdl p_coprime_m m_coprime_p) as p_coprime_p.
  rewrite prime_coprime // dvdnn // in p_coprime_p.
  apply/allP ; move=> f f_in.
    move/nthP in f_in.
    pose proof (f_in 0) as [i Hi Hf].
    rewrite size_map in Hi.
    rewrite (nth_map (0, 0)) // in Hf.
    remember (nth (0, 0) (prime_decomp n) i) as q ; destruct q as [q a].
    rewrite -Hf /=.
    rewrite expn_gt0.
    apply (mem_nth (0, 0)) in Hi.
    rewrite -Heqq in Hi.
    apply mem_prime_decomp in Hi.
    destruct Hi as [q_prime _ _].
    rewrite prime_gt0 //.
  apply/allP ; move=> f f_in.
    move/nthP in f_in.
    pose proof (f_in 0) as [i Hi Hf].
    rewrite size_map in Hi.
    rewrite (nth_map (0, 0)) // in Hf.
    remember (nth (0, 0) (prime_decomp m) i) as q ; destruct q as [q a].
    rewrite -Hf /=.
    rewrite expn_gt0.
    apply (mem_nth (0, 0)) in Hi.
    rewrite -Heqq in Hi.
    apply mem_prime_decomp in Hi.
    destruct Hi as [q_prime _ _].
    rewrite prime_gt0 //.
Qed.

Lemma mem_prime_decomp2 : forall m p e, (p, e) \in prime_decomp m -> logn p m = e.
Proof.
  move=> m p e H.
  rewrite prime_decompE in H.
  move/nthP in H.
  destruct (H (0, 0)) as [i Hi Hf].
  rewrite size_map in Hi.
  apply (nth_map 0 (0, 0) (fun p => (p, logn p m))) in Hi.
  rewrite Hf in Hi.
  by inversion Hi.
Qed.


Lemma prime_decomp_coprime :
  forall m n, m > 0 -> n > 0
  -> coprime m n
  -> perm_eq (prime_decomp (m * n)) ((prime_decomp m) ++ (prime_decomp n)).
Proof.
  move=> m n m_gt_0 n_gt_0 m_coprime_n.
  apply uniq_perm ; first apply prime_decomp_uniq.
  rewrite cat_uniq.
  apply/and3P.
  split ; first apply prime_decomp_uniq ; last apply prime_decomp_uniq.
  apply/hasPn.
  move=> [p a] H.
  rewrite coprime_has_primes // in m_coprime_n.
  move/hasPn in m_coprime_n.
  pose proof (m_coprime_n p) as H0.
  rewrite /= -[p]/((p, a).1) (map_f fst) // in H0.
  pose proof (H0 isT) as H0.
  move/memPn in H0.
  pose proof (H0 p) as H0.
  apply/negP ; move=> H1.
  apply (map_f fst) in H1.
  apply H0 in H1.
  by move/negP in H1.
  move=> [p a].
  apply/eqP/equiv_eqP.
  apply nthP with (x0:=(0, 0)).
  apply nthP with (x0:=(0, 0)).
  split ; move=> [i H H0] ; apply (mem_nth (0, 0)) in H as H' ;
    rewrite H0 in H' ; rewrite ?prime_decompE in H H0.
  apply mem_prime_decomp in H'.
  rewrite size_map in H.
  rewrite (nth_map 0 (0, 0)) // in H0.
  inversion H0.
  apply/nthP.
  rewrite H0.
  assert (exists2 i, i < size (primes (m * n)) & nth 0 (primes (m * n)) i = p) as H4 ; first by exists i.
  move/nthP in H4.
  rewrite mem_cat.
  rewrite H2 lognM // in H3.
  pose proof (coprime_logn_or m n m_gt_0 n_gt_0 m_coprime_n p) as Hp.
  move/orP in Hp.
  apply/orP.
  destruct Hp as [Hp|Hp] ; move/eqP in Hp ; rewrite Hp in H3.
    right.
    rewrite add0n in H3.
    rewrite prime_decompE -H3.
    apply (map_f (fun p => (p, logn p n))).
    rewrite -logn_gt0 H3 ; by destruct H'.
    left.
    rewrite addn0 in H3.
    rewrite prime_decompE -H3.
    apply (map_f (fun p => (p, logn p m))).
    rewrite -logn_gt0 H3 ; by destruct H'.
  apply/nthP.
  pose proof (coprime_logn_or m n m_gt_0 n_gt_0 m_coprime_n p) as H1.
  move/orP in H1.
  rewrite mem_cat in H'.
  move/orP in H'.
  destruct H1 as [H1|H1] ; move/eqP in H1 ; destruct H' as [H'|H'].
    apply mem_prime_decomp2 in H' as H2.
    apply mem_prime_decomp in H'.
    rewrite -H2 H1 in H' ; by destruct H'.
    apply mem_prime_decomp2 in H' as Ha.
    rewrite -Ha prime_decompE.
    rewrite -(addn0 (logn p n)) -H1 -lognM // mulnC.
    apply (map_f (fun p => (p, logn p (m * n)))).
    rewrite primes_mul //.
    apply/orP.
    right.
    rewrite -[p]/((p, a).1).
    by apply map_f.
    apply mem_prime_decomp2 in H' as Ha.
    rewrite -Ha prime_decompE.
    rewrite -(add0n (logn p m)) -H1 -lognM // mulnC.
    apply (map_f (fun p => (p, logn p (m * n)))).
    rewrite primes_mul //.
    apply/orP.
    left.
    rewrite -[p]/((p, a).1).
    by apply map_f.
    apply mem_prime_decomp2 in H' as H2.
    apply mem_prime_decomp in H'.
    rewrite -H2 H1 in H' ; by destruct H'.
Qed.

Lemma divisors_div_dvdn : forall n d, 0 < n -> d \in [seq n %/ d | d <- divisors n] -> d %| n.
Proof.
  move=> n d n_gt_0 d_in_ddiv.
  move/mapP in d_in_ddiv.
  destruct d_in_ddiv as [d' d'_dvd_n d_eq_n_div_d'].
  rewrite d_eq_n_div_d'.
  apply dvdn_div.
  rewrite dvdn_divisors //.
Qed.

Lemma divisors_gt0 : forall n d, d \in divisors n -> d > 0.
Proof.
  case=> [|n] d d_dvd_n.
    unfold divisors in d_dvd_n.
    simpl in d_dvd_n.
    rewrite mem_seq1 in d_dvd_n.
    move/eqP in d_dvd_n.
    by rewrite d_dvd_n.
  rewrite -dvdn_divisors in d_dvd_n ; last by apply ltn0Sn.
  apply dvdn_gt0 with (n.+1) ; last by [].
  apply ltn0Sn.
Qed.

Lemma mem_divisors_dvdn : forall n d, d \in divisors n -> d %| n.
Proof.
  case=> [|n] d d_dvd_n ; first by apply dvdn0.
  by rewrite dvdn_divisors.
Qed.

Lemma div_divisors_perm : forall n, 0 < n -> perm_eq [seq n %/ d | d <- divisors n] (divisors n).
Proof.
  move=> n n_gt_0.
  apply uniq_perm.
  rewrite map_inj_in_uniq ; first by apply divisors_uniq.
  move=> d d' d_dvd_n d'_dvd_n n_div_d_eq_n_div_d'.
  assert (0 < d) as d_gt_0 by
    by apply divisors_gt0 with n.
  assert (0 < d') as d'_gt_0 by
    by apply divisors_gt0 with n.
  assert (d' * (n %/ d) = n) as H.
    rewrite n_div_d_eq_n_div_d' muln_divA.
    by rewrite -{2}(muln1 d') divnMl // divn1.
    by apply: mem_divisors_dvdn.
  assert (d' * n = d * n) as H0.
    rewrite -{2}H mulnA (mulnC d d') -mulnA (mulnC d) divn_mulAC.
    rewrite mulnK //.
    by apply: mem_divisors_dvdn.
  move/eqP in H0.
  apply/eqP ; rewrite eq_sym -(eqn_pmul2r n_gt_0) //.
  apply divisors_uniq.
  move=> d.
  apply/eqP/equiv_eqP.
  apply/nthP ; apply 0.
  apply/idP.
  split.
    move=> [i Hi H].
    rewrite size_map in Hi.
    rewrite ?(nth_map 0) // in H.
    apply (mem_nth 0) in Hi as H0.
    remember (nth 0 (divisors n) i) as m eqn:Heqm ; rewrite -Heqm in H0.
    rewrite -dvdn_divisors //.
    rewrite -dvdn_divisors // in H0.
    apply dvdn_div in H0.
    by rewrite -H.
    move=> d_dvd_n.
    apply/nthP.
    rewrite -dvdn_divisors // in d_dvd_n.
    assert (d = n %/ (n %/ d)).
      rewrite divnA // -divn_mulAC.
      rewrite divnn n_gt_0 mul1n //.
      apply dvdnn.
    rewrite H (map_f (fun d => n %/ d)) // -dvdn_divisors //.
    by apply dvdn_div.
Qed.

Lemma fact_prod : forall n, n`! = \prod_(1 <= i < n.+1) i.
Proof.
  elim=> [|n IHn] ; first by rewrite BigOp.bigopE.
  assert (1 <= n.+1) as Sn_ge_1 by by [].
  apply/eqP ; rewrite eq_sym ; apply/eqP.
  rewrite factS IHn (big_cat_nat _ _ _ Sn_ge_1) //=.
  rewrite mulnC {1}BigOp.bigopE /=.
  unfold index_iota at 1.
  by rewrite -[n.+2]/(2 + n) -{2}[n.+1]/(1 + n) subnDr /= muln1.
Qed.

Lemma divn_primepow_eq0 :
  forall n p a, prime p
  -> n > 0
  -> a > trunc_log p n -> n %/ p ^ a = 0.
Proof.
  move=> n p a p_prime n_gt_0 a_gt_logn_p_n.
  apply divn_small.
  apply ltn_leq_trans with (p ^ (trunc_log p n).+1) ; rewrite /=.
  pose proof (trunc_log_bounds (prime_gt1 p_prime) n_gt_0) as H.
  move/andP in H ; by destruct H.
  rewrite leq_exp2l //.
  apply (prime_gt1 p_prime).
Qed.

Lemma leq_logn_trunc_log :
  forall n p, n > 0
  -> p > 1
  -> logn p n <= trunc_log p n.
Proof.
  move=> n p n_gt_0 p_prime.
  apply trunc_log_max ;
    first by [].
  apply dvdn_leq ;
    first by [].
  apply pfactor_dvdnn.
Qed.

Lemma leq_trunc_log :
  forall p m n, p > 1
  -> 0 < m <= n
  -> trunc_log p m <= trunc_log p n.
Proof.
  move=> p m n p_gt_1 m_ge_n_gt_0.
  move/andP in m_ge_n_gt_0.
  destruct m_ge_n_gt_0 as [m_gt_0 m_le_n].
  apply trunc_log_max ; first by [].
  apply leq_trans with m ; last by [].
  by apply trunc_logP.
Qed.

Lemma expn_ltn_exp :
  forall m n p, 1 < p
  -> p ^ n <= m
  -> n < m.
Proof.
  move=> m n ; move: m.
  elim: n => [|n IHn] m p p_gt_1 p_n_le_m.
    rewrite expn0 in p_n_le_m ;
    by apply leq_trans with 1.
  destruct m.
  rewrite leqn0 expn_eq0 in p_n_le_m.
  move/andP in p_n_le_m.
  destruct p_n_le_m as [p_eq_0 _].
  move/eqP in p_eq_0.
  by rewrite p_eq_0 in p_gt_1.
  assert (m > 0) as m_gt_0.
    apply ltn_leq_trans with 1 ; first by [].
    assert (p <= m.+1) as p_le_Sm.
      apply leq_trans with (p ^ n.+1) ; last by [].
      rewrite -{1}(expn1 p).
      by apply leq_pexp2l ; first by apply leq_trans with 2.
    by assert (1 < m.+1) by by apply ltn_leq_trans with p.
  apply (leq_div2r p) in p_n_le_m.
  rewrite expnS -{3}(muln1 p) divnMl in p_n_le_m ; last by apply leq_trans with 2.
  rewrite divn1 in p_n_le_m.
  apply IHn with p ; first by [].
  apply leq_trans with (m.+1 %/ p) ; first by [].
  rewrite -addn1.
  apply leq_trans with (m %/ p + 1 %/ p + 1) ; first by apply leq_divDl.
  assert (1 %/ p = 0) as H by by apply divn_small.
  rewrite H addn0 addn1 ltn_divLR ; last by apply leq_trans with 2.
  by apply ltn_Pmulr.
Qed.

Lemma prime_decomp_injective :
  forall m n, 0 < m -> 0 < n
  -> prime_decomp m = prime_decomp n
  -> m = n.
Proof.
  move=> m n m_gt_0 n_gt_0 H.
  by rewrite (prod_prime_decomp m_gt_0) (prod_prime_decomp n_gt_0) H.
Qed.

Lemma logn_eq :
  forall m n, 0 < m -> 0 < n
  -> (forall p, logn p m = logn p n)
  -> m = n.
Proof.
  move=> m n m_gt_0 n_gt_0 H.
  apply prime_decomp_injective ; [by []|by []|].
  rewrite ?prime_decompE.
  apply eq_map_eq.
    move=> p ; by rewrite H.
  apply eq_sorted with ltn.
    by move ; apply ltn_trans.
    by move ; apply anti_ltn.
    apply sorted_primes.
    apply sorted_primes.
    apply uniq_perm.
    apply primes_uniq.
    apply primes_uniq.
    move=> p.
    by rewrite ?mem_primes2 H.
Qed.

Lemma logn_eq_prime :
  forall m n, 0 < m -> 0 < n
  -> (forall p, prime p -> logn p m = logn p n)
  -> m = n.
Proof.
  move=> m n m_gt_0 n_gt_0 H.
  apply prime_decomp_injective ; [by []|by []|].
  rewrite ?prime_decompE.
  apply eq_in_map_eq.
  move=> p p_in.
  rewrite H //.
  rewrite mem_primes in p_in.
  move/and3P in p_in.
  by destruct p_in.
  apply eq_sorted with ltn.
    by move ; apply ltn_trans.
    by move ; apply anti_ltn.
    apply sorted_primes.
    apply sorted_primes.
    apply uniq_perm.
    apply primes_uniq.
    apply primes_uniq.
    move=> p.
    rewrite ?mem_primes2.
    destruct (prime p)eqn:p_prime.
    by rewrite H.
    unfold logn.
    by rewrite p_prime.
Qed.

Section logn_dvdn_prime.

Local Lemma logn_dvdn_prime_aux {T : eqType} :
  forall p f (s : seq T), {in s, forall x, ltn 0 (f x)}
  -> (p \in primes (\prod_(x <- s) f x)) = \big[orb/false]_(x <- s) (p \in primes (f x)).
Proof.
  move=> p f ; elim=> [|h s IHs] Hf.
    by rewrite ?big_nil.
  rewrite ?big_cons primes_mul.
  rewrite IHs //.
  move=> x x_in.
    apply Hf.
    by apply mem_behead.
  apply Hf ; by apply mem_head.
  apply ltn_0_prod_f.
  apply/allP.
  move=> x x_in.
  move/nthP in x_in.
  destruct (x_in 0) as [i Hi Hx].
  rewrite size_map in Hi.
  rewrite (nth_map h) // in Hx.
  rewrite -Hx.
  apply Hf.
  rewrite -[nth h s i]/(nth h (h::s) i.+1).
  by apply mem_nth.
Qed.

Local Lemma logn_dvdn_prime_aux3 :
     forall m primes_m, primes_m = primes m -> 0 < m
  -> forall n primes_n, primes_n = primes n -> 0 < n
  -> (forall p, prime p -> logn p m <= logn p n)
  -> m %| n.
Proof.
  move=> m primes_m ; move: m.
  elim: primes_m => [|p primes_m IHprimes_m].
    move=> m Hprimes_m m_gt_0 n primes_n Hprimes_n n_gt_0 H.
    by rewrite (prod_prime_decomp m_gt_0) ?prime_decompE big_map -Hprimes_m big_nil dvd1n.
  move=> m Hprimes_m m_gt_0 n primes_n ; move: n.
  elim: primes_n => [|q primes_n IHprimes_n].
    move=> n Hprimes_n n_gt_0 H.
    assert (n = 1) as n_eq_1 by
      by rewrite (prod_prime_decomp n_gt_0) ?prime_decompE big_map -Hprimes_n big_nil.
    rewrite n_eq_1 dvdn1.
    apply/eqP.
    apply logn_eq_prime ; [by []|by []|].
    move=> r r_prime.
    rewrite logn1.
    apply/eqP.
    rewrite -leqn0.
    rewrite n_eq_1 in H.
    apply leq_trans with (logn r 1) ; first by apply H.
    by rewrite logn1.
  move=> n Hprimes_n n_gt_0 H.
  assert (prime p) as p_prime.
    assert (p \in primes m) as p_prime by by rewrite -Hprimes_m mem_head.
    rewrite mem_primes in p_prime.
    move/and3P in p_prime.
    by destruct p_prime.
  assert (prime q) as q_prime.
    assert (q \in primes n) as q_prime by by rewrite -Hprimes_n mem_head.
    rewrite mem_primes in q_prime.
    move/and3P in q_prime.
    by destruct q_prime.
  assert (p = pdiv m) as p_pdiv_m by
    by unfold pdiv ; rewrite -Hprimes_m /=.
  assert (q = pdiv n) as q_pdiv_n by
    by unfold pdiv ; rewrite -Hprimes_n /=.
  assert (q <= p) as q_le_p.
    rewrite q_pdiv_n.
    apply pdiv_min_dvd ; first by apply prime_gt1.
  pose proof (mem_primes p n) as p_in_primes_n.
  rewrite p_prime n_gt_0 /= in p_in_primes_n.
  rewrite -p_in_primes_n -logn_gt0.
  apply leq_trans with (logn p m) ; last by apply H.
  by rewrite logn_gt0 mem_primes p_prime m_gt_0 /= p_pdiv_m pdiv_dvd.
  rewrite leq_eqVlt eq_sym in q_le_p.
  rewrite (prod_prime_decomp m_gt_0) (prod_prime_decomp n_gt_0)
    ?prime_decompE big_map.
  assert (
    \prod_(f <- [seq (p, logn p n) | p <- primes n]) f.1 ^ f.2
    = \prod_(j <- primes n) (j, logn j n).1 ^ (j, logn j n).2
    ) as step by by rewrite big_map. rewrite step /= ; clear step.
  rewrite -Hprimes_m -Hprimes_n ?big_cons.
  assert (0 < \prod_(j <- primes_m) j ^ logn j m) as prod_m_gt_0.
    apply ltn_0_prod_f.
    apply/allP.
    move=> f f_in.
    move/nthP in f_in.
    destruct (f_in 0) as [i Hi Hf].
    rewrite size_map in Hi.
    rewrite (nth_map 0) // in Hf.
    rewrite -Hf /= -(expn0 (nth 0 primes_m i)).
    apply leq_pexp2l ; last by [].
    apply prime_gt0.
    apply (mem_nth 0) in Hi.
    apply (mem_cons _ p) in Hi.
    rewrite Hprimes_m mem_primes in Hi.
    move/and3P in Hi.
    by destruct Hi.
  assert (0 < \prod_(j <- primes_n) j ^ logn j n) as prod_n_gt_0.
    apply ltn_0_prod_f.
    apply/allP.
    move=> f f_in.
    move/nthP in f_in.
    destruct (f_in 0) as [i Hi Hf].
    rewrite size_map in Hi.
    rewrite (nth_map 0) // in Hf.
    rewrite -Hf /= -(expn0 (nth 0 primes_n i)).
    apply leq_pexp2l ; last by [].
    apply prime_gt0.
    apply (mem_nth 0) in Hi.
    apply (mem_cons _ q) in Hi.
    rewrite Hprimes_n mem_primes in Hi.
    move/and3P in Hi.
    by destruct Hi.
  assert (primes_m = primes (\prod_(j <- primes_m) j ^ logn j m)) as Hprimes_prod_m.
    apply eq_sorted with ltn ;
      first by move ; apply ltn_trans.
      by move ; apply anti_ltn.
    pose proof (sorted_primes m) as primes_m_sorted.
    rewrite -Hprimes_m /= in primes_m_sorted.
    by apply path_sorted in primes_m_sorted.
    apply sorted_primes.
    apply uniq_perm.
    pose proof (primes_uniq m) as primes_m_uniq.
    rewrite -Hprimes_m /= in primes_m_uniq.
    move/andP in primes_m_uniq.
    by destruct primes_m_uniq.
    apply primes_uniq.
    move=> r.
    rewrite logn_dvdn_prime_aux.
    rewrite mem_big_eq.
    apply eq_big_seq.
    move=> s s_in.
    apply (mem_cons _ p) in s_in.
    rewrite Hprimes_m mem_primes in s_in.
    move/and3P in s_in.
    destruct s_in as [s_prime _ s_dvd_m].
    destruct (s == r)eqn:s_eq_r.
      move/eqP in s_eq_r.
      subst.
      rewrite primes_exp.
      apply primes_prime in s_prime.
      by rewrite s_prime mem_seq1 eq_refl.
      rewrite logn_gt0 mem_primes.
      by apply/and3P.
      rewrite mem_primes.
      destruct (prime r)eqn:r_prime ; last by [].
      assert (0 < s ^ logn s m) as s_logn_gt_0 by
        by rewrite -(expn0 s).
      rewrite s_logn_gt_0 /=.
      destruct (r %| s ^ logn s m)eqn:r_dvd_s_logn ; last by [].
      pose proof r_dvd_s_logn as H0.
      move/dvdn_pfactor in H0.
      destruct (H0 s_prime) as [e e_le_logn r_eq_s_e] ; clear H0.
      destruct e as [|[|e]].
        rewrite expn0 in r_eq_s_e.
        by rewrite r_eq_s_e in r_prime.
        rewrite expn1 in r_eq_s_e.
        by rewrite r_eq_s_e eq_refl in s_eq_r.
        rewrite expnS in r_eq_s_e.
        exfalso ; assert (~~ prime r) as r_not_prime ;
          last by rewrite r_prime in r_not_prime.
        apply/primePn ; right.
        exists s ; last rewrite r_eq_s_e dvdn_mulr // dvdnn.
        apply/andP ; split ; first by apply prime_gt1.
        rewrite -(muln1 s) r_eq_s_e ltn_mul2l.
        apply/andP ; split ; first by apply prime_gt0.
        rewrite -(expn0 s) ltn_exp2l ; last by apply prime_gt1.
        apply ltn0Sn.
    move=> s s_in /=.
      apply (mem_cons _ p) in s_in.
      rewrite Hprimes_m mem_primes in s_in.
      move/and3P in s_in.
      destruct s_in as [s_prime _ _].
      rewrite -(expn0 s) leq_exp2l //.
      by apply prime_gt1.
  assert (primes_n = primes (\prod_(j <- primes_n) j ^ logn j n)) as Hprimes_prod_n.
    apply eq_sorted with ltn ;
      first by move ; apply ltn_trans.
      by move ; apply anti_ltn.
    pose proof (sorted_primes n) as primes_n_sorted.
    rewrite -Hprimes_n /= in primes_n_sorted.
    by apply path_sorted in primes_n_sorted.
    apply sorted_primes.
    apply uniq_perm.
    pose proof (primes_uniq n) as primes_n_uniq.
    rewrite -Hprimes_n /= in primes_n_uniq.
    move/andP in primes_n_uniq.
    by destruct primes_n_uniq.
    apply primes_uniq.
    move=> r.
    rewrite logn_dvdn_prime_aux.
    rewrite mem_big_eq.
    apply eq_big_seq.
    move=> s s_in.
    apply (mem_cons _ q) in s_in.
    rewrite Hprimes_n mem_primes in s_in.
    move/and3P in s_in.
    destruct s_in as [s_prime _ s_dvd_n].
    destruct (s == r)eqn:s_eq_r.
      move/eqP in s_eq_r.
      subst.
      rewrite primes_exp.
      apply primes_prime in s_prime.
      by rewrite s_prime mem_seq1 eq_refl.
      rewrite logn_gt0 mem_primes.
      by apply/and3P.
      rewrite mem_primes.
      destruct (prime r)eqn:r_prime ; last by [].
      assert (0 < s ^ logn s n) as s_logn_gt_0 by
        by rewrite -(expn0 s).
      rewrite s_logn_gt_0 /=.
      destruct (r %| s ^ logn s n)eqn:r_dvd_s_logn ; last by [].
      pose proof r_dvd_s_logn as H0.
      move/dvdn_pfactor in H0.
      destruct (H0 s_prime) as [e e_le_logn r_eq_s_e] ; clear H0.
      destruct e as [|[|e]].
        rewrite expn0 in r_eq_s_e.
        by rewrite r_eq_s_e in r_prime.
        rewrite expn1 in r_eq_s_e.
        by rewrite r_eq_s_e eq_refl in s_eq_r.
        rewrite expnS in r_eq_s_e.
        exfalso ; assert (~~ prime r) as r_not_prime ;
          last by rewrite r_prime in r_not_prime.
        apply/primePn ; right.
        exists s ; last rewrite r_eq_s_e dvdn_mulr // dvdnn.
        apply/andP ; split ; first by apply prime_gt1.
        rewrite -(muln1 s) r_eq_s_e ltn_mul2l.
        apply/andP ; split ; first by apply prime_gt0.
        rewrite -(expn0 s) ltn_exp2l ; last by apply prime_gt1.
        apply ltn0Sn.
    move=> s s_in /=.
      apply (mem_cons _ q) in s_in.
      rewrite Hprimes_n mem_primes in s_in.
      move/and3P in s_in.
      destruct s_in as [s_prime _ _].
      rewrite -(expn0 s) leq_exp2l //.
      by apply prime_gt1.
  destruct (p == q)eqn:p_eq_q.
  move/eqP in p_eq_q ; rewrite p_eq_q.
  apply dvdn_mul.
  rewrite dvdn_Pexp2l ; last by apply prime_gt1.
  by apply H.
  apply (IHprimes_m (\prod_(j <- primes_m) j ^ logn j m) Hprimes_prod_m prod_m_gt_0
    (\prod_(j <- primes_n) j ^ logn j n) (primes_n) Hprimes_prod_n) ; first by [].
  move=> s s_prime.
  rewrite ?logn_prod_f.
  rewrite (eq_big_seq (fun p => if p == s then logn p m else 0)).
  assert (
    \sum_(x <- primes_n) logn s (x ^ logn x n)
    = \sum_(i <- primes_n) (if i == s then logn i n else 0)
    ) as step ; last rewrite step ; last clear step.
  rewrite (eq_big_seq (fun p => if p == s then logn p n else 0)) //.
  move=> r r_in.
    apply (mem_cons _ q) in r_in.
    rewrite Hprimes_n mem_primes in r_in.
    move/and3P in r_in.
    destruct r_in as [r_prime _ r_dvd_n].
    rewrite lognX (logn_prime s r_prime) eq_sym.
    case: (r == s) ; by rewrite ?muln1 ?muln0.
  destruct (s \in primes_m)eqn:s_in_primes_m ; first destruct (s \in primes_n)eqn:s_in_primes_n.
    rewrite (big_rem _ s_in_primes_m) /= (big_rem _ s_in_primes_n) /= eq_refl.
    apply leq_add ; first by apply H.
    rewrite (eq_big_seq (fun p => 0)).
    rewrite -(big_map_id _ _ (fun p => 0) _ predT) /=.
    by rewrite map_const -sumnE sumn_nseq mul0n.
    move=> r r_in.
      destruct (r == s)eqn:r_eq_s ; last by [].
      move/eqP in r_eq_s.
      rewrite r_eq_s mem_rem_uniqF // in r_in.
      pose proof (primes_uniq m) as uniq_primes_m.
      rewrite -Hprimes_m /= in uniq_primes_m.
      move/andP in uniq_primes_m.
      by destruct uniq_primes_m.
    exfalso.
    destruct (s \in primes n)eqn:s_eq_q.
    rewrite -Hprimes_n mem_head_or_behead s_in_primes_n orbF in s_eq_q.
    move/eqP in s_eq_q.
    rewrite s_eq_q in s_in_primes_m.
    pose proof (primes_uniq m) as uniq_primes_m.
    by rewrite -Hprimes_m cons_uniq p_eq_q  s_in_primes_m in uniq_primes_m.
    rewrite -logn_gt0 in s_eq_q.
    assert (s \in primes m) as s_in by
      by rewrite -Hprimes_m ; by apply mem_cons.
    rewrite leqNgt in s_eq_q.
    assert (logn s n < 1) as H0 by
      by destruct (logn s n < 1).
    rewrite -logn_gt0 in s_in.
    assert (0 < 0) ; last by [].
    apply leq_trans with (logn s m) ; first by [].
    rewrite ltnS in H0.
    apply leq_trans with (logn s n) ; last by [].
    by apply H.
    rewrite (eq_big_seq (fun p => 0)).
    rewrite -(big_map_id _ _ (fun p => 0) _ predT) /=.
    by rewrite map_const -sumnE sumn_nseq mul0n.
    move=> r r_in_primes_m.
    destruct (r == s)eqn:r_eq_s ; last by [].
    move/eqP in r_eq_s.
    by rewrite r_eq_s s_in_primes_m in r_in_primes_m.
    move=> r r_in_primes_m.
    assert (r \in primes m) as r_in.
      rewrite -Hprimes_m ; by apply mem_cons.
    rewrite mem_primes in r_in.
    move/and3P in r_in.
    destruct r_in as [r_prime _ r_dvd_m].
    destruct (r == s)eqn:r_eq_s.
    move/eqP in r_eq_s.
    by rewrite r_eq_s lognX lognn s_prime muln1.
    by rewrite lognX (logn_prime s) // eq_sym r_eq_s muln0.
  apply/allP.
    move=> f f_in.
    move/nthP in f_in.
    destruct (f_in 0) as [i Hi Hf].
    rewrite size_map in Hi.
    rewrite (nth_map 0) // in Hf.
    remember (nth 0 primes_n i) as r eqn:Heqr.
    rewrite -Hf /=.
    rewrite -(expn0 r).
    apply leq_pexp2l ; last by [].
    apply (mem_nth 0) in Hi.
    rewrite -Heqr in Hi.
    apply (mem_cons _ q) in Hi.
    rewrite Hprimes_n in Hi.
    apply prime_gt0.
    rewrite mem_primes in Hi.
    move/and3P in Hi.
    by destruct Hi.
  apply/allP.
    move=> f f_in.
    move/nthP in f_in.
    destruct (f_in 0) as [i Hi Hf].
    rewrite size_map in Hi.
    rewrite (nth_map 0) // in Hf.
    remember (nth 0 primes_m i) as r eqn:Heqr.
    rewrite -Hf /=.
    rewrite -(expn0 r).
    apply leq_pexp2l ; last by [].
    apply (mem_nth 0) in Hi.
    rewrite -Heqr in Hi.
    apply (mem_cons _ p) in Hi.
    rewrite Hprimes_m in Hi.
    apply prime_gt0.
    rewrite mem_primes in Hi.
    move/and3P in Hi.
    by destruct Hi.
  rewrite /= in q_le_p.
  apply dvdn_mull.
  assert (
    \prod_(p <- primes m) p ^ logn p m
    = p ^ logn p m * \prod_(j <- primes_m) j ^ logn j m
    ) as step ; last rewrite -step ; last clear step.
    by rewrite -Hprimes_m big_cons.
  assert (
    m =\prod_(p0 <- primes m) p0 ^ logn p0 m
    ) as step ; last rewrite -step ; last clear step.
  rewrite {1}(prod_prime_decomp m_gt_0) prime_decompE big_map //.
  apply (IHprimes_n (\prod_(j <- primes_n) j ^ logn j n) Hprimes_prod_n) ; first by [].
  move=> s s_prime.
  rewrite logn_prod_f.
  destruct (s \in primes n)eqn:s_in.
  pose proof s_in as s_dvd_n.
  rewrite -Hprimes_n mem_head_or_behead in s_in.
  rewrite mem_primes in s_dvd_n.
  move/and3P in s_dvd_n.
  destruct s_dvd_n as [_ _ d_dvd_n].
  move/orP in s_in.
  destruct s_in as [s_eq_q|s_in].
  move/eqP in s_eq_q.
  subst.
  apply leq_trans with 0 ; last by [].
  rewrite leqNgt.
  apply/negP.
  move=> pdiv_n_in_primes_m.
  rewrite logn_gt0 mem_primes in pdiv_n_in_primes_m.
  move/and3P in pdiv_n_in_primes_m.
  destruct pdiv_n_in_primes_m as [_ _ pdiv_n_dvd_m].
  rewrite ltnNge in q_le_p.
  move/negP in q_le_p.
  apply: q_le_p.
  apply pdiv_min_dvd ; last by [].
  by apply prime_gt1.
  rewrite (big_rem _ s_in) /= -(addn0 (logn s m)).
  apply leq_add ; last by [].
  rewrite lognX (logn_prime s s_prime) eq_refl muln1.
  by apply H.
  apply leq_trans with 0 ; last by [].
  rewrite leqNgt.
  apply/negP.
  move=> s_dvd_m.
  assert (0 < logn s n) as s_dvd_n.
    apply leq_trans with (logn s m) ; first by [].
    by apply H.
  rewrite logn_gt0 in s_dvd_n.
  by rewrite s_dvd_n in s_in.
  apply/allP.
    move=> f f_in.
    move/nthP in f_in.
    destruct (f_in 0) as [i Hi Hf].
    rewrite size_map in Hi.
    rewrite (nth_map 0) // in Hf.
    remember (nth 0 primes_n i) as r eqn:Heqr.
    rewrite -Hf /=.
    rewrite -(expn0 r).
    apply leq_pexp2l ; last by [].
    apply (mem_nth 0) in Hi.
    rewrite -Heqr in Hi.
    apply (mem_cons _ q) in Hi.
    rewrite Hprimes_n in Hi.
    apply prime_gt0.
    rewrite mem_primes in Hi.
    move/and3P in Hi.
    by destruct Hi.
Qed.

Lemma logn_dvdn_prime :
  forall m n, 0 < m -> 0 < n
  -> (forall p, prime p -> logn p m <= logn p n)
  -> m %| n.
Proof.
  move=> m n m_gt_0 n_gt_0 H.
  assert (primes m = primes m) as primes_m by by [].
  assert (primes n = primes n) as primes_n by by [].
  apply (logn_dvdn_prime_aux3 m (primes m) primes_m m_gt_0 n (primes n) primes_n n_gt_0 H).
Qed.

End logn_dvdn_prime.

Lemma logn_leq_dvdn :
  forall m n p, 0 < m -> 0 < n
  -> m %| n
  -> logn p m <= logn p n.
Proof.
  move=> m n p m_gt_0 n_gt_0 m_dvd_n.
  destruct (prime p)eqn:p_prime ; last unfold logn ; last by rewrite p_prime.
  rewrite ?logn_count_dvd //.
  apply leq_trans with (\sum_(1 <= k < m) (p ^ k %| m) + \sum_(m <= k < n) (p ^ k %| m)) ;
    first apply leq_addr.
  rewrite -big_cat_nat //=.
  move: (index_iota 1 n) ; elim=> [|a s IHs] ; first by rewrite big_nil.
  rewrite ?big_cons.
  apply leq_add ; last by [].
  destruct (p ^ a %| n)eqn:p_a_dvd_n ; first by case: (p ^ a %| m).
  destruct (p ^ a %| m)eqn:p_a_dvd_m ; last by [].
  assert (p ^ a %| n) as absurd by by apply dvdn_trans with m.
  by rewrite absurd in p_a_dvd_n.
  by apply dvdn_leq.
Qed.


Lemma minn_or : forall m n, (minn m n == m) || (minn m n == n).
Proof.
  move=> m n.
  pose proof (leq_total m n) as H.
  move/orP in H.
  apply/orP.
  destruct H ; [left | right] ; apply/eqP.
  by apply/minn_idPl.
  by apply/minn_idPr.
Qed.

Lemma gcdn_div :
  forall m n p, 0 < p -> p %| m -> p %| n
  -> gcdn (m %/ p) (n %/ p) = gcdn m n %/ p.
Proof.
  move=> m n p p_gt_0 p_dvd_m p_dvd_n.
  apply gcdn_def.
  rewrite dvdn_divRL // mulnC muln_divA ; last by rewrite dvdn_gcd p_dvd_m p_dvd_n.
  by rewrite mulnC mulnK // dvdn_gcdl.
  rewrite dvdn_divRL // mulnC muln_divA ; last by rewrite dvdn_gcd p_dvd_m p_dvd_n.
  by rewrite mulnC mulnK // dvdn_gcdr.
  move=> d d_dvd_m_p d_dvd_n_p.
  move/dvdnP in d_dvd_m_p ; destruct d_dvd_m_p as [k Hk].
  move/dvdnP in d_dvd_n_p ; destruct d_dvd_n_p as [l Hl].
  rewrite dvdn_divRL ; last by rewrite dvdn_gcd p_dvd_m p_dvd_n.
  move/eqP in Hk.
  move/eqP in Hl.
  rewrite -?eqn_mul // in Hk, Hl.
  move/eqP in Hk.
  move/eqP in Hl.
  rewrite dvdn_gcd.
  apply/andP ; split ; apply/dvdnP ;
    [exists k ; rewrite Hk | exists l ; rewrite Hl] ; ring.
Qed.

Lemma strong_induction :
  forall (P : nat -> Prop),
  P 0
  -> (forall n, (forall m, m < n -> P m) -> P n)
  -> forall n, P n.
Admitted.

Lemma subn_minl : left_distributive subn minn.
Proof.
  elim=> [|m IHm] ; elim=> [|n IHn] ; elim=> [|p IHp] //.
    by rewrite ?sub0n min0n.
    by rewrite subn0.
    by rewrite minnSS -add1n -?(add1n m) -?(add1n n) -?(add1n p) ?subnDl.
Qed.

Lemma logn_gcdn :
  forall m n p, 0 < m -> 0 < n
  -> logn p (gcdn m n) = minn (logn p m) (logn p n).
Proof.
  apply (strong_induction (fun m => forall n p : nat, 0 < m -> 0 < n -> logn p (gcdn m n) = minn (logn p m) (logn p n))) ; first by [].
  move=> m IHm n p m_gt_0 n_gt_0.
  destruct (prime p)eqn:p_prime ; last unfold logn ; last by rewrite p_prime.
  assert (0 < gcdn m n) as gcd_m_n_gt_0 by by rewrite gcdn_gt0 m_gt_0.
  pose proof (minn_or (logn p m) (logn p n)) as H.
  move/orP in H ; destruct H ; move/eqP in H ; rewrite H.
  rewrite lognE p_prime gcd_m_n_gt_0 /=.
  destruct (p %| gcdn m n)eqn:p_dvd_gcd_m_n.
  apply Logic.eq_sym.
  rewrite lognE p_prime m_gt_0 /=.
  rewrite dvdn_gcd in p_dvd_gcd_m_n.
  move/andP in p_dvd_gcd_m_n.
  destruct p_dvd_gcd_m_n as [p_dvd_m p_dvd_n].
  rewrite p_dvd_m.
  congr S.
  rewrite -gcdn_div // ; last by apply prime_gt0.
  rewrite IHm ; last rewrite ltn_divRL // mul0n ; last rewrite ltn_divRL // mul0n ;
    last apply ltn_Pdiv ; last by [] ; last by apply prime_gt1.
  by rewrite ? logn_div // -subn_minl H.
  apply/eqP.
  rewrite eq_sym -leqn0 leqNgt.
  apply/negP.
  move=> p_dvd_m.
  apply negbT in p_dvd_gcd_m_n.
  rewrite dvdn_gcd negb_and in p_dvd_gcd_m_n.
  move/orP in p_dvd_gcd_m_n.
  pose proof p_dvd_m as logn_p_m_gt_0.
  rewrite logn_gt0 mem_primes in p_dvd_m.
  move/and3P in p_dvd_m.
  destruct p_dvd_m as [_ _ p_div_m].
  destruct p_dvd_gcd_m_n as [p_dvd|p_dvd] ; move/negP in p_dvd ; apply p_dvd ; first by [].
  assert (0 < logn p n) as p_dvd_n.
    apply ltn_leq_trans with (logn p m) ; first by [].
    by rewrite -H geq_minr.
  rewrite logn_gt0 mem_primes in p_dvd_n.
  move/and3P in p_dvd_n.
  by destruct p_dvd_n.
  rewrite lognE p_prime gcd_m_n_gt_0 /=.
  destruct (p %| gcdn m n)eqn:p_dvd_gcd_m_n.
  apply Logic.eq_sym.
  rewrite lognE p_prime n_gt_0 /=.
  rewrite dvdn_gcd in p_dvd_gcd_m_n.
  move/andP in p_dvd_gcd_m_n.
  destruct p_dvd_gcd_m_n as [p_dvd_m p_dvd_n].
  rewrite p_dvd_n.
  congr S.
  rewrite -gcdn_div // ; last by apply prime_gt0.
  rewrite IHm ; last rewrite ltn_divRL // mul0n ; last rewrite ltn_divRL // mul0n ;
    last apply ltn_Pdiv ; last by [] ; last by apply prime_gt1.
  by rewrite ? logn_div // -subn_minl H.
  apply/eqP.
  rewrite eq_sym -leqn0 leqNgt.
  apply/negP.
  move=> p_dvd_n.
  apply negbT in p_dvd_gcd_m_n.
  rewrite dvdn_gcd negb_and in p_dvd_gcd_m_n.
  move/orP in p_dvd_gcd_m_n.
  pose proof p_dvd_n as logn_p_m_gt_0.
  rewrite logn_gt0 mem_primes in p_dvd_n.
  move/and3P in p_dvd_n.
  destruct p_dvd_n as [_ _ p_div_n].
  destruct p_dvd_gcd_m_n as [p_dvd|p_dvd] ; move/negP in p_dvd ; apply p_dvd ; last by [].
  assert (0 < logn p m) as p_dvd_m.
    apply ltn_leq_trans with (logn p n) ; first by [].
    by rewrite -H geq_minl.
  rewrite logn_gt0 mem_primes in p_dvd_m.
  move/and3P in p_dvd_m.
  by destruct p_dvd_m.
Qed.


Section divisors_coprime.

Local Lemma divisors_coprime_aux_aux :
  forall p n, prime p -> 0 < n
  -> logn p n = 0
  -> ~~ (p %| n).
Proof.
  move=> p n p_prime n_gt_0 logn_p_n_eq_0.
  apply/negP.
  move=> p_dvd_n.
  rewrite lognE in logn_p_n_eq_0.
  by rewrite p_prime p_dvd_n n_gt_0 /= in logn_p_n_eq_0.
Qed.

Local Lemma divisors_coprime_aux :
  forall m n, 0 < m -> 0 < n
  -> coprime m n
  -> forall d11 d21 d12 d22,
     d11 %| m -> d21 %| n -> d12 %| m -> d22 %| n
  -> d11 * d21 == d12 * d22 = (d11 == d12) && (d21 == d22).
Proof.
  move=> m n m_gt_0 n_gt_0 m_coprime_n
         d11       d21       d12       d22
         d11_dvd_m d21_dvd_n d12_dvd_m d22_dvd_n.
  assert (d11 * d21 == d12 * d22 == (d11 == d12) && (d21 == d22)) as H ; last by move/eqP in H.
  apply/equiv_eqP.
  apply/idP.
  apply/idP.
  split.
  pose proof (dvdn_gt0 m_gt_0 d11_dvd_m) as d11_gt_0.
  pose proof (dvdn_gt0 n_gt_0 d21_dvd_n) as d21_gt_0.
  pose proof (dvdn_gt0 m_gt_0 d12_dvd_m) as d12_gt_0.
  pose proof (dvdn_gt0 n_gt_0 d22_dvd_n) as d22_gt_0.
  move=> d11_d21_eq_d12_d22.
  assert (coprime d11 d21) as d11_coprime_d21 by
    by [apply coprime_dvdl with m ; first by [] ; by apply coprime_dvdr with n].
  assert (coprime d12 d22) as d12_coprime_d22 by
    by [apply coprime_dvdl with m ; first by [] ; by apply coprime_dvdr with n].
  assert (coprime d11 d22) as d11_coprime_d22 by
    by [apply coprime_dvdl with m ; first by [] ; by apply coprime_dvdr with n].
  assert (coprime d12 d21) as d12_coprime_d21 by
    by [apply coprime_dvdl with m ; first by [] ; by apply coprime_dvdr with n].
  apply/andP ; split ; apply/eqP.
  apply logn_eq_prime ; first by [] ; first by [].
  move=> p p_prime.
  assert (logn p (d11 * d21) = logn p (d12 * d22)) as H by
    by [move/eqP in d11_d21_eq_d12_d22 ; rewrite d11_d21_eq_d12_d22].
  rewrite ?lognM // in H.
  pose proof (coprime_logn_or d11 d21 d11_gt_0 d21_gt_0 d11_coprime_d21 p) as H1.
  move/orP in H1.
  pose proof (coprime_logn_or d12 d22 d12_gt_0 d22_gt_0 d12_coprime_d22 p) as H2.
  move/orP in H2.
  pose proof (coprime_logn_or d11 d22 d11_gt_0 d22_gt_0 d11_coprime_d22 p) as H3.
  move/orP in H3.
  pose proof (coprime_logn_or d12 d21 d12_gt_0 d21_gt_0 d12_coprime_d21 p) as H4.
  move/orP in H4.
  destruct   H1 as [H1|H1] ; move/eqP in H1 ; destruct H2 as [H2|H2] ; move/eqP in H2 ;
    destruct H3 as [H3|H3] ; move/eqP in H3 ; destruct H4 as [H4|H4] ; move/eqP in H4 ;
    rewrite ?H1 ?H2 ?H3 ?H4 ?addn0 ?add0n // in H ; rewrite ?H1 ?H2 ?H3 ?H4 //.
  apply logn_eq_prime ; first by [] ; first by [].
  move=> p p_prime.
  assert (logn p (d11 * d21) = logn p (d12 * d22)) as H by
    by [move/eqP in d11_d21_eq_d12_d22 ; rewrite d11_d21_eq_d12_d22].
  rewrite ?lognM // in H.
  pose proof (coprime_logn_or d11 d21 d11_gt_0 d21_gt_0 d11_coprime_d21 p) as H1.
  move/orP in H1.
  pose proof (coprime_logn_or d12 d22 d12_gt_0 d22_gt_0 d12_coprime_d22 p) as H2.
  move/orP in H2.
  pose proof (coprime_logn_or d11 d22 d11_gt_0 d22_gt_0 d11_coprime_d22 p) as H3.
  move/orP in H3.
  pose proof (coprime_logn_or d12 d21 d12_gt_0 d21_gt_0 d12_coprime_d21 p) as H4.
  move/orP in H4.
  destruct   H1 as [H1|H1] ; move/eqP in H1 ; destruct H2 as [H2|H2] ; move/eqP in H2 ;
    destruct H3 as [H3|H3] ; move/eqP in H3 ; destruct H4 as [H4|H4] ; move/eqP in H4 ;
    rewrite ?H1 ?H2 ?H3 ?H4 ?addn0 ?add0n // in H ; rewrite ?H1 ?H2 ?H3 ?H4 //.
  move=> H.
  move/andP in H.
  destruct H as [d11_eq_d12 d21_eq_d22].
  move/eqP in d11_eq_d12.
  move/eqP in d21_eq_d22.
  by rewrite d11_eq_d12 d21_eq_d22.
Qed.

Lemma divisors_coprime :
  forall m n, 0 < m -> 0 < n
  -> coprime m n
  -> perm_eq (divisors (m * n)) [seq (d1 * d2) | d1 <- divisors m, d2 <- divisors n].
Proof.
  move=> m n m_gt_0 n_gt_0 m_coprime_n.
  apply uniq_perm ; first apply divisors_uniq.
  apply/(uniqP 0).
  move=> i j i_in j_in H.
  rewrite ?nth_flatten /= in H.
  remember ([seq [seq d1 * d2 | d2 <- divisors n] | d1 <- divisors m]) as prod_divisors eqn:Heq.
  assert (shape prod_divisors = nseq (size (divisors m)) (size (divisors n))).
    rewrite Heq.
    unfold shape.
    rewrite -map_comp.
    assert ((size \o (fun d1 : nat => [seq d1 * d2 | d2 <- divisors n])) =1 (fun d => size (divisors n))) as H0.
      move=> d //= ; by rewrite size_map.
    by rewrite (eq_map H0) map_const.
  remember (reshape_index  (shape prod_divisors) i) as qi eqn:Heqqi.
  remember (reshape_offset (shape prod_divisors) i) as ri eqn:Heqri.
  remember (reshape_index  (shape prod_divisors) j) as qj eqn:Heqqj.
  remember (reshape_offset (shape prod_divisors) j) as rj eqn:Heqrj.
  rewrite ?H0 in Heqqi, Heqri, Heqqj, Heqrj.
  remember (nth 0 (divisors m) qi) as d11 eqn:Heqd11.
  remember (nth 0 (divisors n) ri) as d21 eqn:Heqd21.
  remember (nth 0 (divisors m) qj) as d12 eqn:Heqd12.
  remember (nth 0 (divisors n) rj) as d22 eqn:Heqd22.
  rewrite ?size_flatten ?H0 in i_in, j_in.
  assert (qi < size (divisors m)) as Hqi.
    rewrite -(size_nseq (size (divisors m)) (size (divisors n))) Heqqi.
    by apply reshape_indexP.
  assert (ri < size (divisors n)) as Hri.
    assert (size (divisors n) = if qi < size (divisors m) then size (divisors n) else 0) as H1 by
      by rewrite Hqi.
    rewrite H1 -nth_nseq Heqqi Heqri.
    by apply reshape_offsetP.
  assert (qj < size (divisors m)) as Hqj.
    rewrite -(size_nseq (size (divisors m)) (size (divisors n))) Heqqj.
    by apply reshape_indexP.
  assert (rj < size (divisors n)) as Hrj.
    assert (size (divisors n) = if qj < size (divisors m) then size (divisors n) else 0) as H1 by
      by rewrite Hqj.
    rewrite H1 -nth_nseq Heqqj Heqrj.
    by apply reshape_offsetP.
  rewrite -(reshape_indexK (shape prod_divisors) i) -(reshape_indexK (shape prod_divisors) j).
  rewrite ?Heq ?(nth_map 0) // in H.
  rewrite -Heqd11 -Heqd21 -Heqd12 -Heqd22 in H.
  assert (d11 %| m) as d11_dvd_m.
    rewrite mem_divisors_dvdn // Heqd11.
    by apply mem_nth.
  assert (d21 %| n) as d21_dvd_n.
    rewrite mem_divisors_dvdn // Heqd21.
    by apply mem_nth.
  assert (d12 %| m) as d12_dvd_m.
    rewrite mem_divisors_dvdn // Heqd12.
    by apply mem_nth.
  assert (d22 %| n) as d22_dvd_n.
    rewrite mem_divisors_dvdn // Heqd22.
    by apply mem_nth.
  rewrite ?H0 -Heqqi -Heqri -Heqqj -Heqrj.
  move/eqP in H.
  rewrite (divisors_coprime_aux m n) // in H.
  move/andP in H.
  destruct H as [d11_eq_d12 d21_eq_d22].
  rewrite Heqd11 Heqd12 nth_uniq // in d11_eq_d12 ; last apply divisors_uniq.
  rewrite Heqd21 Heqd22 nth_uniq // in d21_eq_d22 ; last apply divisors_uniq.
  move/eqP in d11_eq_d12.
  move/eqP in d21_eq_d22.
  by rewrite d11_eq_d12 d21_eq_d22.
  assert (0 < m * n) as m_n_gt_0.
    rewrite -(muln0 0).
    by apply ltn_mul.
  move=> d.
  rewrite -dvdn_divisors //.
  assert ((d %| m * n) == (d \in [seq d1 * d2 | d1 <- divisors m, d2 <- divisors n])) as H0 ; last by move/eqP in H0.
  apply/equiv_eqP.
  apply/idP.
  apply/idP.
  split.
  move=> d_dvd_m_n.
    assert (0 < d) as d_gt_0 by
      by apply dvdn_gt0 with (m * n).
  apply/flatten_mapP.
  exists (gcdn m d).
    rewrite -dvdn_divisors //.
    apply dvdn_gcdl.
  apply/mapP.
  exists (gcdn n d).
    rewrite -dvdn_divisors //.
    apply dvdn_gcdl.
  assert (0 < gcdn m d) as gcd_m_d_gt_0 by by rewrite gcdn_gt0 m_gt_0.
  assert (0 < gcdn n d) as gcd_n_d_gt_0 by by rewrite gcdn_gt0 n_gt_0.
  assert (d = gcdn (m * n) d) as d_eq_gcdn_m_n_d.
    apply Logic.eq_sym.
    by apply/gcdn_idPr.
  rewrite {1}d_eq_gcdn_m_n_d.
  apply logn_eq_prime ; first by rewrite -d_eq_gcdn_m_n_d.
    rewrite -(muln0 0) ; by apply ltn_mul.
  move=> p p_prime.
  rewrite ?logn_gcdn // ?lognM // ?logn_gcdn //.
  pose proof (coprime_logn_or _ _ m_gt_0 n_gt_0 m_coprime_n p) as H.
  move/orP in H.
  destruct H ; move/eqP in H ; rewrite H.
    by rewrite min0n ?add0n.
    by rewrite min0n ?addn0.
  move=> d_in.
  move/flatten_mapP in d_in.
  destruct d_in as [d1 d1_in d_in].
  move/mapP in d_in.
  destruct d_in as [d2 d2_in d_eq_d1_d2].
  rewrite d_eq_d1_d2.
  apply dvdn_mul ; by rewrite mem_divisors_dvdn.
Qed.

End divisors_coprime.

Lemma divisors_filter_prime :
  forall n, 0 < n
  -> primes n = [seq d <- divisors n | prime d].
Proof.
  move=> n n_gt_0.
  apply eq_sorted_irr with ltn.
    by move ; apply ltn_trans.
    by move ; apply ltnn.
    apply sorted_primes.
    apply sorted_filter ; first by [move ; apply ltn_trans] ; apply sorted_divisors_ltn.
  move=> p.
  by rewrite mem_primes mem_filter dvdn_divisors n_gt_0.
Qed.


