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


Section primepow_divisors.

Local Lemma primepow_divisors_aux : forall p a b, [seq (NatTrec.mul p \o expn p) i | i <- iota b a] = [seq p ^ i | i <- iota b.+1 a].
Proof.
  move=> p ; elim=> [|a IHa] //.
  move=> b /=.
  rewrite IHa.
  congr cons.
  by rewrite NatTrec.mulE expnS.
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
      rewrite ?NatTrec.mulE expn1 expn0 muln1 (prime_gt0 p_prime) [p ^ 2]/(p * p) -mulnE ;
        do 3 congr cons.
      rewrite -map_comp.
      by rewrite primepow_divisors_aux.
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


