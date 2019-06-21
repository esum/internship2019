From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq prime div.
From mathcomp Require Import path fintype bigop.
Add LoadPath "~/git/git.graillo.tf/stage/2019-06/src".
Require Import seq2 arith.

(* Proof of some induction theorems :
 *
 * primes_induction : forall P,
 *   P 1
 *   -> (forall m n, m > 0 -> n > 0 -> P m -> P n -> P (m * n))
 *   -> (forall p, prime p -> P p)
 *   -> (forall d n, prime_decomp n = d -> n > 0 -> P n).
 *
 * Lemma primespow_induction : forall P,
 *   P 1
 *   -> (forall m n, m > 0 -> n > 0 -> coprime m n -> P m -> P n -> P (m * n))
 *   -> (forall p a, prime p -> 0 < a -> P (p ^ a))
 *   -> (forall n, n > 0 -> P n).
 *)


Section primes_induction.

Local Lemma sorted_min :
  forall x l default, sorted ltn l
  -> x \in l
  -> (forall y, y \in l -> x <= y)
  -> x = head default l.
Proof.
  move=> x l.
  move: x.
  elim: l => [|h [|h' t] IHl] ; move=> x default l_sorted x_in_l x_min ; first by [].
    rewrite mem_seq1 in x_in_l.
    by apply/eqnP.
  simpl in *.
  move/andP in l_sorted.
  destruct l_sorted as [h_lt_h' path_t].
  rewrite mem_head_or_behead in x_in_l.
  move/orP in x_in_l.
  destruct x_in_l as [x_eq_h|x_in_t].
    by apply/eqP.
  apply order_path_min in path_t.
  move/allP in path_t.
  rewrite mem_head_or_behead in x_in_t.
  move/orP in x_in_t.
  destruct x_in_t as [x_eq_h'|x_in_t].
    move/eqP in x_eq_h'.
    subst.
    assert (h' <= h) as h_ge_h'.
      apply x_min. rewrite mem_head_or_behead eq_refl //.
    assert (h' < h') as h'_tl_h'.
      by apply leq_ltn_trans with h.
      by rewrite ltnn in h'_tl_h'.
  assert (h' < h') as h'_tl_h'.
    apply ltn_leq_trans with x.
    by apply path_t.
    apply x_min.
    rewrite ?mem_head_or_behead.
    by rewrite orbC eq_refl //.
  by rewrite ltnn in h'_tl_h'.
  move=> ? ? ? ; apply ltn_trans.
Qed.

Local Lemma primes_induction_aux_aux_aux2 :
  forall m n, coprime m n
  -> 0 < m -> 0 < n
  -> perm_eq (primes (m * n)) ((primes m) ++ (primes n)).
Proof.
  move=> m n m_coprime_n m_gt_0 n_gt_0.
  assert (uniq (primes m ++ primes n)) as uniq_primes_m_cat_primes_n.
    rewrite cat_uniq.
    apply/and3P.
    split ; [by apply primes_uniq | | by apply primes_uniq].
    apply/negP ; move=> H.
    move/hasP in H.
    destruct H as [p p_in_primes_n p_in_primes_m].
    rewrite /= ?mem_primes in p_in_primes_m p_in_primes_n.
    move/and3P in p_in_primes_m.
    move/and3P in p_in_primes_n.
    destruct p_in_primes_m as [p_prime _ p_dvd_m].
    destruct p_in_primes_n as [_       _ p_dvd_n].
    assert (coprime p n) as p_coprime_n by
      by apply coprime_dvdl with m.
    rewrite prime_coprime // in p_coprime_n.
    by rewrite p_dvd_n in p_coprime_n.
    apply uniq_perm.
      apply primes_uniq.
      apply uniq_primes_m_cat_primes_n.
    move=> p.
    by rewrite mem_cat primes_mul.
Qed.

Local Lemma primes_induction_aux_aux_aux :
  forall m n, coprime m n
  -> 0 < m -> 0 < n
  -> primes (m * n) = merge leq (primes m) (primes n).
Proof.
  move=> m n m_coprime_n m_gt_0 n_gt_0.
  apply eq_sorted with leq.
    by move ; apply leq_trans.
    by move ; apply anti_leq.
    pose proof (sorted_primes (m * n)) as sorted_primes_m_n.
    rewrite ltn_sorted_uniq_leq in sorted_primes_m_n.
    move/andP in sorted_primes_m_n.
    by destruct sorted_primes_m_n.
    apply merge_sorted.
      by move ; apply leq_total.
      pose proof (sorted_primes m) as sorted_primes_m.
      rewrite ltn_sorted_uniq_leq in sorted_primes_m.
      move/andP in sorted_primes_m.
      by destruct sorted_primes_m.
      pose proof (sorted_primes n) as sorted_primes_n.
      rewrite ltn_sorted_uniq_leq in sorted_primes_n.
      move/andP in sorted_primes_n.
      by destruct sorted_primes_n.
  apply perm_trans with (primes m ++ primes n) ;
    first by apply primes_induction_aux_aux_aux2.
  rewrite perm_sym.
  apply/permPl.
  apply perm_merge.
Qed.

Local Lemma primes_induction_aux_aux :
  forall p m a, prime p
  -> 0 < m
  -> 0 < a
  -> (p < pdiv m) || (m == 1)
  -> primes (p ^ a * m) = p :: primes m.
Proof.
  move=> p m a p_prime m_gt_1 a_gt_1 p_lt_pdiv_m.
  unfold primes.
  destruct (m == 1)eqn:m_eq_1.
    move/eqP in m_eq_1.
    rewrite m_eq_1 muln1 /= -[unzip1 (prime_decomp (p ^ a))]/(primes (p ^ a)).
    rewrite primes_exp //.
    by apply primes_prime.
  rewrite orbF in p_lt_pdiv_m.
  assert (coprime p m) as p_coprime_m.
    rewrite prime_coprime //.
    apply/negP.
    move=> p_div_m.
    apply pdiv_min_dvd in p_div_m as p_le_pdiv_m.
    assert (pdiv m < pdiv m) as pdiv_m_lt_pdiv_m.
      by apply leq_ltn_trans with p.
      by rewrite (ltnn (pdiv m)) in pdiv_m_lt_pdiv_m.
    by apply prime_gt1.
  assert (pdiv (p^a * m) = p).
    unfold pdiv.
    rewrite -(sorted_min p) //.
    apply sorted_primes.
    rewrite primes_mul //. rewrite primes_exp // primes_prime // mem_seq1.
    apply/orP ; left ; by apply/eqnP.
    rewrite expn_gt0 prime_gt0 //.
    move=> q q_in_primes.
    rewrite primes_mul // in q_in_primes.
    move/orP in q_in_primes.
    case q_in_primes ; move=> H.
    rewrite primes_exp // primes_prime // mem_seq1 in H.
    move/eqnP in H.
    by rewrite H leqnn.
    apply leq_trans with (pdiv m).
    rewrite leq_eqVlt p_lt_pdiv_m.
    by destruct (p == pdiv m).
    apply: pdiv_min_dvd.
    apply: prime_gt1.
    rewrite mem_primes in H.
    move/and3P in H.
    by destruct H.
    rewrite mem_primes in H.
    move/and3P in H.
    by destruct H.
    rewrite expn_gt0 prime_gt0 //.
    rewrite -[unzip1 (prime_decomp (p ^ a * m))]/(primes (p ^ a * m)).
    rewrite primes_induction_aux_aux_aux //.
    rewrite primes_exp //.
    rewrite primes_prime //.
    destruct (primes m) as [|q d]eqn:primes_m.
      unfold primes in primes_m.
      by rewrite primes_m.
    unfold pdiv in p_lt_pdiv_m.
    simpl.
    rewrite primes_m in p_lt_pdiv_m.
    simpl in p_lt_pdiv_m.
    rewrite leqNgt p_lt_pdiv_m /=.
    congr cons.
    unfold primes in primes_m.
    by rewrite primes_m.
  rewrite coprime_expl //.
  rewrite expn_gt0 prime_gt0 //.
Qed.


Local Lemma primes_induction_aux :
  forall d, all prime (unzip1 d)
  -> all (ltn 0) (unzip2 d)
  -> sorted ltn (unzip1 d)
  -> prime_decomp (\prod_(f <- d) f.1 ^ f.2) = d.
Proof.
  elim=> [|[p a] d IHd]; move=> primes_d_prime exp_gt_0 primes_sorted ;
    first by rewrite bigop.BigOp.bigopE.
  simpl in primes_d_prime, exp_gt_0.
  move/andP in primes_d_prime.
  move/andP in exp_gt_0.
  destruct primes_d_prime as [p_prime primes_d_prime].
  destruct exp_gt_0 as [a_gt_0 exp_gt_0].
  assert (sorted ltn (unzip1 d)) as primes_d_sorted.
    simpl in primes_sorted.
    by apply path_sorted with p.
  assert (0 < \prod_(f <- d) f.1 ^ f.2) as prod_d_gt_0.
    apply ltn_0_prod_f.
    apply/allP.
    move=> n n_in_factors.
    move/mapP in n_in_factors.
    destruct n_in_factors as [[q b] q_b_in_d n_eq_q_exp_b].
    simpl in n_eq_q_exp_b.
    rewrite n_eq_q_exp_b.
    unfold ltn ; simpl.
    rewrite expn_gt0 prime_gt0 //.
    rewrite -IHd // in q_b_in_d.
    apply mem_prime_decomp in q_b_in_d.
    by destruct q_b_in_d.
  rewrite bigop.BigOp.bigopE /= -bigop.BigOp.bigopE -{2}IHd ?prime_decompE //.
  rewrite primes_induction_aux_aux //=.
  rewrite lognM //.
  unfold pfactor.
  rewrite lognX lognn p_prime muln1.
  congr cons.
    congr pair.
    rewrite logn_coprime // ; first ring.
    rewrite coprime_has_primes //.
    unfold primes at 2.
    rewrite IHd //.
    rewrite primes_prime //=.
    rewrite has_sym /= orbF.
    simpl in primes_sorted.
    apply order_path_min in primes_sorted.
    move/allP in primes_sorted.
    apply/negP.
    move=> p_in_d.
    assert (p < p) as p_lt_p ; first by apply primes_sorted.
    pose proof (ltnn p) as n_p_lt_p.
    by rewrite p_lt_p in n_p_lt_p.
    move=> ? ? ? ; apply ltn_trans.
    by apply: prime_gt0.
  apply eq_in_map.
    move=> q q_primes_d.
    assert (prime q) as q_prime.
      rewrite (mem_primes q _) in q_primes_d.
      move/and3P in q_primes_d ; by destruct q_primes_d as [q_prime _ _].
    unfold pfactor in IHd.
    unfold primes in q_primes_d.
    rewrite IHd // in q_primes_d.
    congr pair.
    rewrite logn_Gauss // coprime_pexpr //.
    rewrite prime_coprime // dvdn_prime2 //.
      simpl in primes_sorted.
      assert (p < q) as p_lt_q.
        apply order_path_min in primes_sorted.
        move/allP in primes_sorted.
        by apply primes_sorted.
        move=> ? ? ? ; apply ltn_trans.
      unfold negb.
      by rewrite eqn_leq leqNgt p_lt_q /=.
    rewrite expn_gt0 prime_gt0 //.
    unfold pdiv, primes.
    rewrite IHd //.
    destruct d as [|(q, b) d] ; first by rewrite bigop.BigOp.bigopE /= orbT.
    simpl in primes_sorted.
    simpl.
    move/andP in primes_sorted.
    destruct primes_sorted as [p_lt_q _] ; by rewrite p_lt_q.
Qed.

Lemma primes_induction_decomp : forall P,
  P 1
  -> (forall m n, m > 0 -> n > 0 -> P m -> P n -> P (m * n))
  -> (forall p, prime p -> P p)
  -> (forall d n, prime_decomp n = d -> n > 0 -> P n).
Proof.
  move=> P P_1 IHprod Hprime.
  elim=> [|[p a] d IHdecomp] ; move=> n n_decomp n_gt_0.
    apply prime_decomp_nil in n_decomp.
    assert (1 == n).
    rewrite eqn_leq n_gt_0 n_decomp //.
    move/eqnP in H.
    by rewrite -H.
  rewrite (prod_prime_decomp n_gt_0) n_decomp bigop.BigOp.bigopE /=.
  assert (prime p) as p_prime.
    assert ((p, a) \in prime_decomp n) as p_decomp_n. rewrite n_decomp ; apply: mem_head.
    by pose proof (mem_prime_decomp p_decomp_n) as [p_prime _ _].
  assert (0 < reducebig 1 d (fun f : nat * nat => BigBody f muln true (f.1 ^ f.2))) as prod_d_gt_0.
    rewrite -bigop.BigOp.bigopE.
    apply ltn_0_prod_f.
    apply/allP.
    move=> m m_in.
    move/mapP in m_in.
    destruct m_in as [[q b] q_b_in_d H].
    rewrite H /= expn_gt0 prime_gt0 //.
    apply (mem_cons _ (p, a)) in q_b_in_d.
    rewrite -n_decomp in q_b_in_d.
    apply mem_prime_decomp in q_b_in_d.
    by destruct q_b_in_d.
  apply IHprod.
    by rewrite expn_gt0 prime_gt0.
    by [].
    clear n_decomp.
    elim: a => [|a IHa] ; first by rewrite expn0.
      rewrite expnS. apply: IHprod ; last by [].
      by apply: prime_gt0.
      by rewrite expn_gt0 prime_gt0.
      by apply: Hprime.
      rewrite <- bigop.BigOp.bigopE.
    apply: IHdecomp ; last by rewrite bigop.BigOp.bigopE.
    pose proof n_decomp as n_primes.
    rewrite prime_decompE in n_primes.
    unfold primes in n_primes.
    rewrite n_decomp /= in n_primes.
    apply primes_induction_aux.
      apply/allP.
      move=> q q_in_d.
      apply (mem_cons q p) in q_in_d.
      rewrite [p::unzip1 d]/(unzip1 ((p, a)::d)) -n_decomp mem_primes in q_in_d.
      move/and3P in q_in_d.
      by destruct q_in_d.
      apply/allP.
      move=> b b_in_d.
      apply (mem_cons b a) in b_in_d.
      rewrite [a::unzip2 d]/(unzip2 ((p, a)::d)) -n_decomp in b_in_d.
      by apply mem_exp_prime_decomp with n.
   apply path_sorted with p.
   pose proof (sorted_primes n) as primes_sorted.
   unfold primes in primes_sorted.
   by rewrite n_decomp in primes_sorted.
Qed.

Lemma primes_induction : forall P,
  P 1
  -> (forall m n, m > 0 -> n > 0 -> P m -> P n -> P (m * n))
  -> (forall p, prime p -> P p)
  -> (forall n, n > 0 -> P n).
Proof.
  move=> P P_1 IHprod IHprimepow n n_gt_0.
  by apply primes_induction_decomp with (prime_decomp n).
Qed.

End primes_induction.


Section primespow_induction.

Local Lemma coprime_prodr {T : Type} : forall (f : T -> nat) (l : seq T) p, coprime p (\prod_ (x <- l) f x) = all (coprime p) [seq f x | x <- l].
Proof.
  move=> f.
  elim=> [|h t IHl] ; move=> p.
    rewrite bigop.BigOp.bigopE /= coprimen1 //.
  rewrite bigop.BigOp.bigopE.
  simpl.
  rewrite coprime_mulr.
  congr andb.
  by rewrite -bigop.BigOp.bigopE IHl.
Qed.

Lemma primespow_induction_decomp : forall P,
  P 1
  -> (forall m n, m > 0 -> n > 0 -> coprime m n -> P m -> P n -> P (m * n))
  -> (forall p a, prime p -> 0 < a -> P (p ^ a))
  -> (forall d n, prime_decomp n = d -> n > 0 -> P n).
Proof.
  move=> P P_1 IHprod Hprime.
  elim=> [|[p a] d IHdecomp] ; move=> n n_decomp n_gt_0.
    apply prime_decomp_nil in n_decomp.
    assert (1 == n).
    rewrite eqn_leq n_gt_0 n_decomp //.
    move/eqnP in H.
    by rewrite -H.
    rewrite (prod_prime_decomp n_gt_0) n_decomp bigop.BigOp.bigopE /=.
    assert (prime p) as p_prime.
      assert ((p, a) \in prime_decomp n) as p_decomp_n. rewrite n_decomp ; apply: mem_head.
      by pose proof (mem_prime_decomp p_decomp_n) as [p_prime _ _].
    assert (0 < reducebig 1 d (fun f : nat * nat => BigBody f muln true (f.1 ^ f.2))) as prod_d_gt_0.
      rewrite -bigop.BigOp.bigopE.
      apply ltn_0_prod_f.
      apply/allP.
      move=> m m_in.
      move/mapP in m_in.
      destruct m_in as [[q b] q_b_in_d H].
      rewrite H /= expn_gt0 prime_gt0 //.
      apply (mem_cons _ (p, a)) in q_b_in_d.
      rewrite -n_decomp in q_b_in_d.
      apply mem_prime_decomp in q_b_in_d.
      by destruct q_b_in_d.
    apply IHprod.
      by rewrite expn_gt0 prime_gt0.
      by [].
      rewrite coprime_expl // -bigop.BigOp.bigopE coprime_prodr.
      assert ({in d, (preim (fun x : nat * nat => x.1 ^ x.2) (coprime p)) =1 (preim fst (coprime p))}) as H.
        move=> x x_in_d.
        simpl.
        rewrite coprime_pexpr //.
        apply mem_exp_prime_decomp with n.
        rewrite n_decomp /= mem_head_or_behead map_f // orbT //.
      rewrite all_map (eq_in_all H) -all_map all_spred.
      apply/allP.
      move=> b Hb.
        move/nthP in Hb.
        destruct (Hb false) as [i Hi H0].
        rewrite size_map in Hi.
        rewrite (nth_map 0) // in H0.
        rewrite eq_sym -H0.
        apply/eqP.
        remember (nth 0 [seq i.1 | i <- d] i) as q.
        rewrite -Heqq.
        assert (prime q) as q_prime.
          rewrite -(ltn_add2l 1) addnE /= -[(size [seq i.1 | i <- d]).+1]/(size [seq i.1 | i <- (p, a)::d]) -n_decomp in Hi.
          apply (mem_nth 0) in Hi.
          rewrite mem_primes in Hi.
          move/and3P in Hi.
          destruct Hi as [q_prime _ q_dvd_n].
          by rewrite n_decomp /= -Heqq in q_prime.
        pose proof (prime_coprime_logn p q p_prime (prime_gt0 q_prime)) as H1.
        move/eqP in H1.
        rewrite H1.
        rewrite logn_prime //.
        apply/eqP/eqP.
        pose proof (prime_decomp_uniq n) as uniq_n_decomp.
        rewrite n_decomp cons_uniq in uniq_n_decomp.
        move/andP in uniq_n_decomp.
        destruct uniq_n_decomp as [n_p_a_in_d _].
        assert (~~(p == q)) ; last by destruct (p == q).
        apply/negP.
        move=> p_eq_q.
        move/negP in n_p_a_in_d.
        apply: n_p_a_in_d.
        move/eqP in p_eq_q.
        rewrite -p_eq_q in Heqq.
        pose proof (prime_decompE n) as n_decomp_logn.
        unfold primes in n_decomp_logn.
        rewrite n_decomp //= in n_decomp_logn.
        inversion n_decomp_logn as [[Ha Hd]].
        rewrite -Hd p_eq_q.
        rewrite p_eq_q in Heqq.
        apply/(nthP (0, 0)).
        exists i ; first rewrite size_map // in Hi.
        rewrite Hd (nth_map 0) // -Heqq //.
      apply: Hprime ; first by [].
      apply mem_exp_prime_decomp with n.
      by rewrite n_decomp mem_head_or_behead eq_refl.
    apply IHdecomp ; last by [].
    rewrite -bigop.BigOp.bigopE.
    apply primes_induction_aux.
      apply/allP.
      move=> q q_in_d.
      apply (mem_cons q p) in q_in_d.
      rewrite [p::unzip1 d]/(unzip1 ((p, a)::d)) -n_decomp mem_primes in q_in_d.
      move/and3P in q_in_d.
      by destruct q_in_d.
      apply/allP.
      move=> b b_in_d.
      apply (mem_cons b a) in b_in_d.
      rewrite [a::unzip2 d]/(unzip2 ((p, a)::d)) -n_decomp in b_in_d.
      by apply mem_exp_prime_decomp with n.
      apply path_sorted with p.
   pose proof (sorted_primes n) as primes_sorted.
   unfold primes in primes_sorted.
   by rewrite n_decomp in primes_sorted.
Qed.

Lemma primespow_induction : forall P,
  P 1
  -> (forall m n, m > 0 -> n > 0 -> coprime m n -> P m -> P n -> P (m * n))
  -> (forall p a, prime p -> 0 < a -> P (p ^ a))
  -> (forall n, n > 0 -> P n).
Proof.
  move=> P P_1 IHprod IHprimepow n n_gt_0.
  by apply primespow_induction_decomp with (prime_decomp n).
Qed.

End primespow_induction.
