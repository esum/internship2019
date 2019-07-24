From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq prime div.
From mathcomp Require Import path fintype bigop.
From mathcomp Require Import ssralg ssrint.
Add LoadPath "~/git/git.graillo.tf/stage/2019-06/src".
Require Import seq2 arith primes_induction.


Import intZmod.
Import intRing.

Local Open Scope ring_scope.
Local Open Scope int_scope.
Bind Scope ring_scope with int.

Import GRing.

Notation "\sum_ ( d %| n ) F" := (\sum_(d <- divisors n) F)
  (at level 41, F at level 41, d at level 50).


Lemma sumz_div_pred :
  forall (f : nat -> int) n, 0 < n
  -> \sum_(d %| n) f d = \sum_(1 <= k < n.+1 | k %| n) f k.
Proof.
  move=> f n n_gt_0.
  apply/eqP.
  rewrite eq_sym -big_filter.
  apply/eqP.
  apply perm_big.
  apply uniq_perm.
    apply filter_uniq ; apply iota_uniq.
    apply divisors_uniq.
  move=> d.
  rewrite mem_filter -dvdn_divisors // andb_idr //.
  move=> d_dvd_n.
  rewrite mem_iota subnS add1n /=.
  apply/andP ; split.
    by apply dvdn_gt0 with n.
    rewrite -[d < n.+1]/(d <= n).
    by apply dvdn_leq.
Qed.

Lemma sumz_kronecker {T : eqType} : forall f (y : T) (s : seq T),
  \sum_(x <- s) (f x) * (Posz (eq_op y x))
  = \sum_(x <- s | eq_op y x) f x.
Proof.
  move=> f y ; elim=> [|h s IHs] ;
    rewrite BigOp.bigopE //=.
  rewrite -BigOp.bigopE IHs.
  case (y == h).
  by rewrite mulr1.
  by rewrite mulr0 add0r.
Qed.

Lemma sumz_div_inv :
  forall (f : nat -> int) n, 0 < n
  -> \sum_(d %| n) f d = \sum_(d %| n) f (n %/ d).
Proof.
  move=> f n n_gt_0.
  rewrite -(big_map (fun d => n %/ d) predT f).
  apply perm_big.
  rewrite perm_sym.
  by apply div_divisors_perm.
Qed.

Lemma map_map2_comp {T1 T2 T3 T4 : Type} :
  forall {f : T1 -> T2 -> T3} {g : T3 -> T4}
  {s1 : seq T1} {s2 : seq T2},
  [seq g (f x y) | x <- s1, y <- s2] = [seq g z | z <- [seq f x y | x <- s1, y <- s2]].
Proof.
  move=> f g ; elim=> [|h1 s1 IHs1] // ; case=> [|h2 s2] //.
  rewrite /= ?map_const.
  assert (forall T : Type, flatten (nseq (size s1) [::]) = ([::] : seq T)) as step by
    by move: (size s1) ; elim=> [|k IHk].
  by rewrite ?step.
  rewrite /=.
  congr cons.
  rewrite map_cat.
  congr cat ; first by rewrite map_comp.
  by rewrite (IHs1 (h2::s2)).
Qed.

Lemma sumz_div_mul :
  forall (f : nat -> int) m n, 0 < m -> 0 < n
  -> coprime m n
  -> \sum_(d %| m * n) f d = \sum_(d1 %| m) (\sum_(d2 %| n) f (d1 * d2)%N).
Proof.
  move=> f m n m_gt_0 n_gt_0 m_coprime_n.
  apply/eqP ; rewrite eq_sym.
  assert (
    \sum_(d1 %| m) \sum_(d2 %| n) f (d1 * d2)%N
    = \sum_(d <- [seq (d1, d2) | d1 <- divisors m, d2 <- divisors n]) f (d.1 * d.2)%N
    ) as step by by rewrite big_allpairs.
  rewrite step.
  rewrite -(big_map (fun d => d.1 * d.2)%N predT).
  apply/eqP.
  apply perm_big.
  rewrite perm_sym.
  rewrite -map_map2_comp /=.
  by apply divisors_coprime.
Qed.

Lemma eq_in_big :
   forall {R : Type} {idx : R} {op} {I : eqType}
     {r : seq I} {P1} (P2 : pred I) {F1} (F2 : I -> R),
   {in r, P1 =1 P2} ->
   (forall i : I, P1 i -> F1 i = F2 i) ->
   \big[op/idx]_(i <- r | P1 i) F1 i = \big[op/idx]_(i <- r | P2 i) F2 i.
Proof.
  move=> R idx op I ; elim=> [|h r IHr] P1 P2 F1 F2 P1_eq_P2 F1_eq_F2 ;
    first by [rewrite big_nil ; apply Logic.eq_sym ; rewrite big_nil].
  rewrite ?big_cons -P1_eq_P2 ; last by apply mem_head.
  destruct (P1 h)eqn:P1_h.
  rewrite F1_eq_F2 // (IHr _ P2 _ F2) //.
  move=> i i_in_r.
  rewrite P1_eq_P2 // ; by apply mem_cons.
  apply IHr ; last by [].
  move=> i i_in_r.
  rewrite P1_eq_P2 // ; by apply mem_cons.
Qed.

Lemma sumz_div_div :
  forall (f : nat -> nat -> int) n, 0 < n ->
  \sum_(d1 %| n) \sum_(d2 %| d1) f (n %/ d1) d2
  = \sum_(d2 %| n) \sum_(d %| n %/ d2) f d d2.
Proof.
  move=> f n n_gt_0.
  rewrite (eq_big_seq (fun d1 => \sum_(1 <= d2 < n.+1 | (d2 %| d1) && (d2 <= d1)) f (n %/ d1) d2)).
  rewrite sumz_div_pred //.
  rewrite (exchange_big_dep_nat (fun d => d %| n)) /=.
  rewrite -sumz_div_pred //.
  apply (eq_big_seq (fun d2=> \sum_ (d %| n %/ d2) f d d2)).
  move=> d2 d2_dvd_n.
    rewrite -dvdn_divisors // in d2_dvd_n.
    assert (d2 > 0) as d2_gt_0 by by apply dvdn_gt0 with n.
    assert (d2 <= n) as d2_le_n by by apply dvdn_leq.
    rewrite sumz_div_inv  ; last by rewrite divn_gt0.
    rewrite sumz_div_pred ; last by rewrite divn_gt0.
    apply/eqP.
    rewrite eq_sym (big_nat_widen _ _ n.+1).
    rewrite (eq_in_big (fun d => d %| n %/ d2) (fun d => f ((n %/ d2) %/ d) d2)) //.
    remember (\sum_ (i <- index_iota 1 n.+1 | i %| n %/ d2) f ((n %/ d2) %/ i) d2) as x eqn:Heqx.
    rewrite -Heqx (eq_in_big (fun d => (d %| n) && (d2 %| d)) (fun d => f (n %/ d) d2)) //= ?Heqx; clear x Heqx.
    rewrite -big_filter eq_sym -big_filter.
    assert (
      \sum_ (i <- [seq i <- index_iota 1 n.+1 | i %| n %/ d2]) f ((n %/ d2) %/ i) d2
      = \sum_(d <- [seq (d2 * d)%N | d <- index_iota 1 n.+1 & d %| n %/ d2]) f (n %/ d) d2
      ) as step.
      rewrite big_map.
      apply eq_big ; first by [].
      move=> d _.
      by rewrite -divnMA.
    rewrite step.
    apply/eqP.
    congr bigop.
    apply eq_sorted with leq.
      move ; apply leq_trans.
      move ; by apply anti_leq.
    apply sorted_filter ; first by [move=> ? ? ? ; apply leq_trans].
    apply iota_sorted.
    destruct ([seq (d2 * d)%N | d <- index_iota 1 n.+1 & d %| n %/ d2]) as [|h t]eqn:Heql ; first by [].
    apply/(pathP 0%N).
    move=> i Hi.
    rewrite -[i < size t]/(i.+1 < size (h::t)) -Heql size_map in Hi.
    rewrite -[nth 0%N t i]/(nth 0%N (h::t) i.+1) -Heql (nth_map 0%N) ;
      last by apply (ltn_trans (ltnSn i)).
    rewrite (nth_map 0%N) // leq_pmul2l //
      -[nth 0%N [seq d <- index_iota 1 n.+1 | d %| n %/ d2] i]/(nth 0%N (0%N::[seq d <- index_iota 1%N n.+1 | d %| n %/ d2]) i.+1).
    move: i.+1 Hi.
    clear i.
    apply/pathP.
    rewrite path_min_sorted.
      apply sorted_filter ; first by [move ; apply leq_trans].
      apply iota_sorted.
    by move.
    apply uniq_perm.
      apply filter_uniq ; apply iota_uniq.
      rewrite map_inj_in_uniq ; first by [apply filter_uniq ; apply iota_uniq].
      move=> d d' d_in d'_in H.
      move/eqP in H.
      rewrite ?(mulnC d2) (eqn_pmul2r d2_gt_0) // in H.
      by apply/eqP.
    move=> d.
    apply/eqP/equiv_eqP ; first apply/idP ; first apply/idP.
    split ; move=> d_in.
      rewrite mem_filter in d_in.
      move/andP in d_in.
      destruct d_in as [H d_in].
      move/andP in H.
      destruct H as [d_dvd_n d2_dvd_d].
      pose proof d2_dvd_d as d_mul_d2.
      move/dvdnP in d_mul_d2.
      destruct d_mul_d2 as [k d_eq_k_d2].
      rewrite d_eq_k_d2 mulnC mem_map.
      rewrite mem_filter.
      rewrite mem_iota.
      apply/and3P.
      split.
        by rewrite -(dvdn_pmul2r d2_gt_0) divn_mulAC //
          -(addn0 (n * d2)%N) divnMDl //
          div0n addn0 -d_eq_k_d2.
        rewrite -(orbF (0 < k)).
        apply ltn_eqF in d2_gt_0.
        rewrite eq_sym in d2_gt_0.
        rewrite -d2_gt_0 orbC -leq_mul2r mul1n -d_eq_k_d2.
        apply dvdn_leq ; last by [].
        by apply dvdn_gt0 with n.
      rewrite subn1 add1n /= ltnS.
      apply dvdn_leq ; first by [].
      apply dvdn_trans with d ; last by [].
      apply/dvdnP.
      by exists d2 ; rewrite mulnC.
      move=> a b H.
      rewrite ?(mulnC d2) in H.
      move/eqP in H.
      rewrite (eqn_pmul2r d2_gt_0) // in H.
      by apply/eqP.
      move/nthP in d_in.
      destruct (d_in 0%N) as [i Hi Hd].
      rewrite size_map in Hi.
      rewrite (nth_map 0%N) // in Hd.
      apply (mem_nth 0%N) in Hi.
      remember (nth 0%N [seq d <- index_iota 1 n.+1 | d %| n %/ d2] i) as d' eqn:Heqd'.
      rewrite -Heqd' in Hi.
      rewrite mem_filter.
      rewrite mem_filter in Hi.
      move/andP in Hi.
      destruct Hi as [d'_dvd_n_d2 d'_in].
      rewrite andbC andbA.
      apply/andP.
      split.
        rewrite andb_idl ; first by rewrite -(dvdn_pmul2l d2_gt_0) Hd mulnC divn_mulAC //
          -divnA // divnn d2_gt_0 divn1 in d'_dvd_n_d2.
        move=> d_dvd_n.
        rewrite mem_iota subn1 add1n ltnS /=.
        apply/andP.
        split.
          by apply dvdn_gt0 with n.
          by apply dvdn_leq.
        apply/dvdnP.
        by exists d' ; rewrite mulnC.
      move=> d d_in.
      rewrite mem_iota in d_in.
      move/andP in d_in.
      destruct d_in as [d_gt_0 _].
      congr andb ; rewrite andb_idr // ;
        move=> d2_dvd_d.
      by apply dvdn_leq.
      move=> d d_in.
      rewrite mem_iota in d_in.
      move/andP in d_in.
      destruct d_in as [d_gt_0 d_le_n].
      rewrite andb_idr // ;
        move=> d2_dvd_d_div_d2.
      rewrite ltnS.
      apply dvdn_leq ; last by [].
      by rewrite ltn_divRL.
      rewrite ltnS.
      apply leq_div.
  move=> d1 d2 n_ge_d1_ge_0 n_ge_d2_ge_0 d1_dvd_n d2_dvd_d1_and_d2_le_d1.
  move/andP in d2_dvd_d1_and_d2_le_d1.
  destruct d2_dvd_d1_and_d2_le_d1 as [d2_dvd_d1 _].
  by apply dvdn_trans with d1.
  move=> d d_dvd_n.
  rewrite -dvdn_divisors // in d_dvd_n.
  rewrite sumz_div_pred ; last by apply dvdn_gt0 with n.
  apply big_nat_widen.
  assert (d <= n) ; last by [].
  by apply dvdn_leq.
Qed.
