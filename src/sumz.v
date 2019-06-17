From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq ssreflect.prime div.
From mathcomp Require Import path fintype bigop.
Add LoadPath "~/git/git.graillo.tf/stage/2019-06/src".
Require Import seq2 ssrz arith primes_induction.


Definition sumz := foldr addz (Znn 0).


Notation "\sumz_ ( i <- r | P ) F" := (BigOp.bigop (Znn 0) r (fun i => BigBody i addz P F))
  (at level 41, F at level 41, i, r, P at level 50).

Notation "\sumz_ ( i <- r ) F" := (BigOp.bigop (Znn 0) r (fun i => BigBody i addz true F))
  (at level 41, F at level 41, i, r at level 50).

Notation "\sumz_ ( d %| n ) F" := (\sumz_(d <- divisors n) F)
  (at level 41, F at level 41, d at level 50).


Canonical addz_monoid := Monoid.Law addzA add0z addz0.
Canonical addz_comoid := Monoid.ComLaw addzC.

Lemma sumzE : forall r, sumz r = \sumz_(i <- r) i.
Proof.
  elim=> [|h r IHr] ; rewrite BigOp.bigopE //.
Qed.

Lemma sumzDr {T : Type} : forall a f (s : seq T),
  \sumz_(x <- s) mulz a (f x)
  = mulz a (\sumz_(x <- s) f x).
Proof.
  move=> a f ; elim=> [|h s IHs] ; rewrite BigOp.bigopE /= ;
    first by rewrite mulz0.
  by rewrite -BigOp.bigopE IHs mulzDr.
Qed.

Lemma sumzDl {T : Type} : forall a f (s : seq T),
  \sumz_(x <- s) mulz (f x) a
  = mulz (\sumz_(x <- s) f x) a.
Proof.
  move=> a f s ;
    rewrite mulzC -sumzDr.
  apply eq_big ; first by [] ;
  move=> x _ ;
    by rewrite mulzC.
Qed.

Lemma sumz0 {T : Type} :
  forall f (s : seq T), all (eq_op (Znn 0)) [seq f x | x <- s]
  -> \sumz_(x <- s) f x = Znn 0.
Proof.
  move=> f ; elim=> [|h s IHs] ; move=> all_eq_0 ; rewrite BigOp.bigopE //=.
  rewrite /= in all_eq_0.
  move/andP in all_eq_0.
  destruct all_eq_0 as [f_h_eq_0 all_eq_0].
  move/eqP in f_h_eq_0.
  rewrite -f_h_eq_0 add0z -BigOp.bigopE.
  by apply: IHs.
Qed.

Lemma sumz_kronecker {T : eqType} : forall f (y : T) (s : seq T),
  \sumz_(x <- s) mulz (f x) (Znn (eq_op y x))
  = \sumz_(x <- s | eq_op y x) f x.
Proof.
  move=> f y ; elim=> [|h s IHs] ;
    rewrite BigOp.bigopE //=.
  rewrite -BigOp.bigopE IHs.
  case (y == h).
  by rewrite mulz1.
  by rewrite mulz0 add0z.
Qed.

Lemma sumz_div_inv : forall f n,
  \sumz_(d %| n) f d = \sumz_(d %| n) f (n %/ d).
Admitted.

Lemma sumz_div_mul : forall f m n,
  \sumz_(d %| m * n) f d = \sumz_(d1 %| m) (\sumz_(d2 %| n) f (d1 * d2)).
Admitted.

Lemma sumz_div_div :
  forall f n, 0 < n ->
  \sumz_(d1 %| n) \sumz_(d2 %| d1) f (n %/ d1) d2
  = \sumz_(d2 %| n) \sumz_(d %| n %/ d2) f d d2.
Proof.
  move=> f n n_gt_0 ; move: n n_gt_0 f.
  apply (primespow_induction (
    fun n => forall f,
      \sumz_ (d1 %| n) \sumz_ (d2 %| d1) f (n %/ d1) d2
      = \sumz_ (d2 %| n) \sumz_ (d %| n %/ d2) f d d2)
    ) ; first by rewrite BigOp.bigopE.
  move=> m n m_gt_0 n_gt_0 m_coprime_n sum_div_m sum_div_n f.
  rewrite ?sumz_div_mul.
Admitted.