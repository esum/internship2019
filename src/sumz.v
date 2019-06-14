From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq ssreflect.prime div.
From mathcomp Require Import path fintype bigop.
Add LoadPath "~/git/git.graillo.tf/stage/2019-06/src".
Require Import seq2 ssrz arith.


Definition sumz := foldr addz (Znn 0).

Notation "\sumz_ ( i <- r ) F" := (BigOp.bigop (Znn 0) r (fun i => BigBody i addz true F))
  (at level 41, F at level 41, i, r at level 50).

Notation "\sumz_ ( d %| n ) F" := (\sumz_(d <- divisors n) F)
  (at level 41, F at level 41, d at level 50).

Lemma sumzE : forall r, sumz r = \sumz_(i <- r) i.
Proof.
  elim=> [|h r IHr] ; rewrite BigOp.bigopE //.
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

Lemma sumz_div_inv : forall f n,
  \sumz_(d %| n) f d = \sumz_(d %| n) f (n %/ d).
Admitted.

Lemma sumz_div_div : forall f m n,
  \sumz_(d %| m * n) f d = \sumz_(d1 %| m) (\sumz_(d2 %| n) f (d1 * d2)).
Admitted.
