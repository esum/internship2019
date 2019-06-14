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

Lemma sumz_div_inv : forall f n,
  \sumz_(d %| n) f d = \sumz_(d %| n) f (n %/ d).
Admitted.

Search "divisors".

Lemma sumz_div_div : forall f m n,
  \sumz_(d %| m * n) f d = \sumz_(d1 %| m) (\sumz_(d2 %| n) f (d1 * d2)).
Admitted.
