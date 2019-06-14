From mathcomp Require Import ssreflect ssrfun eqtype seq ssrbool.


Lemma mem_head_or_behead {T : eqType} : forall (x : T) h l, x \in h::l = (x == h) || (x \in l).
Proof.
  move=> x h l.
  by unfold mem, in_mem.
Qed.

Lemma foldr_eq {T R : Type} :
  forall (f g : T -> R -> R) x s, f =2 g
  -> foldr f x s = foldr g x s.
Proof.
  move=> f g x ; elim=> [|h s IHs] f_eq_g ; first by [].
  rewrite /= f_eq_g IHs //.
Qed.

Lemma foldr_eq_in {T R : eqType} :
  forall (f g : T -> R -> R) x (s : seq T),
  (forall x y, x \in s -> f x y = g x y)
  -> foldr f x s = foldr g x s.
Proof.
  move=> f g x ; elim=> [|h s IHs] f_eq_g ; first by [].
  rewrite /= f_eq_g.
  rewrite IHs //.
  move=> x' y x'_in_s.
  apply f_eq_g.
  rewrite mem_head_or_behead x'_in_s.
    by case: (x' == h).
  by rewrite mem_head_or_behead eq_refl.
Qed.

