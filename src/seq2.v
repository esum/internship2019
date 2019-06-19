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

Lemma zip_map {T1 T2 R1 R2 : Type} :
  forall {f : T1 -> R1} {g : T2 -> R2} (s1 : seq T1) (s2 : seq T2),
  zip [seq f x | x <- s1] [seq g x | x <- s2] = [seq (f x.1, g x.2) | x <- zip s1 s2].
Proof.
  move=> f g ; elim=> [|h1 s1 IHs1] [|h2 s2] //.
  by rewrite /= IHs1.
Qed.
