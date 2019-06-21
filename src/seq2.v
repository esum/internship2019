From mathcomp Require Import ssreflect ssrfun eqtype seq ssrbool bigop.


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

Lemma eq_map_eq {T1 T2 : Type} :
  forall {f g : T1 -> T2} {s1 s2 : seq T1}, f =1 g
  -> s1 = s2
  -> [seq f x | x <- s1] = [seq g x | x <- s2].
Proof.
  move=> f g s1 s2 f_eq_g s1_eq_s2.
  rewrite s1_eq_s2.
  by apply eq_map.
Qed.

Lemma eq_in_map_eq {T1 : eqType} {T2 : Type} :
  forall {f g : T1 -> T2} {s1 s2 : seq T1},
  {in s1, f =1 g}
  -> s1 = s2
  -> [seq f x | x <- s1] = [seq g x | x <- s2].
Proof.
  move=> f g s1 s2 f_eq_g s1_eq_s2.
  rewrite -s1_eq_s2.
  by apply eq_in_map.
Qed.

Lemma map_const {T1 T2 : Type} :
  forall {s : seq T1} {x : T2}, [seq x | _ <- s] = nseq (size s) x.
Proof.
    by elim=> [|h s IHs] x // ; rewrite /= IHs.
Qed.

Lemma mem_big_eq {T : eqType} :
  forall {x : T} {s}, x \in s = \big[orb/false]_(y <- s) (y == x).
Proof.
  move=> x ; elim=> [|h s IHs] ;
    first by rewrite big_nil.
  by rewrite big_cons mem_head_or_behead /= IHs eq_sym.
Qed.
