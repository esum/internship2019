From mathcomp Require Import ssreflect eqtype seq ssrfun ssrbool ssrnat prime div.
From mathcomp Require Import path fintype bigop.

Inductive Z : Type :=
  | Znn : nat -> Z
  | Zne : nat -> Z.

Notation "0" := (Znn 0) : Z_scope.
Notation "1" := (Znn 1) : Z_scope.

Definition abs k :=
  match k with
  | Znn n => n
  | Zne n => n.+1
  end.

Definition succz k :=
  match k with
  | Znn k    => Znn k.+1
  | Zne 0    => Znn 0
  | Zne k.+1 => Zne k
  end.

Definition predz k :=
  match k with
  | Znn k.+1 => Znn k
  | Znn 0    => Zne 0
  | Zne k    => Zne k.+1
  end.

Lemma succzK : cancel succz predz. Proof. by case=> [k|[|n]]. Qed.
Lemma predzK : cancel predz succz. Proof. by case=> [[|n]|k]. Qed.
Lemma succz_inj : injective succz.
Proof.
  case=> [a|[|m]] [b|[|n]] //= ; by inversion 1.
Qed.
Lemma predz_inj : injective predz.
Proof.
  case=> [[|m]|a] [[|n]|b] //= ; by inversion 1.
Qed.

Definition eqz a b :=
  match a, b with
  | Znn a, Znn b => a == b
  | Zne a, Zne b => a == b
  | _    , _     => false
  end.

Lemma eqzP : Equality.axiom eqz.
  move=> a b ; apply: (iffP idP) => [|<-].
  case: a b => [a|a] [b|b] //= ; by [move/eqnP=> H; rewrite H].
  case: a => [a|a] //=.
Qed.

Canonical z_eqMixin := EqMixin eqzP.
Canonical z_eqType := Eval hnf in EqType Z z_eqMixin.

Arguments eqzP {x y}.

Lemma eqzE : eqz = eq_op. Proof. by []. Qed.

Lemma eqzSS a b : (succz a == succz b) = (a == b). Proof.
  by case: a b => [m|[|m]] [n|[|n]].
Qed.

Lemma eqzpp a b : (predz a == predz b) = (a == b). Proof.
  by case: a b => [[|m]|m] [[|n]|n].
Qed.

Lemma z_irrelevance (x y : Z) (E E' : x = y) : E = E'.
Proof. exact: eq_irrelevance. Qed.

Section zop.

Local Fixpoint addz_fix a b c {struct c} :=
  match a, b with
  | Znn m   , Znn n    => Znn (m + n)
  | Zne m   , Zne n    => Zne (m + n).+1
  | Znn 0   , _        => b
  | _       , Znn 0    => a
  | Znn m.+1, Zne 0    => Znn m
  | Zne 0   , Znn n.+1 => Znn n
  | Znn m.+1, Zne n.+1 =>
    match c with
    | c.+1 => addz_fix (Znn m) (Zne n) c
    | 0    => Znn 0
    end
  | Zne m.+1, Znn n.+1 =>
     match c with
    | c.+1 => addz_fix (Zne m) (Znn n) c
    | 0    => Znn 0
    end
  end.

Local Lemma match_n_eq {T : Type} : forall (n : nat) (m : T), match n with 0 => m | S _ => m end = m. Proof. by case. Qed.

Lemma aux_min : forall a b c, Nat.min (abs a) (abs b) <= c ->
  addz_fix a b c = addz_fix a b (Nat.min (abs a) (abs b)).
Proof.
  move=> a b c.
  move: a b.
  elim: c => [|c IHc] ; case=> [[|m]|[|m]] [[|n]|[|n]] ; move=> H ; try by [].
    simpl abs in *. 
    rewrite -[addz_fix (Znn m.+1) (Zne n.+1) c.+1]/(addz_fix (Znn m) (Zne n) c) ;
    rewrite -[addz_fix (Znn m.+1) (Zne n.+1) (Nat.min m.+1 n.+2)]/(addz_fix (Znn m) (Zne n) (Nat.min m n.+1)) ;
    rewrite IHc //=.
    simpl abs in *. 
    rewrite -[addz_fix (Zne m.+1) (Znn n.+1) c.+1]/(addz_fix (Zne m) (Znn n) c) ;
    rewrite -[addz_fix (Zne m.+1) (Znn n.+1) (Nat.min m.+2 n.+1)]/(addz_fix (Zne m) (Znn n) (Nat.min m.+1 n)) ;
    rewrite IHc //=.
Qed.

Definition addz_rec m n := addz_fix m n (Nat.min (abs m) (abs n)).

Definition addz := nosimpl addz_rec.
Notation "m + n" := (addn m n) : Z_scope.

Lemma add0z : left_id (Znn 0) addz.
Proof. by case. Qed.

Lemma addz0 : right_id (Znn 0) addz.
Proof.
  unfold addz.
  case=> [[|n]|[|n]] // ; unfold addz_rec ; simpl ;
  by rewrite addn0.
Qed.

Lemma addSz : forall a b, addz (succz a) b = succz (addz a b).
Proof.
  case=> a ; elim: a => [|a IHa] ; case=> b ; elim: b => [|b IHb] //.
  rewrite -[addz (succz (Znn a.+1)) (Zne b.+1)]/(addz (succz (Znn a)) (Zne b))
    IHa //.
  rewrite addz0 //.
  rewrite /=.
  rewrite -[addz (Zne a.+1) (Znn b.+1)]/(addz (Zne a) (Znn b))
   -IHa.
  by destruct a.
  rewrite /= addn0 ; destruct a ;
    first by [] ;
    last unfold addz, addz_rec ; rewrite /= addn0 //.
  by destruct a.
Qed.

Lemma addpz : forall a b, addz (predz a) b = predz (addz a b).
Proof.
Admitted.

Lemma addzCA : left_commutative addz.
Proof.
Admitted.

Lemma addzC : commutative addz.
Proof.
  unfold addz.
  move=> [a|a] ; first unfold addz_rec.
    case=> [b/=|b].
    case: a => [|a] ; case: b => [|b] /= ; congr Znn ; ring.
    move: a b.
      elim=> [|a IHa] ; first by case.
      case=> [|b] //= ; rewrite IHa ; congr addz_fix.
  move: a ; unfold addz_rec ; elim=> [|a IHa].
    case=> [[|b]|[|b]] //= ; congr Zne ; ring.
    case=> [[|b]|[|b]] //= ; [by rewrite IHa | |] ; congr Zne ; ring.
Qed.

Lemma addz1 k : addz k (Znn 1) = succz k.
Proof.
  case: k => [n|[|n]].
    unfold addz, addz_rec ; simpl.
    by case: (Nat.min n 1) => [|m] ; rewrite /= match_n_eq addn1.
    by [].
    by unfold addz, addz_rec ; rewrite /= match_n_eq.
Qed.

Lemma addzA : associative addz.
Proof.
  by move=> a b c ; rewrite (addzC b) addzCA addzC.
Qed.

Lemma addzAC : right_commutative addz.
Proof. by move=> a b c; rewrite -!addzA (addzC b). Qed.

Lemma addzACA : interchange addz addz.
Proof. by move=> a b c d; rewrite -!addzA (addzCA b). Qed.

Lemma addzS : forall a b, addz a (succz b) = succz (addz a b).
Proof.
  move=> a b.
  by rewrite (addzC a) (addzC a) addSz.
Qed.

Lemma addzp : forall a b, addz a (predz b) = predz (addz a b).
Proof.
  move=> a b.
  by rewrite (addzC a) (addzC a) addpz.
Qed.

Lemma eqz_add2l c a b : ((addz c a) == (addz c b)) = (a == b).
Proof.
  move: a b.
  case: c => [m|m] ; elim: m => [|m IHm].
    case=> [n|n] [p|p] ; unfold addz, addz_rec ; rewrite /= ?add0n //.
    case=> [[|n]|[|n]] [[|p]|[|p]] ; by rewrite -[Znn m.+1]/(succz (Znn m)) ?addSz ?eqzSS IHm.
    case=> [[|n]|[|n]].
      move=> [[|p]|[|p]] ; unfold addz, addz_rec ; rewrite //.
      move=> [[|p]|[|p]] ; rewrite -[Znn n.+1]/(succz (Znn n)) ?addzS -?addSz /= add0z ?addz0.
        by elim: n => [|n IHn].
        elim: n => [|n IHn] ;  unfold addz, addz_rec ; rewrite //.
        elim: n => [|n IHn] ;  unfold addz, addz_rec ; rewrite //.
        elim: n => [|n IHn] ;  unfold addz, addz_rec ; rewrite //.
      move=> [[|p]|[|p]] ; unfold addz, addz_rec ; rewrite //.
      move=> [[|p]|[|p]] ; unfold addz, addz_rec ; rewrite //.
    case=> [[|n]|[|n]] [[|p]|[|p]] ; rewrite -[Zne m.+1]/(predz (Zne m)) ?addpz eqzpp //.
Qed.

Lemma eqz_add2r c a b : ((addz a c) == (addz b c)) = (a == b).
Proof. by rewrite -!(addzC c) eqz_add2l. Qed.

Lemma addzI : right_injective addz.
Proof.
  move=> a b c Heq.
  apply: eqP.
  by rewrite -(eqz_add2l a) Heq eqxx.
Qed.

Definition oppz k :=
  match k with
  | Znn 0    => Znn 0
  | Znn n.+1 => Zne n
  | Zne n    => Znn n.+1
  end.

Lemma oppz_inv : involutive oppz.
Proof.
  by move=> [[|n]|[|n]].
Qed.

Lemma oppz_abs k : abs (oppz k) = abs k.
Proof.
  by case: k => [[|n]|[|n]].
Qed.

Lemma oppz0 k : (oppz k == Znn 0) = (k ==  Znn 0).
Proof.
  by case: k => [[|n]|[|n]].
Qed.

Definition subz_rec a b := addz a (oppz b).

Definition subz := nosimpl subz_rec.

Lemma subz0 : right_id (Znn 0) subz.
Proof.
  move=> k ; unfold subz, subz_rec ; rewrite /= addz0 //.
Qed.

Lemma subzz : self_inverse (Znn 0) subz.
Proof.
  move=> [[|n]|[|n]] // ; elim: n => [|n IHn] //.
Qed.

End zop.

Definition leqz a b :=
  match a, b with
  | Znn m, Znn n => m <= n
  | Znn _, Zne _ => false
  | Zne _, Znn _ => true
  | Zne m, Zne n => n <= m
  end.

Notation "m <= n" := (leqz m n) : Z_scope.
Notation "m < n"  := (succz m <= n) : Z_scope.

Definition mulz a b :=
  match a, b with
  | Znn 0   , _        => Znn 0
  | _       , Znn 0    => Znn 0
  | Znn m   , Znn n    => Znn (m * n)
  | Znn m.+1, Zne n    => Zne (m * n + m + n)
  | Zne m   , Znn n.+1 => Zne (m * n + m + n)
  | Zne m   , Zne n    => Znn (m.+1 * n.+1)
  end.

Lemma mul0z : left_zero (Znn 0) mulz. Proof. by case. Qed.
Lemma mulz0 : right_zero (Znn 0) mulz. Proof. by case=> [[|n]|n]. Qed.

Lemma mulzC : commutative mulz.
Proof.
  case=> [[|a]|a] [[|b]|b] //= ; [congr Znn|congr Zne|congr Zne|congr Znn] ; ring.
Qed.

Lemma mul1z : left_id  (Znn 1) mulz. Proof. case=> [[|?]|[|?]] ; rewrite /= ?mul1n //. Qed.
Lemma mulz1 : right_id (Znn 1) mulz. Proof. case=> [[|?]|[|?]] ; rewrite /= ?muln1 // ; congr Zne ; ring. Qed.

