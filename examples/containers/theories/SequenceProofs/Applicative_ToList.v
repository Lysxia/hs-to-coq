From Coq Require Import
  Lia Morphisms Program.Tactics.
Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Import GHC.Base.Notations.
Require Proofs.Data.Foldable.
Import GHC.Num.Notations.
Require Import CustomTactics.

Import ListNotations.

Require Import Data.Sequence.Internal.
From SequenceProofs Require Import
  ToList
  Functor
  Validity
  ValidityFunction
  Applicative_Internal
  Applicative_aptyMiddle.

Local Open Scope Z_scope.

Opaque aptyMiddle.

Ltac folds :=
  fold_classes;
  repeat (change @Base.Applicative__list_liftA2 with (@liftA2 list _ _)).

Lemma liftA2_singleton_list {a b c} (f : a -> b -> c) (x : a) (ys : list b)
  : liftA2 f [x] ys = fmap (f x) ys.
Proof.
  cbn. rewrite app_nil_r.
  rewrite flat_map_cons_f.
  reflexivity.
Qed.

Lemma liftA2_nil_r {a b c} (f : a -> b -> c) (xs : list a)
  : liftA2 f xs [] = [].
Proof.
  induction xs; cbn; auto.
Qed.

Lemma liftA2_cons {a b c} (f : a -> b -> c) (x : a) (xs : list a) (ys : list b)
  : liftA2 f (x :: xs) ys = fmap (f x) ys ++ liftA2 f xs ys.
Proof.
  reflexivity.
Qed.

Lemma liftA2_snoc {a b c} (f : a -> b -> c) (xs : list a) (x : a) (ys : list b)
  : liftA2 f (xs ++ [x]) ys = liftA2 f xs ys ++ fmap (f x) ys.
Proof.
Admitted.

Theorem toList_viewl {a} (ta : Seq a)
  : toList (viewl ta) = toList ta.
Proof.
Admitted.

Theorem toList_viewr {a} (ta : Seq a)
  : toList (viewr ta) = toList ta.
Proof.
Admitted.

Lemma toList_rigidify {a} (ta : FingerTree (Elem a))
  : toList (rigidify ta) = toList ta.
Proof.
Admitted.

Definition toList' {a} (r : Rigid a) : list a :=
  let tla : ToList a a := fun x => [x] in
  toList r.

Definition toList'_FT {a} (t : FingerTree a) : list a :=
  let tla : ToList a a := fun x => [x] in
  toList t.

Definition toList'_Digit23 {a} (t : Digit23 a) : list a :=
  let tla : ToList a a := fun x => [x] in
  toList t.

Definition toList'_FT_Node {a} (t : FingerTree (Node a)) : list a :=
  let tla : ToList a a := fun x => [x] in
  toList'_FT t >>= toList.

Lemma Thin_Node_ind (P : forall (a : Type), Thin (Node a) -> Prop)
    (EMPTY : forall (a : Type), P a EmptyTh)
    (SINGLE : forall (a : Type) x, P a (SingleTh x))
    (DEEP : forall (a : Type) s pr t sf (IH_Thin_Node : P (Node a) t), P a (DeepTh s pr t sf))
  : forall (a : Type) (t : Thin (Node a)), P a t.
Proof.
  fix SELF 2; intros ? []; [ apply EMPTY | apply SINGLE | apply DEEP, SELF ].
Qed.

Lemma square {A : Type} {a b c d : A}
  : a = b -> c = a -> b = d -> c = d.
Proof.
  intros.
  transitivity a; [ eassumption | ].
  transitivity b; eassumption.
Qed.

Lemma toList_aptyMiddle {b} (tb : Thin (Node b))
  : forall
    {a c b' c'} `{ToList b' b} `{ToList c' c}
    (firstf lastf : b -> c)
    (firstx lastx : a)
    (f : a -> b -> c) (g : a -> b' -> c')
    (ta : FingerTree (Elem a))
    (s : Int) (pr : Digit23 b) (sf : Digit23 b)
    (rb := Mk_Rigid s pr tb sf)
    (firstW : forall y, firstf y = f firstx y)
    (lastW : forall y, lastf y = f lastx y)
    (w : forall x y, toList (f x y) = fmap (g x) (toList y))
  ,    toList (fmap firstf pr)
    ++ toList (aptyMiddle firstf lastf f ta rb)
    ++ toList (fmap lastf sf)
  = fmap (g firstx) (toList rb) ++ liftA2 g (toList ta) (toList rb) ++ fmap (g lastx) (toList rb).
Proof.
  apply Thin_Node_ind with (t := tb); intros; rewrite unfold_aptyMiddle; cbn.
  - admit.
  - admit.
  - folds.
    specialize (IH_Thin_Node a0 (Node c) b' c' _ _).
    match goal with
    | [ |- context [ aptyMiddle ?firstf ?lastf ?f ?ta (Mk_Rigid ?s ?pr ?tb ?sf) ]] =>
      specialize (IH_Thin_Node firstf lastf firstx lastx f g ta s pr sf)
    end.
    hnf in IH_Thin_Node.
    prove_assumptions_of IH_Thin_Node.
    { intros []; cbn; rewrite !firstW; reflexivity. }
    { intros []; cbn; rewrite !lastW; reflexivity. }
    { intros ? []; cbn; rewrite !map_app, !w; reflexivity. }
    apply (square IH_Thin_Node).
    + admit.
    + admit.
Admitted.

Lemma toList_fmap_nodeToDigit {a b c} `{ToList c b} (f : a -> b) (t : _ a)
  : toList (fmap f (nodeToDigit t)) = toList (fmap f t).
Proof.
  destruct t; reflexivity.
Qed.

Theorem toList_liftA2 {a b c} (f : a -> b -> c) (ta : Seq a) (tb : Seq b)
  : toList (liftA2 f ta tb) = liftA2 f (toList ta) (toList tb).
Proof.
  destruct tb as [tb]; cbn.
  assert (L_ta := toList_viewl ta).
  destruct (viewl ta) as [ | xa ta' ]; cbn; cbn in L_ta.
  { rewrite <- L_ta. reflexivity. }
  assert (L_ta' := toList_viewr ta').
  destruct (viewr ta') as [ | ta'' xa' ]; cbn; cbn in L_ta'; folds.
  { rewrite <- L_ta' in L_ta.
    rewrite <- L_ta.
    rewrite liftA2_singleton_list.
    rewrite toList_fmap__FingerTree.
    reflexivity.
  }
  destruct ta'' as [ta'']; cbn in L_ta'.
  assert (L_tb := toList_rigidify tb).
  destruct (rigidify tb) as [ | [x] | [x] [y] | [x] [y] [z] | [s pr tb' sf]]; cbn; cbn in L_tb.
  - rewrite <- L_tb.
    rewrite liftA2_nil_r.
    reflexivity.
  - rewrite <- L_tb.
    admit.
  - admit.
  - admit.
  - rewrite 2 toList_fmap_nodeToDigit.
    fold_toList.
    change (@Base.Applicative__list_liftA2) with (@liftA2 list _ _).
    rewrite <- L_ta, <- L_ta'.
    rewrite liftA2_cons, liftA2_snoc.
    rewrite <- L_tb.
    apply toList_aptyMiddle; auto.
    intros ? []; reflexivity.
Admitted.
