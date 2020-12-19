From Coq Require Import
  Setoid
  Morphisms.

Require Import GHC.Base.
Require Import Data.Foldable.
Require Import Data.Sequence.Internal.

From Proofs Require Import
  GHC.Base
  Data.Foldable.

Require Import CustomTactics.
From SequenceProofs Require Import
  ToList
  ValidityFunction
  EqProp.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Ltac fold_Foldable :=
  repeat (change (Internal.Foldable__FingerTree_foldMap (m := ?m) (a := ?a)) with (foldMap (t := FingerTree) (m := m) (a := a)));
  repeat (change (Foldable.Foldable__list_foldMap (m := ?m) (a := ?a)) with (foldMap (t := list) (m := m) (a := a))).

Ltac fold_classes_ := fold_classes; fold_Foldable; fold_toList.

Fixpoint foldMapTree {m0 a0 : Type} {H2 : Semigroup m0}
               {H3 : Monoid m0} (arg_7__ : Node a0 -> m0)
               (arg_8__ : FingerTree (Node a0)) {struct arg_8__} : m0 :=
     match arg_8__ with
     | EmptyT => mempty
     | Single x => arg_7__ x
     | Deep _ pr m1 sf =>
         foldDigit _<>_ arg_7__ pr <>
         (foldMapTree (fun t0 : Node (Node a0) => foldNode _<>_ arg_7__ t0) m1 <>
          foldDigit _<>_ arg_7__ sf)
     end.

Lemma foldMap_app {a m} `{MonoidLaws m} (f : a -> m) (xs ys : list a)
  : foldMap f (xs ++ ys) === mappend (foldMap f xs) (foldMap f ys).
Proof.
  induction xs; cbn.
  - rewrite monoid_mempty_l. reflexivity.
  - unfold op_z2218U__. rewrite mappend_assoc. rewrite IHxs. reflexivity.
Qed.

Lemma foldDigit_toList {a m} `{MonoidLaws m} {f : a -> m}
    {b} {f0 : b -> m} `{ToList b a}
  : (forall x, f x === foldMap f0 (toList x)) ->
    forall d : Digit a, foldDigit _<>_ f d === foldMap f0 (toList d).
Proof.
  intros HFOLD []; cbn; fold_classes_;
    rewrite ?foldMap_app, <- !HFOLD, ?mappend_assoc;
    reflexivity.
Qed.

Lemma foldNode_toList {a m} `{MonoidLaws m} {f : a -> m}
    {b} {f0 : b -> m} `{ToList b a}
  : (forall x, f x === foldMap f0 (toList x)) ->
    forall d : Node a, foldNode _<>_ f d === foldMap f0 (toList d).
Proof.
  intros HFOLD []; cbn; fold_classes_;
    rewrite ?foldMap_app, <- !HFOLD, ?mappend_assoc;
    reflexivity.
Qed.

Lemma foldMapTree_toList {b m} `{MonoidLaws m} {f0 : b -> m}
    {a} `{TOLIST : ToList b a} {f : Node a -> m} {t : FingerTree (Node a)}
  : (forall x, f x === foldMap f0 (toList x)) ->
    foldMapTree f t === foldMap f0 (toList t).
Proof.
  revert a TOLIST f t; fix SELF 4; intros a TOLIST f [ | | i pr t sf]; cbn; fold_classes_.
  - reflexivity.
  - exact (fun x => x _).
  - specialize (SELF (Node a) _ (foldNode _<>_ f) t).
    intros HFOLD.
    prove_assumptions_of SELF.
    { apply foldNode_toList, HFOLD. }
    rewrite SELF.
    rewrite !(foldDigit_toList HFOLD), !foldMap_app.
    reflexivity.
Qed.

Lemma foldMap_toList__FingerTree {b m} `{MonoidLaws m} (f0 : b -> m)
    a `{ToList b a} (f : a -> m) (t : FingerTree a)
  : (forall x, f x === foldMap f0 (toList x)) ->
    foldMap f t === foldMap f0 (toList t).
Proof.
  destruct t; cbn; fold_classes_; intros HFOLD.
  - reflexivity.
  - auto.
  - rewrite 2 (foldDigit_toList HFOLD).
    unfold op_zlzg__.
    rewrite 2 foldMap_app.
    repeat apply proper_mappend; try reflexivity.
    apply foldMapTree_toList.
    apply foldNode_toList.
    apply HFOLD.
Qed.

Lemma foldMap_toList__Seq {a m} `{MonoidLaws m} (f : a -> m) (s : Seq a)
  : foldMap f s === foldMap f (toList s).
Proof.
  destruct s; cbn; fold_classes_.
  eapply foldMap_toList__FingerTree.
  intros []; cbn. unfold op_z2218U__.
  rewrite monoid_mempty_r.
  reflexivity.
Qed.
