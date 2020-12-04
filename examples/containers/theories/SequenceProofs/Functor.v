Require Import GHC.Base.
Require Import Data.Sequence.Internal.

Require Import SequenceProofs.ToList.
Require Import SequenceProofs.ValidityFunction.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Ltac fold_classes_ := fold_classes; fold_toList.

Lemma fmap_fmap__Digit {A B C} (f : A -> B) (g : B -> C) (d : Digit A)
  : fmap g (fmap f d) = fmap (fun a => g (f a)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma fmap_ext__Digit {A B} (f g : A -> B) (d : Digit A)
  : (forall a, f a = g a) -> fmap f d = fmap g d.
Proof.
  intros E; destruct d; cbn; f_equal; reflexivity + apply E.
Qed.

Class Square_toList {T U A B} `{ToList T A} `{ToList U B} (f : A -> B) (g : T -> U) : Prop :=
  square_toList : forall a, toList (f a) = fmap g (toList a).

Instance toList_fmap__Digit {T U A B} `{ToList T A} `{ToList U B}
    (f : A -> B) (g : T -> U) {_ : Square_toList f g}
  : Square_toList (fmap (f := Digit) f) g.
Proof.
  intros []; cbn; rewrite !square_toList, ?map_app; auto.
Qed.

Instance toList_fmap__Node {T U A B} `{ToList T A} `{ToList U B}
    (f : A -> B) (g : T -> U) {_ : Square_toList f g}
  : Square_toList (fmap (f := Node) f) g.
Proof.
  intros []; cbn; rewrite !square_toList, ?map_app; auto.
Qed.

Lemma toList_fmap__FingerTree {T U A} {t : FingerTree A}
  : forall {B} `{ToList T A} `{ToList U B}
           {f : A -> B} {g : T -> U}
           {_ : Square_toList f g},
    toList (fmap f t) = fmap g (toList t).
Proof.
  induction t; cbn; intros * Hfg; fold_classes_; auto.
  rewrite (IHt _ _) with (f0 := fmap f) (g0 := g).
  - rewrite !map_app, !square_toList; reflexivity.
  - typeclasses eauto.
Qed.

Instance Square__FingerTree {T U A B} `{ToList T A} `{ToList U B}
    (f : A -> B) (g : T -> U) {_ : Square_toList f g}
  : Square_toList (fmap (f := FingerTree) f) g.
Proof.
  intros t; apply toList_fmap__FingerTree; auto.
Qed.

Instance Square__Elem {A B} (f : A -> B)
  : Square_toList (fmap (f := Elem) f) f.
Proof.
  intros []; reflexivity.
Qed.

Lemma toList_fmap_Seq {A B} (f : A -> B) (s : Seq A)
  : toList (fmap f s) = fmap f (toList s).
Proof.
  destruct s; cbn.
  apply toList_fmap__FingerTree.
Qed.
