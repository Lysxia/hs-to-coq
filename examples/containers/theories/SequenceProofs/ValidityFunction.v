Require Import GHC.Base.
Import GHC.Base.Notations.
Import ListNotations.
Require Import Data.Sequence.Internal.
Require Import SequenceProofs.Sized.
Require Import SequenceProofs.Validity.

Ltac fold_classes :=
  repeat (change (@Internal.Functor__FingerTree_fmap) with (@fmap FingerTree _));
  repeat (change (@Internal.Functor__Digit_fmap) with (@fmap Digit _));
  repeat (change (@Internal.Functor__Node_fmap) with (@fmap Node _));
  repeat (change (@Internal.Sized__FingerTree_size ?A _) with (@size (FingerTree A) _));
  repeat (change (@Internal.Sized__Digit_size ?A _) with (@size (Digit A) _));
  repeat (change (@Internal.Sized__Node_size ?A) with (@size (Node A) _));
  repeat (change (@Internal.Sized__Elem_size ?A) with (@size (Elem A) _));
  repeat (change (@Internal.Foldable__Digit_sum ?A) with (@Foldable.sum Digit _ A));
  repeat (change (Foldable.sum (fmap size ?d)) with (size d)).


Section ValidityFunction.

Context {A B : Type} `{Sized A} `{Validity A} `{Sized B} `{Validity B}.

(* Functions are valid when they preserve validity. *)
Global Instance Validity__Fun : Validity (A -> B) :=
  fun f => (forall a : A, valid a -> valid (f a)).

Definition FSizedValid (f : A -> B) : Prop :=
  (forall a, size (f a) = size a) /\
  (forall a, valid a -> valid (f a)).

Definition FMultSizedValid (x : Int) (f : A -> B) : Prop :=
  (forall a, size (f a) = x * size a) /\
  (forall a, valid a -> valid (f a)).

Lemma valid_FSizedValid (f : A -> B)
  : FSizedValid f -> valid f.
Proof. apply proj2. Qed.

Lemma valid_FMultSizedValid (x : Int) (f : A -> B)
  : FMultSizedValid x f -> valid f.
Proof. apply proj2. Qed.

End ValidityFunction.

Section FmapValid.

Context {A B : Type} `{Sized A} `{Validity A} `{SizedB : Sized B} `{ValidityB : Validity B}.

Theorem valid_fmap__Node (f : A -> B)
  : FSizedValid f -> valid (fmap (f := Node) f).
Proof.
  intros [Hsize Hvalid] []; cbn;
  rewrite !Hsize; intros_valid; auto.
Qed.

Theorem size_fmap__Node (f : A -> B)
  : FSizedValid f ->
    forall (t : Node A), size (fmap f t) = size t.
Proof.
  intros [Hsize Hvalid].
  destruct t; cbn; rewrite ?Hsize; reflexivity.
Qed.

Theorem FSizedValid_fmap__Node (f : A -> B)
  : FSizedValid f -> FSizedValid (fmap (f := Node) f).
Proof.
  split; [ apply size_fmap__Node; auto | apply valid_fmap__Node; auto ].
Qed.

Theorem size_fmap__Digit (f : A -> B)
  : FSizedValid f ->
    forall (t : Digit A), size (fmap f t) = size t.
Proof.
  intros [Hsize Hvalid].
  destruct t; cbn; try rewrite ?Hsize; reflexivity.
Qed.

Lemma size_fmap__Digit_mult (i : Int) (f : A -> B) (d : Digit A)
  : FMultSizedValid i f ->
    size (fmap f d) = i * size d.
Proof.
  intros [Hsize Hvalid]; destruct d; cbn; rewrite !Hsize; cbn;
    rewrite ?Z.mul_add_distr_l; reflexivity.
Qed.

Theorem valid_fmap__Digit (f : A -> B)
  : valid f -> valid (fmap (f := Digit) f).
Proof.
  unfold valid; intros Hvalid []; cbn; intros_valid; auto.
Qed.

Theorem FSizedValid_fmap__Digit (f : A -> B)
  : FSizedValid f -> FSizedValid (fmap (f := Digit) f).
Proof.
  split; [ apply size_fmap__Digit; auto | apply valid_fmap__Digit, valid_FSizedValid; auto ].
Qed.

Theorem valid_digit12ToDigit : valid digit12ToDigit.
Proof.
  intros []; auto.
Qed.

End FmapValid.

Theorem size_fmap__FingerTree
    {A B : Type} `{Sized A} `{Validity A} `{SizedB : Sized B} `{ValidityB : Validity B}
    (f : A -> B) (t : FingerTree A)
  : FSizedValid f -> size (fmap f t) = size t.
Proof.
  revert B SizedB ValidityB f; induction t; intros B SizedB ValidityB f Hf.
  - auto.
  - apply Hf.
  - reflexivity.
Qed.

Theorem valid_fmap__FingerTree
    {A B : Type} `{Sized A} `{Validity A} `{SizedB : Sized B} `{ValidityB : Validity B}
    (f : A -> B) (t : FingerTree A)
  : FSizedValid f -> valid t -> valid (fmap f t).
Proof.
  revert B SizedB ValidityB f; induction t; intros B SizedB ValidityB f Hf.
  - auto.
  - apply Hf.
  - intros_valid. cbn. fold_classes.
    rewrite 2 size_fmap__Digit by auto.
    rewrite size_fmap__FingerTree by (apply FSizedValid_fmap__Node; auto).
    split; [ auto | split; [| split]].
    1,3:apply valid_fmap__Digit; auto; apply valid_FSizedValid; auto.
    { apply (IHt _ _ _ _ _ _); auto; apply FSizedValid_fmap__Node; auto. }
Qed.

Lemma valid__Elem {A B} (f : Elem A -> Elem B) : valid f.
Proof. constructor. Qed.

Lemma FSizedValid__Elem {A B} (f : Elem A -> Elem B) : FSizedValid f.
Proof. repeat constructor. Qed.

Theorem valid_fmap__Seq {A B} (f : A -> B) (t : Seq A) : valid t -> valid (fmap f t).
Proof.
  destruct t. apply valid_fmap__FingerTree. apply FSizedValid__Elem.
Qed.

Create HintDb validity.

Lemma size_nodeToDigit {A} `{Sized A} `{Validity A} (n : Node A)
  : valid n -> size (nodeToDigit n) = size n.
Proof.
  destruct n; cbn; firstorder.
Qed.

Lemma valid_nodeToDigit {A} `{Sized A} `{Validity A} : valid nodeToDigit.
Proof. intros []; firstorder. Qed.
Hint Resolve valid_nodeToDigit : validity.

Ltac auto_valid_ :=
  intros;
  assumption +
  lazymatch goal with
  | [ |- valid (A := Elem _) _ ] => constructor
  | [ |- valid (A := Elem _ -> Elem _) _ ] => constructor
  | [ |- FSizedValid (B := Elem _) _ ] => apply FSizedValid__Elem
  (* fmap with one argument *)
  | [ |- valid (fmap (f := Digit) _) ] => apply valid_fmap__Digit; auto_valid_
  | [ |- valid (fmap (f := Node) _) ] => apply valid_fmap__Node; auto_valid_
  (* fmap with two arguments *)
  | [ |- valid (fmap (f := Digit) _ _) ] => apply valid_fmap__Digit; auto_valid_
  | [ |- valid (fmap (f := Node) _ _) ] => apply valid_fmap__Node; auto_valid_
  | [ |- FSizedValid (fmap (f := Digit) _) ] => apply FSizedValid_fmap__Digit; auto_valid_
  | [ |- FSizedValid (fmap (f := Node) _) ] => apply FSizedValid_fmap__Node; auto_valid_
  | [ |- FSizedValid ((_ GHC.Base.∘ _) _) ] => unfold op_z2218U__; auto_valid_
  | [ H : FSizedValid ?f |- valid ?f ] => revert H; apply valid_FSizedValid
  | [ |- valid (digit12ToDigit _) ] => apply valid_digit12ToDigit; auto_valid_
  | [ |- valid (nodeToDigit _) ] => apply valid_nodeToDigit; auto_valid_
  | [ |- _ /\ _ ] => split; auto_valid_
  | _ => auto with validity
  end.

Ltac auto_valid := fold_classes; auto_valid_.
