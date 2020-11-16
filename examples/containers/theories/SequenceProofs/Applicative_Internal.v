From Coq Require Import
  Lia Morphisms.
Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Import GHC.Base.Notations.
Require Proofs.Data.Foldable.
Import GHC.Num.Notations.
Require Import CustomTactics.

Import ListNotations.

Require Import Data.Sequence.Internal.
Require Import SequenceProofs.Validity.
Require Import SequenceProofs.ValidityFunction.

Set Bullet Behavior "Strict Subproofs".

Theorem size_digit12ToDigit {A B} `{Sized A} `{Validity A} `{Sized B} `{Validity B}
    (f : A -> B) (d : Digit12 (Node A))
  : FSizedValid f ->
    valid d ->
    size (fmap (fmap f) (digit12ToDigit d)) = size d.
Proof.
  destruct d; cbn; fold_classes; intros; rewrite !size_fmap__Node; auto.
Qed.

Theorem FSized_mapMulFT {A B} `{Sized A} `{Validity A} `{Sized B} `{Validity B}
    (i : Int) (f : A -> B)
  : FMultSizedValid i f ->
    forall t : FingerTree A, size (mapMulFT i f t) = i * size t.
Proof.
  intros Hf; destruct t; cbn.
  - rewrite Z.mul_0_r; reflexivity.
  - apply Hf.
  - reflexivity.
Qed.

Theorem FMultSizedValid_mapMulNode {A B} `{Sized A} `{Validity A} `{SizedB : Sized B} `{ValidityB : Validity B}
    (i : Int) (f : A -> B)
  : FMultSizedValid i f ->
    FMultSizedValid i (mapMulNode i f).
Proof.
  intros [Hsizef Hvalidf].
  split; intros []; cbn; reflexivity + intros_valid.
  all: split; auto; rewrite !Hsizef; cbn; try lia.
Qed.

Theorem size_mapMulFT {A B} `{Sized A} `{Validity A} `{SizedB : Sized B} `{ValidityB : Validity B}
    (i : Int) (f : A -> B)
  : FMultSizedValid i f ->
    forall t : FingerTree A, size (mapMulFT i f t) = i * size t.
Proof.
  intros [Hf _] []; cbn; rewrite ?Hf; cbn; lia.
Qed.

Theorem valid_mapMulFT {A B} `{Sized A} `{Validity A} `{SizedB : Sized B} `{ValidityB : Validity B}
    (i : Int) (f : A -> B)
  : FMultSizedValid i f ->
    forall t : FingerTree A, valid t -> valid (mapMulFT i f t).
Proof.
  intros Hf t; revert B SizedB ValidityB f Hf; induction t; intros B SizedB ValidityB f Hf; cbn.
  - constructor.
  - apply Hf.
  - intros_valid.
    auto_valid; eauto using (valid_FMultSizedValid i f).
    { rewrite size_mapMulFT by auto using (FMultSizedValid_mapMulNode i f).
      rewrite 2 (size_fmap__Digit_mult i) by auto.
      subst i0; cbn; lia. }
    apply (IHt _ _ _ _ _); auto using (FMultSizedValid_mapMulNode i f).
Qed.

Theorem size_squashL {A} (d : Digit23 A) (ns : Digit12 (Node A))
  : size (squashL d ns) = size d + size ns.
Proof. destruct ns; cbn; lia. Qed.

Theorem size_squashR {A} (ns : Digit12 (Node A)) (d : Digit23 A)
  : size (squashR ns d) = size ns + size d.
Proof. destruct ns; cbn; lia. Qed.

Theorem valid_squashL {A} `{Sized A} `{Validity A} (d : Digit23 A) (ns : Digit12 (Node A))
  : valid d -> valid ns -> valid (squashL d ns).
Proof. destruct ns; cbn; firstorder lia. Qed.

Theorem valid_squashR {A} `{Sized A} `{Validity A} (ns : Digit12 (Node A)) (d : Digit23 A)
  : valid ns -> valid d -> valid (squashR ns d).
Proof. destruct ns; cbn; firstorder lia. Qed.

Lemma unfold_pullL {A} (s : Int) (m : FingerTree (Node A)) (d : Digit A)
  : pullL s m d
  = match viewLTree m with
    | ConsLTree pr m' => Deep s (nodeToDigit pr) m' d
    | EmptyLTree => digitToTree' s d
    end.
Proof.
  destruct m; reflexivity.
Qed.

Lemma valid_digitToTree' {A} `{Sized A} `{Validity A} (s : Int) (d : Digit A)
  : size d = s -> valid d -> valid (digitToTree' s d).
Proof.
  destruct d; cbn; intros ?; intros_valid; auto_valid; lia.
Qed.

Lemma size_digitToTree' {A} `{Sized A} (s : Int) (d : Digit A)
  : size d = s -> size (digitToTree' s d) = s.
Proof.
  destruct d; cbn; lia.
Qed.

Theorem valid_viewLTree {A} `{Sized A} `{Validity A} (t : FingerTree A)
  : valid t -> valid (viewLTree t) /\ size (viewLTree t) = size t.
Proof.
  induction t as [ | | A s d ]; cbn; fold_classes.
  - auto.
  - split; auto; lia.
  - intros V; decompose_conj V.
    specialize (IHt _ _ H3).
    revert H1 H2; destruct d; cbn; fold_classes; do 2 intros_valid; auto_valid; auto.
    1,2: rewrite ?unfold_pullL; destruct (viewLTree t); cbn in *; revert H1 IHt;
      fold_classes; do 2 intros_valid; auto_valid.
    1: rewrite size_nodeToDigit by auto.
    2: apply valid_digitToTree'; auto; lia.
    3: rewrite size_digitToTree' by lia.
    all: lia.
Qed.

Theorem valid_viewRTree {A} `{Sized A} `{Validity A} (t : FingerTree A)
  : valid t -> valid (viewRTree t) /\ size (viewRTree t) = size t.
Proof.
Admitted.

Theorem valid_viewl {A} (t : Seq A) : valid t -> valid (viewl t).
Proof.
  destruct t as [t]; cbn.
  intros Vt.
  destruct (valid_viewLTree t Vt) as [VVt SVt].
  destruct (viewLTree t) as [ [x] | ]; [ destruct VVt | ]; auto.
Qed.

Theorem size_viewl {A} (t : Seq A) : size (viewl t) = size t.
Proof.
Admitted.

Theorem valid_viewr {A} (t : Seq A) : valid t -> valid (viewr t).
Proof.
  destruct t as [t]; cbn.
  intros Vt.
  destruct (valid_viewRTree t Vt) as [VVt SVt].
  destruct (viewRTree t) as [ ? [x] | ]; [ destruct VVt | ]; auto.
Qed.

Theorem size_viewr {A} (t : Seq A) : size (viewr t) = size t.
Admitted.

Theorem valid_rigidify {A} (t : FingerTree (Elem A))
  : valid t -> valid (rigidify t).
Proof.
  destruct t as [ | | s pr m sf ]; cbn; auto.
  intros_valid.
  destruct pr as [ a | a b | a b c | a b c d ].
  - pose proof (valid_viewLTree m); destruct (viewLTree m) as [[] m' | ].
    + admit.
    + admit.
    + destruct sf; cbn; auto.
      (* m is empty *) admit. admit.
  - admit.
  - admit.
  - admit.
Admitted.

Theorem size_rigidify {A} (t : FingerTree (Elem A))
  : size (rigidify t) = size t.
Proof.
Admitted.

Theorem valid_lift2FT {A B C} (f : A -> B -> C)
    (x : A) (xs : FingerTree (Elem A)) (x1 : A) (y1 y2 : B)
  : valid xs -> valid (lift2FT f x xs x1 (y1, y2)).
Proof.
  cbn - [Z.add]. fold_classes.
  assert (FMultSizedValid 2%Z (fun '(Mk_Elem x0) =>
            Node2 2%Z (Mk_Elem (f x0 y1)) (Mk_Elem (f x0 y2))))
    by (repeat (constructor + intros [])).
  intros Hxs. splits; try exact I.
  - rewrite size_mapMulFT; auto.
    cbn [op_zt__ Num_Integer__]. lia.
  - apply valid_mapMulFT; auto.
Qed.

Theorem size_lift2FT {A B C} `{Sized B} (f : A -> B -> C)
    (x : A) (xs : FingerTree (Elem A)) (x1 : A) (y1 y2 : B)
  : size (lift2FT f x xs x1 (y1, y2)) = #2 + size xs + size y1 + size y2.
Proof.
Admitted.

Theorem valid_lift3FT {A B C} (f : A -> B -> C)
    (x : A) (xs : FingerTree (Elem A)) (x1 : A) (y1 y2 y3 : B)
  : valid xs -> valid (lift3FT f x xs x1 (y1, y2, y3)).
Proof.
  cbn - [Z.add]. fold_classes.
  assert (FMultSizedValid 3%Z (fun '(Mk_Elem x0) =>
            Node3 3%Z (Mk_Elem (f x0 y1)) (Mk_Elem (f x0 y2)) (Mk_Elem (f x0 y3))))
    by (repeat (constructor + intros [])).
  intros Hxs. splits; try exact I.
  - rewrite size_mapMulFT; auto.
    cbn [op_zt__ Num_Integer__]. lia.
  - apply valid_mapMulFT; auto.
Qed.

Theorem size_lift3FT {A B C} `{Sized B} (f : A -> B -> C)
    (x : A) (xs : FingerTree (Elem A)) (x1 : A) (y1 y2 y3 : B)
  : size (lift3FT f x xs x1 (y1, y2, y3)) = #2 + size xs + size y1 + size y2 + size y3.
Proof.
Admitted.
