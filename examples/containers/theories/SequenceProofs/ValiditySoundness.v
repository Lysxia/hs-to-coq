From Coq Require Import
  Lia Morphisms.  (* For [Proper] *)

Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Proofs.Data.Foldable.
Import ListNotations.
Require Import Data.Sequence.Internal.
Require Import SequenceProofs.Validity.
Require Import SequenceProofs.ToList.

Class ValiditySound T A `{ToList T A} `{Sized A} `{Validity A} : Prop :=
  validity_sound : forall (x : A), valid x -> size x = List.length (toList x).

Ltac rewrite_size :=
  rewrite <- !validity_sound by assumption;
  try (reflexivity + assumption).

Ltac auto_ValiditySound_ ih :=
  intros_valid;
  length_apps;
  fold_valid;
  fold_toList;
  ih tt;
  rewrite_size.

Ltac auto_ValiditySound := auto_ValiditySound_ ltac:(fun _ => idtac).

Instance ValiditySound__Elem {T} : ValiditySound T (Elem T).
Proof.
  intros []; reflexivity.
Qed.

Instance ValiditySound_Digit {T A} `{ValiditySound T A} : ValiditySound T (Digit A).
Proof.
  intros d; revert H H0 H1 H2; induction d; intros H H0 H1 H2; cbn;
    auto_ValiditySound.
Qed.

Instance ValiditySound_Node {T A} `{ValiditySound T A} : ValiditySound T (Node A).
Proof.
  intros n; revert H H0 H1 H2; induction n; intros H H0 H1 H2; cbn;
    auto_ValiditySound.
Qed.

Instance ValiditySound_FingerTree {T A} `{ValiditySound T A} : ValiditySound T (FingerTree A).
Proof.
  intros t; revert H H0 H1 H2; induction t; intros H H0 H1 H2.
  - reflexivity.
  - exact (validity_sound (T := T) (A := a) _).
  - cbn.
    auto_ValiditySound_ ltac:(fun _ => rewrite <- (IHt _ _ _ _) by assumption).
Qed.

Theorem length_toList_Seq {A}
  : forall (z : Seq A), valid z -> length z = List.length (toList z).
Proof.
  intros []; cbn - [List.length].
  exact (validity_sound (T := A) (A := FingerTree (Elem A)) _).
Qed.

Fixpoint depth {A} (t : FingerTree A) : Z :=
  match t with
  | EmptyT => 0
  | Single _ => 0
  | Deep _ _ t' _ => 1 + depth t'
  end.


Parameter U : Z.

Local Open Scope Z_scope.

Lemma nonnegative_depth {A} (t : FingerTree A) : 0 <= depth t.
Proof.
  induction t; cbn - [Z.add]; lia.
Qed.

Ltac Z_assum :=
  assumption + apply Zle_bool_imp_le; reflexivity.

Lemma Z_pow_succ (x y : Z) :
  0 <= y ->
  Z.pow x (1 + y) = x * Z.pow x y.
Proof.
  intros.
  rewrite Z.pow_add_r by Z_assum.
  rewrite Z.pow_1_r.
  reflexivity.
Qed.

Class NonNegative (b : Z) : Prop :=
  nonnegative : 0 <= b.

Instance NonNegative_mul_3 (b : Z) `{NonNegative b} : NonNegative (3 * b).
Proof.
  unfold NonNegative in *. lia.
Qed.

Class BoundedLength {T} A `{ToList T A} (b : Z) : Prop :=
  bounded_length : forall (a : A), List.length (toList a) <= b.

Instance Proper_Z_add_le : Proper (Z.le ==> Z.le ==> Z.le) Z.add.
Proof.
  intros x y Hxy p q Hpq.
  apply Z.add_le_mono; auto.
Qed.

Lemma Z_mul_const_l_le (x y : Z) : 0 <= x -> 1 <= y -> x <= y * x.
Proof.
  intros. rewrite <- (Z.mul_1_l x) at 1. apply Z.mul_le_mono_nonneg_r; auto.
Qed.

Instance Proper_Z_mul_4_le : Proper (Z.le ==> Z.le) (Z.mul 4).
Proof.
  intros x y Hxy.
  apply Z.mul_le_mono_pos_l; lia.
Qed.

Instance BoundedLength_Digit {T A} `{ToList T A} (b : Z)
  : NonNegative b -> BoundedLength A b -> BoundedLength (Digit A) (4 * b).
Proof.
  intros Eb Hb; red in Hb.
  intros []; cbn - [Z.mul];
    length_apps; fold_toList; rewrite !Hb; red in Eb; lia.
Qed.

Instance BoundedLength_Node {T A} `{ToList T A} (b : Z)
  : NonNegative b -> BoundedLength A b -> BoundedLength (Node A) (3 * b).
Proof.
  intros Eb Hb; red in Hb.
  intros []; cbn - [Z.mul];
    length_apps; fold_toList; rewrite !Hb; red in Eb; lia.
Qed.

Lemma Z_1_le_pow (x y : Z) : 1 <= x -> 0 <= y -> 1 <= x ^ y.
Proof.
  intros. apply (Zlt_le_succ 0). apply Z.pow_pos_nonneg; lia.
Qed.

Theorem depth_length_FingerTree {T A} `{ToList T A}
  : forall (t : FingerTree A),
      forall b,
      NonNegative b ->
      BoundedLength A b ->
      (List.length (toList t) <= 11 ^ depth t * b)%Z.
Proof.
  intros t; revert H; induction t; intros H b Eb Hb.
  - cbn - [Z.mul]; red in Eb; lia.
  - cbn - [Z.mul]; red in Eb. rewrite Z.mul_1_l. apply (Hb a0).
  - cbn - [Z.add].
    length_apps.
    fold_toList.
    rewrite Z_pow_succ by apply nonnegative_depth.
    rewrite !bounded_length.
    rewrite (IHt _ (3 * b) _ _).
    red in Eb.
    assert (b <= 11 ^ depth t * b)
      by (apply Z_mul_const_l_le;
        [ assumption | apply Z_1_le_pow; [ Z_assum | apply nonnegative_depth ] ]).
    rewrite H0 at 1 3.
    replace (11 ^ depth t * (3 * b)) with (3 * (11 ^ depth t * b)) by lia.
    rewrite <- Z.mul_assoc.
    lia.
Qed.
