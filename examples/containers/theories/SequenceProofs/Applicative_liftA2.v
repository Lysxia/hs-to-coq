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
Require Import SequenceProofs.Applicative_Internal.
Require Import SequenceProofs.Applicative_aptyMiddle.

Opaque aptyMiddle.

Ltac auto_valid := fold_classes; auto_valid_.

Section liftA2.

Context {A B C : Type}.

Theorem valid_liftA2 (f : A -> B -> C) (ta : Seq A) (tb : Seq B)
  : valid ta -> valid tb -> valid (liftA2 f ta tb).
Proof.
  intros Hta Htb.
  cbv [liftA2 Applicative__Seq Data.Sequence.Internal.Applicative__Seq_liftA2 liftA2__ liftA2Seq].
  destruct tb as [tb].
  pose proof (valid_viewl ta Hta) as HtaL.
  destruct (viewl ta) as [ | a ta' ]; [ constructor | ].
  pose proof (valid_viewr ta' HtaL) as HtaLR.
  destruct (viewr ta') as [ | ta'' a'].
  { apply valid_fmap__Seq; assumption. }
  destruct ta'' as [ta''].
  pose proof (valid_rigidify tb Htb) as Htbr.
  destruct (rigidify tb) as [ | [r1] | [r1] [r2] | [r1] [r2] [r3] | [s pr m sf] ].
  - constructor.
  - apply valid_fmap__Seq; auto.
  - apply valid_lift2FT; auto.
  - apply valid_lift3FT; auto.
  - decompose_conj Htbr. cbn; auto_valid.
    + rewrite 2 size_fmap__Digit, 2 size_nodeToDigit; auto_valid.
      rewrite size_aptyMiddle; auto_valid.
      * cbn; fold_classes. admit.
      * cbn; fold_classes; auto.
    + fold_valid; apply valid_aptyMiddle; auto_valid.
      cbn; fold_classes; auto.
Admitted.

End liftA2.
