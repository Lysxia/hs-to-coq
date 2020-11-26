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
Require Import SequenceProofs.Validity.
Require Import SequenceProofs.ValidityFunction.
Require Import SequenceProofs.Applicative_Internal.
Require Import SequenceProofs.Applicative_aptyMiddle.

Local Open Scope Z_scope.

Opaque aptyMiddle.

Ltac auto_valid := fold_classes; auto_valid_.

Definition valid_with_size {A} `{Sized A} `{Validity A} (n : Int) : A -> Prop :=
  fun a => valid a /\ size a = n.

Definition midsize {A} `{Sized A} (t : Rigid A) : Int :=
  match t with
  | Mk_Rigid _ _ m _ => size m
  end.

Lemma FMultSizedValid_ElemToNode2 {A B C} `{Sized B} `{Validity B} `{Sized C} `{Validity C}
    (s : Int) (map23 : A -> B -> C)
    (pr sf : Digit23 B)
  : s = size pr + size sf ->
    (forall a, FSizedValid (map23 a)) ->
    valid pr -> valid sf ->
    FMultSizedValid s
      (fun '(Mk_Elem f) =>
         Node2 (size pr + size sf) (fmap (map23 f) pr) (fmap (map23 f) sf)).
Proof.
  split; intros []; cbn; fold_classes.
  - subst s; cbn; clear; lia.
  - intros _.
    split.
    + rewrite 2 size_fmap__Node; auto.
    + split; apply valid_fmap__Node; auto.
Qed.

Lemma FMultSizedValid_ElemToNode3 {A B C} `{Sized B} `{Validity B} `{Sized C} `{Validity C}
    (s : Int) (map23 : A -> B -> C)
    (pr sf n : Digit23 B)
  : s = size pr + size n + size sf ->
    (forall a, FSizedValid (map23 a)) ->
    valid pr -> valid sf -> valid n ->
    FMultSizedValid s
      (fun '(Mk_Elem f) =>
         Node3 (size pr + size n + size sf)
           (fmap (map23 f) pr)
           (fmap (map23 f) n)
           (fmap (map23 f) sf)).
Proof.
  split; intros []; cbn; fold_classes.
  * subst s; cbn; clear; lia.
  * intros _.
    split; [ | auto_valid ].
    rewrite 3 size_fmap__Node; auto.
Qed.

Section aptyMiddle.

Context {B C A : Type}
  `{SizedB : Sized B} `{ValidityB : Validity B} `{SizedC : Sized C} `{ValidityC : Validity C}
  (firstf : B -> C) (lastf : B -> C) (map23 : A -> B -> C)
  (ta : FingerTree (Elem A)) (tb : Rigid B)
  (Hfirstf : FSizedValid firstf)
  (Hlastf : FSizedValid lastf)
  (Hmap23 : forall a, FSizedValid (map23 a))
  (Hta : valid ta)
  (Htb : valid tb).

Opaque aptyMiddle.

Theorem valid_with_size_aptyMiddle
  : valid_with_size
      (midsize tb + size tb + size ta * size tb)
      (aptyMiddle firstf lastf map23 ta tb).
Proof.
  revert_until tb. revert SizedB ValidityB SizedC ValidityC.
  apply aptyMiddle_ind; clear; intros B C A firstf lastf map23 ta tb IH; intros.
  rewrite unfold_aptyMiddle.
  destruct tb as [ s pr m sf ]; decompose_conj Htb.
  destruct m as [ | | sm prm mm sfm ].
  + red; cbn.
    pose proof (FMultSizedValid_ElemToNode2 s map23 pr sf) as MMF.
    prove_assumptions_of MMF; try solve [ auto | subst; clear; cbn; lia ].
    split.
    * auto_valid.
      apply valid_mapMulFT; auto.
    * fold_classes. rewrite 2 size_fmap__Node; auto_valid.
      rewrite size_mapMulFT; auto.
      subst; clear; cbn; lia.
  + red; cbn.
    pose proof (FMultSizedValid_ElemToNode3 s map23 pr sf) as MMF.
    prove_assumptions_of MMF; auto.
    split.
    * auto_valid.
      apply valid_mapMulFT; auto.
    * fold_classes. rewrite !size_fmap__Node; auto_valid.
      rewrite size_mapMulFT; auto.
      subst; clear; cbn; lia.
  + match goal with
    | [ H : valid__Thin (DeepTh _ _ _ _) |- _ ] => decompose_conj H
    end.
    specialize (IH _ _ _ (fmap firstf) (fmap lastf) (fmap GHC.Base.∘ map23) ta (Mk_Rigid s (squashL pr prm) mm (squashR sfm sf)) eq_refl _ _ _ _).
    prove_assumptions_of IH; auto_valid.
      { cbn. fold_classes.
        split.
        { rewrite size_squashL, size_squashR.
          subst; cbn; lia. }
        { auto using @valid_squashL, @valid_squashR. } }
    destruct IH as [ IHvalid IHsize ].
    split.
    * cbn. auto_valid.
      { rewrite IHsize. cbn. fold_classes. rewrite 2 size_digit12ToDigit by auto.
        subst s sm; cbn; lia.  }
    * cbn. lia.
Qed.

Lemma size_aptyMiddle
  : size (aptyMiddle firstf lastf map23 ta tb) =
    midsize tb + size tb + size ta * size tb.
Proof. apply valid_with_size_aptyMiddle. Qed.

Lemma valid_aptyMiddle : valid (aptyMiddle firstf lastf map23 ta tb).
Proof. apply valid_with_size_aptyMiddle. Qed.

End aptyMiddle.

Section liftA2.

Context {A B C : Type}.

Theorem valid_liftA2 (f : A -> B -> C) (ta : Seq A) (tb : Seq B)
  : valid ta -> valid tb -> valid (liftA2 f ta tb).
Proof.
  intros Hta Htb.
  cbv [liftA2 Applicative__Seq Data.Sequence.Internal.Applicative__Seq_liftA2 liftA2__ liftA2Seq].
  destruct tb as [tb].
  pose proof (valid_viewl ta Hta) as HtaL.
  pose proof (size_viewl ta) as Sta; prove_assumptions_of Sta; auto.
  destruct (viewl ta) as [ | a ta' ]; [ constructor | ].
  pose proof (valid_viewr ta' HtaL) as HtaLR.
  pose proof (size_viewr ta') as Sta'; prove_assumptions_of Sta'; auto.
  destruct (viewr ta') as [ | ta'' a'].
  { apply valid_fmap__Seq; assumption. }
  destruct ta'' as [ta''].
  pose proof (valid_rigidify tb Htb) as Htbr.
  pose proof (size_rigidify tb) as Stb.
  destruct (rigidify tb) as [ | [r1] | [r1] [r2] | [r1] [r2] [r3] | [s pr m sf] ].
  - constructor.
  - apply valid_fmap__Seq; auto.
  - apply valid_lift2FT; auto.
  - apply valid_lift3FT; auto.
  - decompose_conj Htbr. cbn; auto_valid.
    + rewrite 2 size_fmap__Digit, 2 size_nodeToDigit; auto_valid.
      rewrite size_aptyMiddle; auto_valid.
      * revert Sta Sta' H; cbn - [Z.add]; fold_classes.
        intros [] [] ->. lia.
      * cbn; fold_classes; auto.
    + fold_valid; apply valid_aptyMiddle; auto_valid.
      cbn; fold_classes; auto.
Qed.

End liftA2.
