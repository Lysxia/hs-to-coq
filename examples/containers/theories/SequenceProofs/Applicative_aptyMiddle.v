From Coq Require Import
  Lia ZArith Morphisms Program.Tactics.

Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Proofs.Data.Foldable.
Import GHC.Num.Notations.
Require Import CustomTactics.

Require Import Data.Sequence.Internal.
Require Import SequenceProofs.Validity.
Require Import SequenceProofs.ValidityFunction.
Require Import SequenceProofs.Applicative_Internal.

Local Open Scope Z_scope.

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
      (fun pat : Elem A =>
       (let
        'Mk_Elem f as anonymous' := pat
         return (anonymous' = pat -> Node (Digit23 C)) in
         fun _ : Mk_Elem f = pat =>
         Node2 (size pr + size sf)
           (fmap (map23 f) pr) (fmap (map23 f) sf)) eq_refl).
Proof.
  split; intros []; cbn.
  * subst s; cbn; clear; lia.
  * intros _.
    split.
    { change _ with (size pr + size sf = size (fmap (map23 getElem) pr) + size (fmap (map23 getElem) sf)).
      rewrite 2 size_fmap__Node; auto. }
    { split; apply valid_fmap__Node; auto. }
Qed.

Lemma FMultSizedValid_ElemToNode3 {A B C} `{Sized B} `{Validity B} `{Sized C} `{Validity C}
    (s : Int) (map23 : A -> B -> C)
    (pr sf n : Digit23 B)
  : s = size pr + size n + size sf ->
    (forall a, FSizedValid (map23 a)) ->
    valid pr -> valid sf -> valid n ->
    FMultSizedValid s
      (fun pat : Elem A =>
       (let
        'Mk_Elem f as anonymous' := pat
         return (anonymous' = pat -> Node (Digit23 C)) in
         fun _ : Mk_Elem f = pat =>
         Node3 (size pr + size n + size sf)
           (fmap (map23 f) pr) (fmap (map23 f) n) (fmap (map23 f) sf)) eq_refl).
Proof.
  split; intros []; cbn.
  * subst s; cbn; clear; lia.
  * intros _.
    split; [ | auto_valid ].
    change _ with (size pr + size n + size sf
      = size (fmap (map23 getElem) pr) + size (fmap (map23 getElem) n) + size (fmap (map23 getElem) sf)).
    rewrite 3 size_fmap__Node; auto.
Qed.

Local Notation ap8 P F x1 x2 x3 x4 x5 x6 x7 x8 :=
  (P x1 x2 x3 x4 x5 x6 x7 x8 (F x1 x2 x3 x4 x5 x6 x7 x8)).

Theorem aptyMiddle_ind
  (P : forall B C A (firstf lastf : B -> C) (map23 : A -> B -> C)
         (ta : FingerTree (Elem A)) (tb : Rigid B) (r : FingerTree (Node C)), Prop)
  (HYP : forall B C A (firstf lastf : B -> C) (map23 : A -> B -> C)
             (ta : FingerTree (Elem A)) (tb : Rigid B),
           (forall B0 C0 A0 firstf0 lastf0 map230 ta0 tb0,
             (S (depth_Rigid tb0) = depth_Rigid tb)%nat ->
             ap8 P (@aptyMiddle) B0 C0 A0 firstf0 lastf0 map230 ta0 tb0) ->
           ap8 P (@aptyMiddle) B C A firstf lastf map23 ta tb)
  : forall B C A (firstf lastf : B -> C) (map23 : A -> B -> C)
        (ta : FingerTree (Elem A)) (tb : Rigid B),
    ap8 P (@aptyMiddle) B C A firstf lastf map23 ta tb.
Proof.
  intros B C A firstf lastf map23 ta tb.
  remember (depth_Rigid tb) as n eqn:Eqn.
  revert B C A firstf lastf map23 ta tb Eqn.
  induction n; intros; apply HYP.
  - rewrite <- Eqn; discriminate.
  - rewrite <- Eqn; intros; apply IHn, eq_add_S; auto.
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

Theorem valid_with_size_aptyMiddle
  : valid_with_size
      (midsize tb + size tb + size ta * size tb)
      (aptyMiddle firstf lastf map23 ta tb).
Proof.
  revert_until tb. revert SizedB ValidityB SizedC ValidityC.
  apply aptyMiddle_ind; clear; intros B C A firstf lastf map23 ta tb IH; intros.
  unfold aptyMiddle.
  cbv beta iota delta [ aptyMiddle_func ].
  rewrite Wf.Fix_eq.
  { cbn beta iota delta [projT1 projT2].
    match goal with
    | [ |- valid_with_size _ ?T ] => let U := eval hnf in T in change T with U
    end.
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
      change (Wf.Fix_sub _ _ _ _ _ _) with
        (aptyMiddle (fmap firstf) (fmap lastf) (fmap GHC.Base.∘ map23) ta
           (Mk_Rigid s (squashL pr prm) mm (squashR sfm sf))).
      remember @aptyMiddle as aptyMiddle_ eqn:EAM; clear EAM.
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
  }
  { intros x f g Efg. destruct x as (? & ? & ? & ? & ? & ? & ? & ?).
    cbn beta iota delta [projT1 projT2].
    match goal with
    | [ |- ?T = ?U ] =>
      let T' := eval hnf in T in change T with T';
      let U' := eval hnf in U in change U with U'
    end.
    destruct r.
    destruct t.
    all: try reflexivity.
    f_equal.
    apply Efg.
  }
Time Qed.

Lemma size_aptyMiddle
  : size (aptyMiddle firstf lastf map23 ta tb) =
    midsize tb + size tb + size ta * size tb.
Proof. apply valid_with_size_aptyMiddle. Qed.

Lemma valid_aptyMiddle : valid (aptyMiddle firstf lastf map23 ta tb).
Proof. apply valid_with_size_aptyMiddle. Qed.

End aptyMiddle.
