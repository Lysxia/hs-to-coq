From Coq Require Import
  Lia ZArith Morphisms Program.Tactics.

Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Proofs.Data.Foldable.
Import GHC.Num.Notations.
Require Import CustomTactics.

Require Import Data.Sequence.Internal.

Local Open Scope Z_scope.

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

Lemma mapMulFT_ext {a b} (i : Int) (f g : a -> b) (t : FingerTree a)
  : (forall x, f x = g x) ->
    mapMulFT i f t = mapMulFT i g t.
Proof.
  revert b f g; induction t as [ | | a s dl m IH dr ]; intros * H; cbn.
  - reflexivity.
  - rewrite H; reflexivity.
  - f_equal.
    + destruct dl; cbn; f_equal; apply H.
    + apply IH. intros []; cbn; f_equal; apply H.
    + destruct dr; cbn; f_equal; apply H.
Qed.

Lemma unfold_aptyMiddle {b c a} (firstf lastf : (b -> c)) (map23 : a -> b -> c)
    (fs : FingerTree (Elem a)) (tb : Rigid b)
  : aptyMiddle firstf lastf map23 fs tb
  = match tb with
    | Mk_Rigid s pr (DeepTh sm prm mm sfm) sf =>
      Deep (sm + (s * (size fs + #1)))
        (fmap (fmap firstf) (digit12ToDigit prm))
        (aptyMiddle (fmap firstf) (fmap lastf) (fmap GHC.Base.∘ map23) fs
           (Mk_Rigid s (squashL pr prm) mm (squashR sfm sf)))
        (fmap (fmap lastf) (digit12ToDigit sfm))
    | Mk_Rigid s pr EmptyTh sf =>
      let converted := node2 pr sf in
      deep (One (fmap firstf sf))
        (mapMulFT s (fun '(Mk_Elem f) => fmap (fmap (map23 f)) converted) fs)
        (One (fmap lastf pr))
    | Mk_Rigid s pr (SingleTh q) sf =>
      let converted := node3 pr q sf in
      deep (Two (fmap firstf q) (fmap firstf sf))
        (mapMulFT s (fun '(Mk_Elem f) => fmap (fmap (map23 f)) converted) fs)
        (Two (fmap lastf pr) (fmap lastf q))
    end.
Proof.
  match goal with
  | [ |- ?X = ?Y ] => pose (RHS := Y); change Y with RHS
  end.
  cbv beta iota delta [ aptyMiddle aptyMiddle_func ].
  rewrite Wf.Fix_eq.
  { cbn beta iota delta [projT1 projT2].
    match goal with
    | [ |- ?X = _ ] => let U := eval hnf in X in change X with U
    end.
    destruct tb as [ s pr m sf ].
    destruct m as [ | | sm prm mm sfm ].
    - subst RHS; cbn. f_equal. apply mapMulFT_ext.
      intros []; reflexivity.
    - subst RHS; cbn. f_equal. apply mapMulFT_ext.
      intros []; reflexivity.
    - subst RHS. reflexivity.
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
