From Coq Require Import ZArith.

Require Import GHC.Base.
Require Import Proofs.Data.Foldable.
Import ListNotations.
Require Import Data.Sequence.Internal.
Require Import SequenceProofs.Sized.
Require Import CustomTactics.

Local Open Scope Z_scope.

(* A precondition to most functions is that all size annotations are
   correct. *)
Class Validity (A : Type) : Type :=
  valid : A -> Prop.

Instance Validity__Elem {A} : Validity (Elem A) :=
  fun _ => True.

Instance Validity__Digit {A} `{Validity A} : Validity (Digit A) :=
  fun d =>
    match d with
    | One   w => valid w
    | Two   w x => valid w /\ valid x
    | Three w x y => valid w /\ valid x /\ valid y
    | Four  w x y z => valid w /\ valid x /\ valid y /\ valid z
    end.

Instance Validity__Node {A} `{Validity A} `{Sized A} : Validity (Node A) :=
  fun t =>
    match t with
    | Node2 s x y => s = size x + size y /\ valid x /\ valid y
    | Node3 s x y z => s = size x + size y + size z /\ valid x /\ valid y /\ valid z
    end.

Fixpoint valid__FingerTree {A} `{Validity A} `{Sized A} (t : FingerTree A) : Prop :=
  match t with
  | EmptyT => True
  | Single x => valid x
  | Deep s pr m sf =>
    s = size pr + size m + size sf /\ valid pr /\ valid__FingerTree m /\ valid sf
  end.

Instance Validity__FingerTree {A} `{Validity A} `{Sized A} : Validity (FingerTree A) :=
  valid__FingerTree.

Instance Validity__Seq {A} : Validity (Seq A) :=
  fun z =>
    match z with
    | Mk_Seq t => valid t
    end.

Instance Validity__Digit12 {A} `{Validity A} : Validity (Digit12 A) :=
  fun d =>
    match d with
    | One12 a => valid a
    | Two12 a b => valid a /\ valid b
    end.

Fixpoint valid__Thin {A} `{Sized A} `{Validity A} (t : Thin A) : Prop :=
  match t with
  | EmptyTh => True
  | SingleTh x => valid x
  | DeepTh s pr m sf =>
    s = size pr + size m + size sf /\ valid pr /\ valid__Thin m /\ valid sf
  end.

Instance Validity__Thin {A} `{Sized A} `{Validity A} : Validity (Thin A) :=
  valid__Thin.

Instance Validity__Rigid {A} `{Sized A} `{Validity A} : Validity (Rigid A) :=
  fun t =>
    match t with
    | Mk_Rigid s pr m sf =>
      s = size pr + size m + size sf /\ valid pr /\ valid m /\ valid sf
    end.

Instance Validity__ViewLTree {A} `{Sized A} `{Validity A} : Validity (ViewLTree A) :=
  fun v =>
    match v with
    | ConsLTree x xs => valid x /\ valid xs
    | EmptyLTree => True
    end.

Instance Validity__ViewRTree {A} `{Sized A} `{Validity A} : Validity (ViewRTree A) :=
  fun v =>
    match v with
    | SnocRTree xs x => valid xs /\ valid x
    | EmptyRTree => True
    end.

Instance Validity__ViewL {A} : Validity (ViewL A) :=
  fun v =>
    match v with
    | EmptyL => True
    | _x :< xs => valid xs
    end.

Instance Validity__ViewR {A} : Validity (ViewR A) :=
  fun v =>
    match v with
    | EmptyR => True
    | xs :> _x => valid xs
    end.

Instance Validity__Rigidified {A} `{Sized A} `{Validity A} : Validity (Rigidified A) :=
  fun r =>
    match r with
    | RigidEmpty => True
    | RigidOne a => valid a
    | RigidTwo a b => valid a /\ valid b
    | RigidThree a b c => valid a /\ valid b /\ valid c
    | RigidFull t => valid t
    end.

Ltac fold_valid :=
  change (@valid__FingerTree ?A _ _) with (@valid (FingerTree A) _);
  change (@valid__Thin ?A _ _) with (@valid (Thin A) _).

Ltac intros_valid :=
  let H := fresh "H" in
  intros H; decompose_conj H.

Ltac length_apps :=
  try (repeat change (List.lenAcc ?l 0%Z) with (List.length l));
  repeat (rewrite List.length_app);
  repeat (rewrite Z.add_assoc).
