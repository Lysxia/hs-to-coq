Require Import GHC.Base.
Require Import Data.Sequence.Internal.
Import GHC.Num.Notations.

Definition size__Digit12 {A} `{Sized A} (d : Digit12 A) : Int :=
  match d with
  | One12 a => size a
  | Two12 a b => size a + size b
  end.

Instance Sized__Digit12 {A} `{Sized A} : Sized (Digit12 A) :=
  fun _ k => k {| size__ := size__Digit12 |}.

Definition size__Thin {A} `{Sized A} (t : Thin A) : Int :=
  match t with
  | EmptyTh => 0%Z
  | SingleTh x => size x
  | DeepTh s _ _ _ => s
  end.

Instance Sized__Thin {A} `{Sized A} : Sized (Thin A) :=
  fun _ k => k {| size__ := size__Thin |}.

Instance Sized__Rigid {A} `{Sized A} : Sized (Rigid A) :=
  fun _ k => k {| size__ := fun t =>
    match t with
    | Mk_Rigid s _ _ _ => s
    end |}.

Definition size__Seq {A} (s : Seq A) : Int :=
  match s with
  | Mk_Seq t => size t
  end.

Instance Sized__Seq {A} : Sized (Seq A) :=
  fun _ k => k {| size__ := size__Seq |}.

Definition size__ViewLTree {A} `{Sized A} (t : ViewLTree A) : Int :=
  match t with
  | ConsLTree x xs => size x + size xs
  | EmptyLTree => 0%Z
  end.

Instance Sized__ViewLTree {A} `{Sized A} : Sized (ViewLTree A) :=
  fun _ k => k {| size__ := size__ViewLTree |}.

Definition size__ViewRTree {A} `{Sized A} (t : ViewRTree A) : Int :=
  match t with
  | SnocRTree xs x => size xs + size x
  | EmptyRTree => 0%Z
  end.

Instance Sized__ViewRTree {A} `{Sized A} : Sized (ViewRTree A) :=
  fun _ k => k {| size__ := size__ViewRTree |}.

Definition size__ViewL {A} (t : ViewL A) : Int :=
  match t with
  | EmptyL => #0
  | x :< xs => (1 + size xs)%Z
  end.

Instance Sized__ViewL {A} : Sized (ViewL A) :=
  fun _ k => k {| size__ := size__ViewL |}.

Definition size__ViewR {A} (t : ViewR A) : Int :=
  match t with
  | EmptyR => #0
  | xs :> x => (size xs + 1)%Z
  end.

Instance Sized__ViewR {A} : Sized (ViewR A) :=
  fun _ k => k {| size__ := size__ViewR |}.

Definition size__Rigidified {A} `{Sized A} (t : Rigidified A) : Int :=
  match t with
  | RigidEmpty => #0
  | RigidOne a => size a
  | RigidTwo a b => size a + size b
  | RigidThree a b c => size a + size b + size c
  | RigidFull t => size t
  end.

Instance Sized__Rigidified {A} `{Sized A} : Sized (Rigidified A) :=
  fun _ k => k {| size__ := size__Rigidified |}.

Ltac fold_sized :=
  repeat (change (@Internal.Sized__FingerTree_size ?A _) with (@size (FingerTree A) _));
  repeat (change (@Internal.Sized__Digit_size ?A _) with (@size (Digit A) _));
  repeat (change (@Internal.Sized__Node_size ?A) with (@size (Node A) _));
  repeat (change (@Internal.Sized__Elem_size ?A) with (@size (Elem A) _));
  repeat (change (@size__Seq ?A) with (@size (Seq A) _));
  repeat (change (@Internal.length ?A) with (@size (Seq A) _));
  repeat (change (@size__Thin ?A) with (@size (Thin A) _));
  repeat (change (@size__ViewLTree ?A) with (@size (ViewLTree A) _));
  repeat (change (@size__ViewRTree ?A) with (@size (ViewRTree A) _)).
