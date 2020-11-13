Require Import GHC.Base.
Import ListNotations.
Require Import Data.Sequence.Internal.

Class ToList (T : Type) (A : Type) : Type :=
  toList : A -> list T.

Instance ToList__Elem {T} : ToList T (Elem T) : Type :=
  fun e =>
    match e with
    | Mk_Elem x => [x]
    end.

Instance ToList__Digit {T A} `{ToList T A} : ToList T (Digit A) : Type :=
  fun d =>
    match d with
    | One   w => toList w
    | Two   w x => toList w ++ toList x
    | Three w x y => toList w ++ toList x ++ toList y
    | Four  w x y z => toList w ++ toList x ++ toList y ++ toList z
    end.

Instance ToList__Node {T A} `{ToList T A} : ToList T (Node A) :=
  fun t =>
    match t with
    | Node2 _s x y => toList x ++ toList y
    | Node3 _s x y z => toList x ++ toList y ++ toList z
    end.

Fixpoint toList__FingerTree {T A} `{ToList T A} (t : FingerTree A) : list T :=
  match t with
  | EmptyT => []
  | Single x => toList x
  | Deep _s pr m sf => toList pr ++ toList__FingerTree m ++ toList sf
  end.

Instance ToList__FingerTree {T A} `{ToList T A} : ToList T (FingerTree A) :=
  toList__FingerTree.

Instance ToList__Seq {T} : ToList T (Seq T) :=
  fun z =>
    match z with
    | Mk_Seq t => toList t
    end.

Instance ToList__Digit12 {T A} `{ToList T A} : ToList T (Digit12 A) :=
  fun d =>
    match d with
    | One12 a => toList a
    | Two12 a b => toList a ++ toList b
    end.

Fixpoint toList_Thin {T A} `{ToList T A} (t : Thin A) : list T :=
  match t with
  | EmptyTh => []
  | SingleTh a => toList a
  | DeepTh _s pr m sf => toList pr ++ toList_Thin m ++ toList sf
  end.

Instance ToList__Thin {T A} `{ToList T A} : ToList T (Thin A) := toList_Thin.

Ltac fold_toList :=
  repeat (change (@toList__FingerTree ?T ?A _) with (@toList T (FingerTree A) _)).
