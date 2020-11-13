Require Import GHC.Base.
Require Import Data.Sequence.Internal.

Definition Sized__Dict__Digit12 {A} `{Sized A} : Sized__Dict (Digit12 A) :=
  {| size__ := fun d =>
    match d with
    | One12 a => size a
    | Two12 a b => size a + size b
    end
  |}.

Instance Sized__Digit12 {A} `{Sized A} : Sized (Digit12 A) :=
  fun _ k => k Sized__Dict__Digit12.

Definition size_Thin {A} `{Sized A} (t : Thin A) : Int :=
  match t with
  | EmptyTh => 0%Z
  | SingleTh x => size x
  | DeepTh s _ _ _ => s
  end.

Instance Sized__Thin {A} `{Sized A} : Sized (Thin A) :=
  fun _ k => k {| size__ := size_Thin |}.

Instance Sized__Rigid {A} `{Sized A} : Sized (Rigid A) :=
  fun _ k => k {| size__ := fun t =>
    match t with
    | Mk_Rigid s _ _ _ => s
    end |}.

