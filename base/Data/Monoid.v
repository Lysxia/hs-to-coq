(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(** This should not be here. Ideally, [GHC.Base] should automatically export
    [GHC.Maybe], but we cannot do that because [GHC.Maybe] depends on
    [GHC.Base]. *)
Require GHC.Maybe.

(* Converted imports: *)

Require Control.Monad.Fail.
Require GHC.Base.
Require GHC.Prim.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Last a : Type := | Mk_Last (getLast : option a) : Last a.

Inductive First a : Type := | Mk_First (getFirst : option a) : First a.

Inductive Ap {k : Type} (f : k -> Type) (a : k) : Type :=
  | Mk_Ap (getAp : f a) : Ap f a.

Arguments Mk_Last {_} _.

Arguments Mk_First {_} _.

Arguments Mk_Ap {_} {_} {_} _.

Definition getLast {a} (arg_0__ : Last a) :=
  let 'Mk_Last getLast := arg_0__ in
  getLast.

Definition getFirst {a} (arg_0__ : First a) :=
  let 'Mk_First getFirst := arg_0__ in
  getFirst.

Definition getAp {k : Type} {f : k -> Type} {a : k} (arg_0__ : Ap f a) :=
  let 'Mk_Ap getAp := arg_0__ in
  getAp.

(* Converted value declarations: *)

Instance Unpeel_First a : GHC.Prim.Unpeel (First a) (option a) :=
  GHC.Prim.Build_Unpeel _ _ getFirst Mk_First.

Local Definition Eq___First_op_zeze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___First_op_zsze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___First {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___First_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___First_op_zsze__ |}.

Local Definition Ord__First_op_zl__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__First_op_zlze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__First_op_zg__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__First_op_zgze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__First_compare {inst_a : Type} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__First_max {inst_a : Type} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__First_min {inst_a : Type} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__First {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Ord (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__First_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__First_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__First_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__First_op_zgze__ ;
           GHC.Base.compare__ := Ord__First_compare ;
           GHC.Base.max__ := Ord__First_max ;
           GHC.Base.min__ := Ord__First_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Monoid.Read__First' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Monoid.Show__First' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Monoid.Generic__First' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Monoid.Generic1__TYPE__First__LiftedRep' *)

Local Definition Functor__First_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> First a -> First b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__First_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> First b -> First a :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__First : GHC.Base.Functor First :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__First_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__First_op_zlzd__ |}.

Local Definition Applicative__First_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> First a -> First b -> First c :=
  fun {a : Type} {b : Type} {c : Type} => GHC.Prim.coerce GHC.Base.liftA2.

Local Definition Applicative__First_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, First (a -> b) -> First a -> First b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.<*>_.

Local Definition Applicative__First_op_ztzg__
   : forall {a : Type}, forall {b : Type}, First a -> First b -> First b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.*>_.

Local Definition Applicative__First_pure : forall {a : Type}, a -> First a :=
  fun {a : Type} => GHC.Prim.coerce GHC.Base.pure.

Program Instance Applicative__First : GHC.Base.Applicative First :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__First_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__First_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__First_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__First_pure |}.

Local Definition Monad__First_op_zgzg__
   : forall {a : Type}, forall {b : Type}, First a -> First b -> First b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__First_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, First a -> (a -> First b) -> First b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__First_return_ : forall {a : Type}, a -> First a :=
  fun {a : Type} => GHC.Prim.coerce GHC.Base.return_.

Program Instance Monad__First : GHC.Base.Monad First :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__First_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} =>
             Monad__First_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__First_return_ |}.

Instance Unpeel_Last a : GHC.Prim.Unpeel (Last a) (option a) :=
  GHC.Prim.Build_Unpeel _ _ getLast Mk_Last.

Local Definition Eq___Last_op_zeze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Last_op_zsze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Last {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Last_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Last_op_zsze__ |}.

Local Definition Ord__Last_op_zl__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Last_op_zlze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Last_op_zg__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Last_op_zgze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Last_compare {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Last_max {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Last_min {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Last {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Last_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Last_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Last_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Last_op_zgze__ ;
           GHC.Base.compare__ := Ord__Last_compare ;
           GHC.Base.max__ := Ord__Last_max ;
           GHC.Base.min__ := Ord__Last_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Monoid.Read__Last' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Monoid.Show__Last' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Monoid.Generic__Last' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Monoid.Generic1__TYPE__Last__LiftedRep' *)

Local Definition Functor__Last_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Last a -> Last b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__Last_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Last b -> Last a :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__Last : GHC.Base.Functor Last :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Last_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Last_op_zlzd__ |}.

Local Definition Applicative__Last_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Last a -> Last b -> Last c :=
  fun {a : Type} {b : Type} {c : Type} => GHC.Prim.coerce GHC.Base.liftA2.

Local Definition Applicative__Last_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Last (a -> b) -> Last a -> Last b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.<*>_.

Local Definition Applicative__Last_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Last a -> Last b -> Last b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.*>_.

Local Definition Applicative__Last_pure : forall {a : Type}, a -> Last a :=
  fun {a : Type} => GHC.Prim.coerce GHC.Base.pure.

Program Instance Applicative__Last : GHC.Base.Applicative Last :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Last_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Last_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Last_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Last_pure |}.

Local Definition Monad__Last_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Last a -> Last b -> Last b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__Last_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Last a -> (a -> Last b) -> Last b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__Last_return_ : forall {a : Type}, a -> Last a :=
  fun {a : Type} => GHC.Prim.coerce GHC.Base.return_.

Program Instance Monad__Last : GHC.Base.Monad Last :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__Last_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} => Monad__Last_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__Last_return_ |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.Monoid.Alternative__Ap' *)

Instance Unpeel_Ap k (f : k -> Type) a : GHC.Prim.Unpeel (Ap f a) (f a) :=
  GHC.Prim.Build_Unpeel _ _ getAp Mk_Ap.

Local Definition Applicative__Ap_liftA2 {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Ap inst_f a -> Ap inst_f b -> Ap inst_f c :=
  fun {a : Type} {b : Type} {c : Type} => GHC.Prim.coerce GHC.Base.liftA2.

Local Definition Applicative__Ap_op_zlztzg__ {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type},
     forall {b : Type}, Ap inst_f (a -> b) -> Ap inst_f a -> Ap inst_f b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.<*>_.

Local Definition Applicative__Ap_op_ztzg__ {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type},
     forall {b : Type}, Ap inst_f a -> Ap inst_f b -> Ap inst_f b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.*>_.

Local Definition Applicative__Ap_pure {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type}, a -> Ap inst_f a :=
  fun {a : Type} => GHC.Prim.coerce GHC.Base.pure.

Local Definition Functor__Ap_fmap {inst_f : Type -> Type} `{GHC.Base.Functor
  inst_f}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Ap inst_f a -> Ap inst_f b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__Ap_op_zlzd__ {inst_f : Type -> Type}
  `{GHC.Base.Functor inst_f}
   : forall {a : Type}, forall {b : Type}, a -> Ap inst_f b -> Ap inst_f a :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__Ap {f : Type -> Type} `{GHC.Base.Functor f}
   : GHC.Base.Functor (Ap f) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Ap_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Ap_op_zlzd__ |}.

Program Instance Applicative__Ap {f : Type -> Type} `{GHC.Base.Applicative f}
   : GHC.Base.Applicative (Ap f) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Ap_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Ap_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} => Applicative__Ap_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Ap_pure |}.

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Monoid.Enum__Ap' *)

Local Definition Eq___Ap_op_zeze__ {inst_k : Type} {inst_f : inst_k -> Type}
  {inst_a : inst_k} `{GHC.Base.Eq_ (inst_f inst_a)}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Ap_op_zsze__ {inst_k : Type} {inst_f : inst_k -> Type}
  {inst_a : inst_k} `{GHC.Base.Eq_ (inst_f inst_a)}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Ap {k : Type} {f : k -> Type} {a : k} `{GHC.Base.Eq_ (f
                                                                            a)}
   : GHC.Base.Eq_ (Ap f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Ap_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Ap_op_zsze__ |}.

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Monoid.Generic__Ap' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Monoid.Generic1__Ap__5' *)

Local Definition Monad__Ap_op_zgzg__ {inst_f : Type -> Type} `{GHC.Base.Monad
  inst_f}
   : forall {a : Type},
     forall {b : Type}, Ap inst_f a -> Ap inst_f b -> Ap inst_f b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__Ap_op_zgzgze__ {inst_f : Type -> Type} `{GHC.Base.Monad
  inst_f}
   : forall {a : Type},
     forall {b : Type}, Ap inst_f a -> (a -> Ap inst_f b) -> Ap inst_f b :=
  fun {a : Type} {b : Type} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__Ap_return_ {inst_f : Type -> Type} `{GHC.Base.Monad
  inst_f}
   : forall {a : Type}, a -> Ap inst_f a :=
  fun {a : Type} => GHC.Prim.coerce GHC.Base.return_.

Program Instance Monad__Ap {f : Type -> Type} `{GHC.Base.Monad f}
   : GHC.Base.Monad (Ap f) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__Ap_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} => Monad__Ap_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__Ap_return_ |}.

Local Definition MonadFail__Ap_fail {inst_f : Type -> Type}
  `{Control.Monad.Fail.MonadFail inst_f}
   : forall {a : Type}, GHC.Base.String -> Ap inst_f a :=
  fun {a : Type} => GHC.Prim.coerce Control.Monad.Fail.fail.

Program Instance MonadFail__Ap {f : Type -> Type} `{Control.Monad.Fail.MonadFail
  f}
   : Control.Monad.Fail.MonadFail (Ap f) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun {a : Type} => MonadFail__Ap_fail |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Data.Monoid.MonadPlus__Ap' *)

Local Definition Ord__Ap_op_zl__ {inst_k : Type} {inst_f : inst_k -> Type}
  {inst_a : inst_k} `{GHC.Base.Ord (inst_f inst_a)}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Ap_op_zlze__ {inst_k : Type} {inst_f : inst_k -> Type}
  {inst_a : inst_k} `{GHC.Base.Ord (inst_f inst_a)}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Ap_op_zg__ {inst_k : Type} {inst_f : inst_k -> Type}
  {inst_a : inst_k} `{GHC.Base.Ord (inst_f inst_a)}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Ap_op_zgze__ {inst_k : Type} {inst_f : inst_k -> Type}
  {inst_a : inst_k} `{GHC.Base.Ord (inst_f inst_a)}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Ap_compare {inst_k : Type} {inst_f : inst_k -> Type}
  {inst_a : inst_k} `{GHC.Base.Ord (inst_f inst_a)}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Ap_max {inst_k : Type} {inst_f : inst_k -> Type} {inst_a
   : inst_k} `{GHC.Base.Ord (inst_f inst_a)}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> Ap inst_f inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Ap_min {inst_k : Type} {inst_f : inst_k -> Type} {inst_a
   : inst_k} `{GHC.Base.Ord (inst_f inst_a)}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> Ap inst_f inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Ap {k : Type} {f : k -> Type} {a : k} `{GHC.Base.Ord (f
                                                                            a)}
   : GHC.Base.Ord (Ap f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Ap_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Ap_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Ap_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Ap_op_zgze__ ;
           GHC.Base.compare__ := Ord__Ap_compare ;
           GHC.Base.max__ := Ord__Ap_max ;
           GHC.Base.min__ := Ord__Ap_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Monoid.Read__Ap' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Monoid.Show__Ap' *)

Local Definition Semigroup__First_op_zlzlzgzg__ {inst_a : Type}
   : First inst_a -> First inst_a -> First inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_First None, b => b
    | a, _ => a
    end.

Program Instance Semigroup__First {a : Type} : GHC.Base.Semigroup (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__First_op_zlzlzgzg__ |}.

Local Definition Monoid__First_mappend {inst_a : Type}
   : First inst_a -> First inst_a -> First inst_a :=
  _GHC.Base.<<>>_.

Local Definition Monoid__First_mempty {inst_a : Type} : First inst_a :=
  Mk_First None.

Local Definition Monoid__First_mconcat {inst_a : Type}
   : list (First inst_a) -> First inst_a :=
  GHC.Base.foldr Monoid__First_mappend Monoid__First_mempty.

Program Instance Monoid__First {a : Type} : GHC.Base.Monoid (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__First_mappend ;
           GHC.Base.mconcat__ := Monoid__First_mconcat ;
           GHC.Base.mempty__ := Monoid__First_mempty |}.

Local Definition Semigroup__Last_op_zlzlzgzg__ {inst_a : Type}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_Last None => a
    | _, b => b
    end.

Program Instance Semigroup__Last {a : Type} : GHC.Base.Semigroup (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Last_op_zlzlzgzg__ |}.

Local Definition Monoid__Last_mappend {inst_a : Type}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Last_mempty {inst_a : Type} : Last inst_a :=
  Mk_Last None.

Local Definition Monoid__Last_mconcat {inst_a : Type}
   : list (Last inst_a) -> Last inst_a :=
  GHC.Base.foldr Monoid__Last_mappend Monoid__Last_mempty.

Program Instance Monoid__Last {a : Type} : GHC.Base.Monoid (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Last_mappend ;
           GHC.Base.mconcat__ := Monoid__Last_mconcat ;
           GHC.Base.mempty__ := Monoid__Last_mempty |}.

Local Definition Semigroup__Ap_op_zlzlzgzg__ {inst_f : Type -> Type} {inst_a
   : Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Semigroup inst_a}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> Ap inst_f inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Ap x, Mk_Ap y => Mk_Ap (GHC.Base.liftA2 _GHC.Base.<<>>_ x y)
    end.

Program Instance Semigroup__Ap {f : Type -> Type} {a : Type}
  `{GHC.Base.Applicative f} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Ap f a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Ap_op_zlzlzgzg__ |}.

Local Definition Monoid__Ap_mappend {inst_f : Type -> Type} {inst_a : Type}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monoid inst_a}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> Ap inst_f inst_a :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Ap_mempty {inst_f : Type -> Type} {inst_a : Type}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monoid inst_a}
   : Ap inst_f inst_a :=
  Mk_Ap (GHC.Base.pure GHC.Base.mempty).

Local Definition Monoid__Ap_mconcat {inst_f : Type -> Type} {inst_a : Type}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monoid inst_a}
   : list (Ap inst_f inst_a) -> Ap inst_f inst_a :=
  GHC.Base.foldr Monoid__Ap_mappend Monoid__Ap_mempty.

Program Instance Monoid__Ap {f : Type -> Type} {a : Type} `{GHC.Base.Applicative
  f} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Ap f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Ap_mappend ;
           GHC.Base.mconcat__ := Monoid__Ap_mconcat ;
           GHC.Base.mempty__ := Monoid__Ap_mempty |}.

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Monoid.Bounded__Ap' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.Monoid.Num__Ap' *)

(* External variables:
     None Type bool comparison list option Control.Monad.Fail.MonadFail
     Control.Monad.Fail.fail Control.Monad.Fail.fail__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.Semigroup GHC.Base.String GHC.Base.compare GHC.Base.compare__
     GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr GHC.Base.liftA2 GHC.Base.liftA2__
     GHC.Base.mappend__ GHC.Base.max GHC.Base.max__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min GHC.Base.min__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____ GHC.Base.op_zgze__
     GHC.Base.op_zgze____ GHC.Base.op_zgzg__ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg__
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg__ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return_ GHC.Base.return___ GHC.Prim.Build_Unpeel GHC.Prim.Unpeel
     GHC.Prim.coerce
*)
