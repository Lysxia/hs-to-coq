(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.

(* Converted type declarations: *)

Inductive Identity a : Type := Mk_Identity : a -> Identity a.

Arguments Mk_Identity {_} _.

Definition runIdentity {a} (arg_0__ : Identity a) :=
  match arg_0__ with
    | Mk_Identity runIdentity => runIdentity
  end.
(* Midamble *)

Instance Unpeel_Identity a : Prim.Unpeel (Identity a) a :=
 Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_Identity x => x end) Mk_Identity.

(* Converted value declarations: *)

(* Translating `instance forall {a}, forall `{(GHC.Read.Read a)}, GHC.Read.Read
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Read.Read"
   unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Show.Show a)}, GHC.Show.Show
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Show.Show"
   unsupported *)

Local Definition instance_Data_Foldable_Foldable_Identity_foldMap : forall {m}
                                                                           {a},
                                                                      forall `{GHC.Base.Monoid m},
                                                                        (a -> m) -> Identity a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

Local Definition instance_Data_Foldable_Foldable_Identity_fold : forall {m},
                                                                   forall `{GHC.Base.Monoid m}, Identity m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    instance_Data_Foldable_Foldable_Identity_foldMap GHC.Base.id.

Local Definition instance_Data_Foldable_Foldable_Identity_foldl : forall {b}
                                                                         {a},
                                                                    (b -> a -> b) -> b -> Identity a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition instance_Data_Foldable_Foldable_Identity_foldl' : forall {b}
                                                                          {a},
                                                                     (b -> a -> b) -> b -> Identity a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition instance_Data_Foldable_Foldable_Identity_foldr : forall {a}
                                                                         {b},
                                                                    (a -> b -> b) -> b -> Identity a -> b :=
  fun {a} {b} =>
    fun arg_17__ arg_18__ arg_19__ =>
      match arg_17__ , arg_18__ , arg_19__ with
        | f , z , Mk_Identity x => f x z
      end.

Local Definition instance_Data_Foldable_Foldable_Identity_foldr' : forall {a}
                                                                          {b},
                                                                     (a -> b -> b) -> b -> Identity a -> b :=
  fun {a} {b} => instance_Data_Foldable_Foldable_Identity_foldr.

Local Definition instance_Data_Foldable_Foldable_Identity_length : forall {a},
                                                                     Identity a -> GHC.Num.Int :=
  fun {a} => fun arg_23__ => GHC.Num.fromInteger 1.

Local Definition instance_Data_Foldable_Foldable_Identity_null : forall {a},
                                                                   Identity a -> bool :=
  fun {a} => fun arg_26__ => false.

Local Definition instance_Data_Foldable_Foldable_Identity_product : forall {a},
                                                                      forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a} `{GHC.Num.Num a} => runIdentity.

Local Definition instance_Data_Foldable_Foldable_Identity_sum : forall {a},
                                                                  forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a} `{GHC.Num.Num a} => runIdentity.

Local Definition instance_Data_Foldable_Foldable_Identity_toList : forall {a},
                                                                     Identity a -> list a :=
  fun {a} =>
    fun arg_27__ => match arg_27__ with | Mk_Identity x => cons x nil end.

Local Definition instance_GHC_Base_Functor_Identity_fmap : forall {a} {b},
                                                             (a -> b) -> Identity a -> Identity b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Identity_op_zlzd__ : forall {a} {b},
                                                                  a -> Identity b -> Identity a :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Identity_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Identity : GHC.Base.Functor Identity := fun _
                                                                               k =>
    k (GHC.Base.Functor__Dict_Build Identity (fun {a} {b} =>
                                      instance_GHC_Base_Functor_Identity_op_zlzd__) (fun {a} {b} =>
                                      instance_GHC_Base_Functor_Identity_fmap)).

Local Definition instance_GHC_Base_Applicative_Identity_op_zlztzg__ : forall {a}
                                                                             {b},
                                                                        Identity (a -> b) -> Identity a -> Identity b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Applicative_Identity_op_ztzg__ : forall {a}
                                                                           {b},
                                                                      Identity a -> Identity b -> Identity b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Identity_op_zlztzg__ (GHC.Base.fmap
                                                         (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Identity_pure : forall {a},
                                                                 a -> Identity a :=
  fun {a} => Mk_Identity.

Instance instance_GHC_Base_Applicative_Identity : GHC.Base.Applicative
                                                  Identity := fun _ k =>
    k (GHC.Base.Applicative__Dict_Build Identity (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_Identity_op_ztzg__) (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_Identity_op_zlztzg__) (fun {a} =>
                                          instance_GHC_Base_Applicative_Identity_pure)).

Local Definition instance_GHC_Base_Monad_Identity_op_zgzg__ : forall {a} {b},
                                                                Identity a -> Identity b -> Identity b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Monad_Identity_op_zgzgze__ : forall {a} {b},
                                                                  Identity a -> (a -> Identity b) -> Identity b :=
  fun {a} {b} =>
    fun arg_10__ arg_11__ =>
      match arg_10__ , arg_11__ with
        | m , k => k (runIdentity m)
      end.

Local Definition instance_GHC_Base_Monad_Identity_return_ : forall {a},
                                                              a -> Identity a :=
  fun {a} => GHC.Base.pure.

Instance instance_GHC_Base_Monad_Identity : GHC.Base.Monad Identity := fun _
                                                                           k =>
    k (GHC.Base.Monad__Dict_Build Identity (fun {a} {b} =>
                                    instance_GHC_Base_Monad_Identity_op_zgzg__) (fun {a} {b} =>
                                    instance_GHC_Base_Monad_Identity_op_zgzgze__) (fun {a} =>
                                    instance_GHC_Base_Monad_Identity_return_)).

(* Translating `instance Control.Monad.Fix.MonadFix Identity' failed: OOPS!
   Cannot find information for class "Control.Monad.Fix.MonadFix" unsupported *)

(* Translating `instance Control.Monad.Zip.MonadZip Identity' failed: OOPS!
   Cannot find information for class "Control.Monad.Zip.MonadZip" unsupported *)

Local Definition instance_Data_Traversable_Traversable_Identity_traverse
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f}, (a -> f b) -> Identity a -> f (Identity b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_3__ arg_4__ =>
      match arg_3__ , arg_4__ with
        | f , Mk_Identity a1 => GHC.Base.fmap (fun arg_5__ =>
                                                match arg_5__ with
                                                  | b1 => Mk_Identity b1
                                                end) (f a1)
      end.

Local Definition instance_Data_Traversable_Traversable_Identity_sequenceA
    : forall {f} {a},
        forall `{GHC.Base.Applicative f}, Identity (f a) -> f (Identity a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable_Identity_traverse GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable_Identity_sequence
    : forall {m} {a},
        forall `{GHC.Base.Monad m}, Identity (m a) -> m (Identity a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Identity_sequenceA.

Local Definition instance_Data_Traversable_Traversable_Identity_mapM
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m}, (a -> m b) -> Identity a -> m (Identity b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Identity_traverse.

(* Translating `instance forall {a}, forall `{Foreign.Storable.Storable a},
   Foreign.Storable.Storable (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.Semigroup.Semigroup a},
   Data.Semigroup.Semigroup (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Float.RealFloat a},
   GHC.Float.RealFloat (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.RealFrac a},
   GHC.Real.RealFrac (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.Real a}, GHC.Real.Real
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Monoid a},
   GHC.Base.Monoid (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Arr.Ix a}, GHC.Arr.Ix
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.String.IsString a},
   Data.String.IsString (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.Integral a},
   GHC.Real.Integral (Identity a)' failed: type applications unsupported *)

(* Translating `instance GHC.Generics.Generic1 Identity' failed: OOPS! Cannot
   find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Identity a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.Fractional a},
   GHC.Real.Fractional (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Float.Floating a},
   GHC.Float.Floating (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.Bits.FiniteBits a},
   Data.Bits.FiniteBits (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Enum a}, GHC.Enum.Enum
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Identity a)' failed: OOPS! Cannot find information for class "Data.Data.Data"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.Bits.Bits a}, Data.Bits.Bits
   (Identity a)' failed: type applications unsupported *)

Definition hash_compose {a} {b} {c} :=
  (@Coq.Program.Basics.compose a b c).

Local Definition instance_Data_Foldable_Foldable_Identity_elem : forall {a},
                                                                   forall `{GHC.Base.Eq_ a}, a -> Identity a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    hash_compose (fun arg_14__ => Coq.Program.Basics.compose arg_14__ runIdentity)
                 GHC.Base.op_zeze__.

Instance instance_Data_Foldable_Foldable_Identity : Data.Foldable.Foldable
                                                    Identity := fun _ k =>
    k (Data.Foldable.Foldable__Dict_Build Identity (fun {a} `{GHC.Base.Eq_ a} =>
                                            instance_Data_Foldable_Foldable_Identity_elem) (fun {m}
                                                                                                `{GHC.Base.Monoid m} =>
                                            instance_Data_Foldable_Foldable_Identity_fold) (fun {m}
                                                                                                {a}
                                                                                                `{GHC.Base.Monoid m} =>
                                            instance_Data_Foldable_Foldable_Identity_foldMap) (fun {b} {a} =>
                                            instance_Data_Foldable_Foldable_Identity_foldl) (fun {b} {a} =>
                                            instance_Data_Foldable_Foldable_Identity_foldl') (fun {a} {b} =>
                                            instance_Data_Foldable_Foldable_Identity_foldr) (fun {a} {b} =>
                                            instance_Data_Foldable_Foldable_Identity_foldr') (fun {a} =>
                                            instance_Data_Foldable_Foldable_Identity_length) (fun {a} =>
                                            instance_Data_Foldable_Foldable_Identity_null) (fun {a} `{GHC.Num.Num a} =>
                                            instance_Data_Foldable_Foldable_Identity_product) (fun {a}
                                                                                                   `{GHC.Num.Num a} =>
                                            instance_Data_Foldable_Foldable_Identity_sum) (fun {a} =>
                                            instance_Data_Foldable_Foldable_Identity_toList)).

Instance instance_Data_Traversable_Traversable_Identity
  : Data.Traversable.Traversable Identity := fun _ k =>
    k (Data.Traversable.Traversable__Dict_Build Identity (fun {m}
                                                              {a}
                                                              {b}
                                                              `{GHC.Base.Monad m} =>
                                                  instance_Data_Traversable_Traversable_Identity_mapM) (fun {m}
                                                                                                            {a}
                                                                                                            `{GHC.Base.Monad
                                                                                                            m} =>
                                                  instance_Data_Traversable_Traversable_Identity_sequence) (fun {f}
                                                                                                                {a}
                                                                                                                `{GHC.Base.Applicative
                                                                                                                f} =>
                                                  instance_Data_Traversable_Traversable_Identity_sequenceA) (fun {f}
                                                                                                                 {a}
                                                                                                                 {b}
                                                                                                                 `{GHC.Base.Applicative
                                                                                                                 f} =>
                                                  instance_Data_Traversable_Traversable_Identity_traverse)).

(* Unbound variables:
     Coq.Program.Basics.compose Data.Foldable.Foldable
     Data.Foldable.Foldable__Dict_Build Data.Traversable.Traversable
     Data.Traversable.Traversable__Dict_Build GHC.Base.Applicative
     GHC.Base.Applicative__Dict_Build GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Functor__Dict_Build GHC.Base.Monad GHC.Base.Monad__Dict_Build
     GHC.Base.Monoid GHC.Base.const GHC.Base.fmap GHC.Base.id GHC.Base.op_zeze__
     GHC.Base.op_ztzg__ GHC.Base.pure GHC.Num.Int GHC.Num.Num GHC.Prim.coerce bool
     cons false list nil
*)
