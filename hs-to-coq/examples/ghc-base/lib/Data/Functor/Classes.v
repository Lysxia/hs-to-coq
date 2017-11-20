(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Functor.Const.
Require Data.Functor.Identity.
Require Data.Proxy.
Require GHC.Base.
Require GHC.Tuple.

(* Converted type declarations: *)

Record Eq2__Dict f := Eq2__Dict_Build {
  liftEq2__ : forall {a} {b} {c} {d},
    (a -> b -> bool) -> (c -> d -> bool) -> f a c -> f b d -> bool }.

Definition Eq2 f :=
  forall r, (Eq2__Dict f -> r) -> r.

Existing Class Eq2.

Definition liftEq2 `{g : Eq2 f} : forall {a} {b} {c} {d},
                                    (a -> b -> bool) -> (c -> d -> bool) -> f a c -> f b d -> bool :=
  g _ (liftEq2__ f).

Record Ord2__Dict f := Ord2__Dict_Build {
  liftCompare2__ : forall {a} {b} {c} {d},
    (a -> b -> comparison) -> (c -> d -> comparison) -> f a c -> f b
    d -> comparison }.

Definition Ord2 f `{(Eq2 f)} :=
  forall r, (Ord2__Dict f -> r) -> r.

Existing Class Ord2.

Definition liftCompare2 `{g : Ord2 f} : forall {a} {b} {c} {d},
                                          (a -> b -> comparison) -> (c -> d -> comparison) -> f a c -> f b
                                          d -> comparison :=
  g _ (liftCompare2__ f).

Record Eq1__Dict f := Eq1__Dict_Build {
  liftEq__ : forall {a} {b}, (a -> b -> bool) -> f a -> f b -> bool }.

Definition Eq1 f :=
  forall r, (Eq1__Dict f -> r) -> r.

Existing Class Eq1.

Definition liftEq `{g : Eq1 f} : forall {a} {b},
                                   (a -> b -> bool) -> f a -> f b -> bool :=
  g _ (liftEq__ f).

Record Ord1__Dict f := Ord1__Dict_Build {
  liftCompare__ : forall {a} {b},
    (a -> b -> comparison) -> f a -> f b -> comparison }.

Definition Ord1 f `{(Eq1 f)} :=
  forall r, (Ord1__Dict f -> r) -> r.

Existing Class Ord1.

Definition liftCompare `{g : Ord1 f} : forall {a} {b},
                                         (a -> b -> comparison) -> f a -> f b -> comparison :=
  g _ (liftCompare__ f).
(* Converted value declarations: *)

Local Definition instance_Eq1_option_liftEq : forall {a} {b},
                                                (a -> b -> bool) -> option a -> option b -> bool :=
  fun {a} {b} =>
    fun arg_79__ arg_80__ arg_81__ =>
      match arg_79__ , arg_80__ , arg_81__ with
        | _ , None , None => true
        | _ , None , Some _ => false
        | _ , Some _ , None => false
        | eq , Some x , Some y => eq x y
      end.

Instance instance_Eq1_option : Eq1 option := fun _ k =>
    k (Eq1__Dict_Build option (fun {a} {b} => instance_Eq1_option_liftEq)).

Local Definition instance_Ord1_option_liftCompare : forall {a} {b},
                                                      (a -> b -> comparison) -> option a -> option b -> comparison :=
  fun {a} {b} =>
    fun arg_74__ arg_75__ arg_76__ =>
      match arg_74__ , arg_75__ , arg_76__ with
        | _ , None , None => Eq
        | _ , None , Some _ => Lt
        | _ , Some _ , None => Gt
        | comp , Some x , Some y => comp x y
      end.

Instance instance_Ord1_option : Ord1 option := fun _ k =>
    k (Ord1__Dict_Build option (fun {a} {b} => instance_Ord1_option_liftCompare)).

(* Translating `instance Read1 option' failed: OOPS! Cannot find information for
   class "Read1" unsupported *)

(* Translating `instance Show1 option' failed: OOPS! Cannot find information for
   class "Show1" unsupported *)

Local Definition instance_Eq1_list_liftEq : forall {a} {b},
                                              (a -> b -> bool) -> list a -> list b -> bool :=
  fun {a} {b} =>
    fix liftEq arg_69__ arg_70__ arg_71__
          := match arg_69__ , arg_70__ , arg_71__ with
               | _ , nil , nil => true
               | _ , nil , cons _ _ => false
               | _ , cons _ _ , nil => false
               | eq , cons x xs , cons y ys => andb (eq x y) (liftEq eq xs ys)
             end.

Instance instance_Eq1_list : Eq1 list := fun _ k =>
    k (Eq1__Dict_Build list (fun {a} {b} => instance_Eq1_list_liftEq)).

Local Definition instance_Ord1_list_liftCompare : forall {a} {b},
                                                    (a -> b -> comparison) -> list a -> list b -> comparison :=
  fun {a} {b} =>
    fix liftCompare arg_64__ arg_65__ arg_66__
          := match arg_64__ , arg_65__ , arg_66__ with
               | _ , nil , nil => Eq
               | _ , nil , cons _ _ => Lt
               | _ , cons _ _ , nil => Gt
               | comp , cons x xs , cons y ys => GHC.Base.mappend (comp x y) (liftCompare comp
                                                                  xs ys)
             end.

Instance instance_Ord1_list : Ord1 list := fun _ k =>
    k (Ord1__Dict_Build list (fun {a} {b} => instance_Ord1_list_liftCompare)).

(* Translating `instance Read1 list' failed: OOPS! Cannot find information for
   class "Read1" unsupported *)

(* Translating `instance Show1 list' failed: OOPS! Cannot find information for
   class "Show1" unsupported *)

Local Definition instance_Eq2_GHC_Tuple_pair_type_liftEq2 : forall {a}
                                                                   {b}
                                                                   {c}
                                                                   {d},
                                                              (a -> b -> bool) -> (c -> d -> bool) -> GHC.Tuple.pair_type
                                                              a c -> GHC.Tuple.pair_type b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_58__ arg_59__ arg_60__ arg_61__ =>
      match arg_58__ , arg_59__ , arg_60__ , arg_61__ with
        | e1 , e2 , pair x1 y1 , pair x2 y2 => andb (e1 x1 x2) (e2 y1 y2)
      end.

Instance instance_Eq2_GHC_Tuple_pair_type : Eq2 GHC.Tuple.pair_type := fun _
                                                                           k =>
    k (Eq2__Dict_Build GHC.Tuple.pair_type (fun {a} {b} {c} {d} =>
                         instance_Eq2_GHC_Tuple_pair_type_liftEq2)).

Local Definition instance_Ord2_GHC_Tuple_pair_type_liftCompare2 : forall {a}
                                                                         {b}
                                                                         {c}
                                                                         {d},
                                                                    (a -> b -> comparison) -> (c -> d -> comparison) -> GHC.Tuple.pair_type
                                                                    a c -> GHC.Tuple.pair_type b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_52__ arg_53__ arg_54__ arg_55__ =>
      match arg_52__ , arg_53__ , arg_54__ , arg_55__ with
        | comp1 , comp2 , pair x1 y1 , pair x2 y2 => GHC.Base.mappend (comp1 x1 x2)
                                                                      (comp2 y1 y2)
      end.

Instance instance_Ord2_GHC_Tuple_pair_type : Ord2 GHC.Tuple.pair_type := fun _
                                                                             k =>
    k (Ord2__Dict_Build GHC.Tuple.pair_type (fun {a} {b} {c} {d} =>
                          instance_Ord2_GHC_Tuple_pair_type_liftCompare2)).

(* Translating `instance Read2 GHC.Tuple.pair_type' failed: OOPS! Cannot find
   information for class "Read2" unsupported *)

(* Translating `instance Show2 GHC.Tuple.pair_type' failed: OOPS! Cannot find
   information for class "Show2" unsupported *)

Local Definition instance_forall____GHC_Base_Eq__a____Eq1__GHC_Tuple_pair_type_a__liftEq {inst_a}
                                                                                         `{(GHC.Base.Eq_ inst_a)}
    : forall {a} {b},
        (a -> b -> bool) -> (GHC.Tuple.pair_type inst_a) a -> (GHC.Tuple.pair_type
        inst_a) b -> bool :=
  fun {a} {b} => liftEq2 GHC.Base.op_zeze__.

Instance instance_forall____GHC_Base_Eq__a____Eq1__GHC_Tuple_pair_type_a_ {a}
                                                                          `{(GHC.Base.Eq_ a)} : Eq1 (GHC.Tuple.pair_type
                                                                                                    a) := fun _ k =>
    k (Eq1__Dict_Build (GHC.Tuple.pair_type a) (fun {a} {b} =>
                         instance_forall____GHC_Base_Eq__a____Eq1__GHC_Tuple_pair_type_a__liftEq)).

Local Definition instance_forall____GHC_Base_Ord_a____Ord1__GHC_Tuple_pair_type_a__liftCompare {inst_a}
                                                                                               `{(GHC.Base.Ord inst_a)}
    : forall {a} {b},
        (a -> b -> comparison) -> (GHC.Tuple.pair_type inst_a) a -> (GHC.Tuple.pair_type
        inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Instance instance_forall____GHC_Base_Ord_a____Ord1__GHC_Tuple_pair_type_a_ {a}
                                                                           `{(GHC.Base.Ord a)} : Ord1
                                                                                                 (GHC.Tuple.pair_type
                                                                                                 a) := fun _ k =>
    k (Ord1__Dict_Build (GHC.Tuple.pair_type a) (fun {a} {b} =>
                          instance_forall____GHC_Base_Ord_a____Ord1__GHC_Tuple_pair_type_a__liftCompare)).

(* Translating `instance forall {a}, forall `{(GHC.Read.Read a)}, Read1
   (GHC.Tuple.pair_type a)' failed: OOPS! Cannot find information for class "Read1"
   unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Show.Show a)}, Show1
   (GHC.Tuple.pair_type a)' failed: OOPS! Cannot find information for class "Show1"
   unsupported *)

Local Definition instance_Eq2_sum_liftEq2 : forall {a} {b} {c} {d},
                                              (a -> b -> bool) -> (c -> d -> bool) -> sum a c -> sum b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_43__ arg_44__ arg_45__ arg_46__ =>
      match arg_43__ , arg_44__ , arg_45__ , arg_46__ with
        | e1 , _ , inl x , inl y => e1 x y
        | _ , _ , inl _ , inr _ => false
        | _ , _ , inr _ , inl _ => false
        | _ , e2 , inr x , inr y => e2 x y
      end.

Instance instance_Eq2_sum : Eq2 sum := fun _ k =>
    k (Eq2__Dict_Build sum (fun {a} {b} {c} {d} => instance_Eq2_sum_liftEq2)).

Local Definition instance_Ord2_sum_liftCompare2 : forall {a} {b} {c} {d},
                                                    (a -> b -> comparison) -> (c -> d -> comparison) -> sum a c -> sum b
                                                    d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_36__ arg_37__ arg_38__ arg_39__ =>
      match arg_36__ , arg_37__ , arg_38__ , arg_39__ with
        | comp1 , _ , inl x , inl y => comp1 x y
        | _ , _ , inl _ , inr _ => Lt
        | _ , _ , inr _ , inl _ => Gt
        | _ , comp2 , inr x , inr y => comp2 x y
      end.

Instance instance_Ord2_sum : Ord2 sum := fun _ k =>
    k (Ord2__Dict_Build sum (fun {a} {b} {c} {d} =>
                          instance_Ord2_sum_liftCompare2)).

(* Translating `instance Read2 sum' failed: OOPS! Cannot find information for
   class "Read2" unsupported *)

(* Translating `instance Show2 sum' failed: OOPS! Cannot find information for
   class "Show2" unsupported *)

Local Definition instance_forall____GHC_Base_Eq__a____Eq1__sum_a__liftEq {inst_a}
                                                                         `{(GHC.Base.Eq_ inst_a)} : forall {a} {b},
                                                                                                      (a -> b -> bool) -> (sum
                                                                                                      inst_a) a -> (sum
                                                                                                      inst_a)
                                                                                                      b -> bool :=
  fun {a} {b} => liftEq2 GHC.Base.op_zeze__.

Instance instance_forall____GHC_Base_Eq__a____Eq1__sum_a_ {a} `{(GHC.Base.Eq_
                                                          a)} : Eq1 (sum a) := fun _ k =>
    k (Eq1__Dict_Build (sum a) (fun {a} {b} =>
                         instance_forall____GHC_Base_Eq__a____Eq1__sum_a__liftEq)).

Local Definition instance_forall____GHC_Base_Ord_a____Ord1__sum_a__liftCompare {inst_a}
                                                                               `{(GHC.Base.Ord inst_a)} : forall {a}
                                                                                                                 {b},
                                                                                                            (a -> b -> comparison) -> (sum
                                                                                                            inst_a)
                                                                                                            a -> (sum
                                                                                                            inst_a)
                                                                                                            b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Instance instance_forall____GHC_Base_Ord_a____Ord1__sum_a_ {a} `{(GHC.Base.Ord
                                                           a)} : Ord1 (sum a) := fun _ k =>
    k (Ord1__Dict_Build (sum a) (fun {a} {b} =>
                          instance_forall____GHC_Base_Ord_a____Ord1__sum_a__liftCompare)).

(* Translating `instance forall {a}, forall `{(GHC.Read.Read a)}, Read1 (sum a)'
   failed: OOPS! Cannot find information for class "Read1" unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Show.Show a)}, Show1 (sum a)'
   failed: OOPS! Cannot find information for class "Show1" unsupported *)

Local Definition instance_Eq1_Data_Functor_Identity_Identity_liftEq : forall {a}
                                                                             {b},
                                                                        (a -> b -> bool) -> Data.Functor.Identity.Identity
                                                                        a -> Data.Functor.Identity.Identity b -> bool :=
  fun {a} {b} =>
    fun arg_29__ arg_30__ arg_31__ =>
      match arg_29__ , arg_30__ , arg_31__ with
        | eq , Data.Functor.Identity.Mk_Identity x , Data.Functor.Identity.Mk_Identity
          y => eq x y
      end.

Instance instance_Eq1_Data_Functor_Identity_Identity : Eq1
                                                       Data.Functor.Identity.Identity := fun _ k =>
    k (Eq1__Dict_Build Data.Functor.Identity.Identity (fun {a} {b} =>
                         instance_Eq1_Data_Functor_Identity_Identity_liftEq)).

Local Definition instance_Ord1_Data_Functor_Identity_Identity_liftCompare
    : forall {a} {b},
        (a -> b -> comparison) -> Data.Functor.Identity.Identity
        a -> Data.Functor.Identity.Identity b -> comparison :=
  fun {a} {b} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | comp , Data.Functor.Identity.Mk_Identity x , Data.Functor.Identity.Mk_Identity
          y => comp x y
      end.

Instance instance_Ord1_Data_Functor_Identity_Identity : Ord1
                                                        Data.Functor.Identity.Identity := fun _ k =>
    k (Ord1__Dict_Build Data.Functor.Identity.Identity (fun {a} {b} =>
                          instance_Ord1_Data_Functor_Identity_Identity_liftCompare)).

(* Translating `instance Read1 Data.Functor.Identity.Identity' failed: OOPS!
   Cannot find information for class "Read1" unsupported *)

(* Translating `instance Show1 Data.Functor.Identity.Identity' failed: OOPS!
   Cannot find information for class "Show1" unsupported *)

Local Definition instance_Eq2_Data_Functor_Const_Const_liftEq2 : forall {a}
                                                                        {b}
                                                                        {c}
                                                                        {d},
                                                                   (a -> b -> bool) -> (c -> d -> bool) -> Data.Functor.Const.Const
                                                                   a c -> Data.Functor.Const.Const b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_18__ arg_19__ arg_20__ arg_21__ =>
      match arg_18__ , arg_19__ , arg_20__ , arg_21__ with
        | eq , _ , Data.Functor.Const.Mk_Const x , Data.Functor.Const.Mk_Const y => eq x
                                                                                    y
      end.

Instance instance_Eq2_Data_Functor_Const_Const : Eq2 Data.Functor.Const.Const :=
  fun _ k =>
    k (Eq2__Dict_Build Data.Functor.Const.Const (fun {a} {b} {c} {d} =>
                         instance_Eq2_Data_Functor_Const_Const_liftEq2)).

Local Definition instance_Ord2_Data_Functor_Const_Const_liftCompare2
    : forall {a} {b} {c} {d},
        (a -> b -> comparison) -> (c -> d -> comparison) -> Data.Functor.Const.Const a
        c -> Data.Functor.Const.Const b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_12__ arg_13__ arg_14__ arg_15__ =>
      match arg_12__ , arg_13__ , arg_14__ , arg_15__ with
        | comp , _ , Data.Functor.Const.Mk_Const x , Data.Functor.Const.Mk_Const y =>
          comp x y
      end.

Instance instance_Ord2_Data_Functor_Const_Const : Ord2
                                                  Data.Functor.Const.Const := fun _ k =>
    k (Ord2__Dict_Build Data.Functor.Const.Const (fun {a} {b} {c} {d} =>
                          instance_Ord2_Data_Functor_Const_Const_liftCompare2)).

(* Translating `instance Read2 Data.Functor.Const.Const' failed: OOPS! Cannot
   find information for class "Read2" unsupported *)

(* Translating `instance Show2 Data.Functor.Const.Const' failed: OOPS! Cannot
   find information for class "Show2" unsupported *)

Local Definition instance_forall____GHC_Base_Eq__a____Eq1__Data_Functor_Const_Const_a__liftEq {inst_a}
                                                                                              `{(GHC.Base.Eq_ inst_a)}
    : forall {a} {b},
        (a -> b -> bool) -> (Data.Functor.Const.Const inst_a)
        a -> (Data.Functor.Const.Const inst_a) b -> bool :=
  fun {a} {b} => liftEq2 GHC.Base.op_zeze__.

Instance instance_forall____GHC_Base_Eq__a____Eq1__Data_Functor_Const_Const_a_ {a}
                                                                               `{(GHC.Base.Eq_ a)} : Eq1
                                                                                                     (Data.Functor.Const.Const
                                                                                                     a) := fun _ k =>
    k (Eq1__Dict_Build (Data.Functor.Const.Const a) (fun {a} {b} =>
                         instance_forall____GHC_Base_Eq__a____Eq1__Data_Functor_Const_Const_a__liftEq)).

Local Definition instance_forall____GHC_Base_Ord_a____Ord1__Data_Functor_Const_Const_a__liftCompare {inst_a}
                                                                                                    `{(GHC.Base.Ord
                                                                                                    inst_a)}
    : forall {a} {b},
        (a -> b -> comparison) -> (Data.Functor.Const.Const inst_a)
        a -> (Data.Functor.Const.Const inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Instance instance_forall____GHC_Base_Ord_a____Ord1__Data_Functor_Const_Const_a_ {a}
                                                                                `{(GHC.Base.Ord a)} : Ord1
                                                                                                      (Data.Functor.Const.Const
                                                                                                      a) := fun _ k =>
    k (Ord1__Dict_Build (Data.Functor.Const.Const a) (fun {a} {b} =>
                          instance_forall____GHC_Base_Ord_a____Ord1__Data_Functor_Const_Const_a__liftCompare)).

(* Translating `instance forall {a}, forall `{(GHC.Read.Read a)}, Read1
   (Data.Functor.Const.Const a)' failed: OOPS! Cannot find information for class
   "Read1" unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Show.Show a)}, Show1
   (Data.Functor.Const.Const a)' failed: OOPS! Cannot find information for class
   "Show1" unsupported *)

Local Definition instance_Eq1_Data_Proxy_Proxy_liftEq : forall {a} {b},
                                                          (a -> b -> bool) -> Data.Proxy.Proxy a -> Data.Proxy.Proxy
                                                          b -> bool :=
  fun {a} {b} => fun arg_7__ arg_8__ arg_9__ => true.

Instance instance_Eq1_Data_Proxy_Proxy : Eq1 Data.Proxy.Proxy := fun _ k =>
    k (Eq1__Dict_Build Data.Proxy.Proxy (fun {a} {b} =>
                         instance_Eq1_Data_Proxy_Proxy_liftEq)).

Local Definition instance_Ord1_Data_Proxy_Proxy_liftCompare : forall {a} {b},
                                                                (a -> b -> comparison) -> Data.Proxy.Proxy
                                                                a -> Data.Proxy.Proxy b -> comparison :=
  fun {a} {b} => fun arg_4__ arg_5__ arg_6__ => Eq.

Instance instance_Ord1_Data_Proxy_Proxy : Ord1 Data.Proxy.Proxy := fun _ k =>
    k (Ord1__Dict_Build Data.Proxy.Proxy (fun {a} {b} =>
                          instance_Ord1_Data_Proxy_Proxy_liftCompare)).

(* Translating `instance Show1 Data.Proxy.Proxy' failed: OOPS! Cannot find
   information for class "Show1" unsupported *)

(* Translating `instance Read1 Data.Proxy.Proxy' failed: OOPS! Cannot find
   information for class "Read1" unsupported *)

Definition compare1 {f} {a} `{Ord1 f} `{GHC.Base.Ord a} : f a -> f
                                                          a -> comparison :=
  liftCompare GHC.Base.compare.

Definition compare2 {f} {a} {b} `{Ord2 f} `{GHC.Base.Ord a} `{GHC.Base.Ord b}
    : f a b -> f a b -> comparison :=
  liftCompare2 GHC.Base.compare GHC.Base.compare.

Definition eq1 {f} {a} `{Eq1 f} `{GHC.Base.Eq_ a} : f a -> f a -> bool :=
  liftEq GHC.Base.op_zeze__.

Definition eq2 {f} {a} {b} `{Eq2 f} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b} : f a
                                                                          b -> f a b -> bool :=
  liftEq2 GHC.Base.op_zeze__ GHC.Base.op_zeze__.

(* Unbound variables:
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Proxy.Proxy Eq GHC.Base.Eq_ GHC.Base.Ord GHC.Base.compare GHC.Base.mappend
     GHC.Base.op_zeze__ GHC.Tuple.pair_type Gt Lt Some andb bool comparison cons
     false inl inr list option pair sum true
*)
