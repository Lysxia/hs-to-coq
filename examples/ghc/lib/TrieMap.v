(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Core.
Require Data.IntMap.Internal.
Require Data.Map.Internal.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require Literal.
Require Name.
Require NameEnv.
Require UniqDFM.

(* Converted type declarations: *)

Definition XT a :=
  (option a -> option a)%type.

Inductive TypeMapX (a : Type) : Type := TYPE_MAP_X.

Inductive TyLitMap a : Type
  := TLM (tlm_number : Data.Map.Internal.Map GHC.Num.Integer a) (tlm_string
    : Data.Map.Internal.Map FastString.FastString a)
   : TyLitMap a.

Class TrieMap m := {
  Key : Type ;
  alterTM : forall {b}, Key -> XT b -> m b -> m b ;
  emptyTM : forall {a}, m a ;
  foldTM : forall {a} {b}, (a -> b -> b) -> m a -> b -> b ;
  lookupTM : forall {b}, Key -> m b -> option b ;
  mapTM : forall {a} {b}, (a -> b) -> m a -> m b }.

Arguments Key _ {_}.

Definition TickishMap :=
  (Data.Map.Internal.Map (Core.Tickish Core.Var))%type.

Inductive MaybeMap m a : Type
  := MM (mm_nothing : option a) (mm_just : m a) : MaybeMap m a.

Definition LiteralMap :=
  (Data.Map.Internal.Map Literal.Literal)%type.

Inductive ListMap (m : Type -> Type) (a : Type) : Type := LIST_MAP.

Inductive GenMap (m : Type -> Type) (a : Type) : Type := GEN_MAP.

Definition TypeMapG :=
  (GenMap TypeMapX)%type.

Inductive LooseTypeMap a : Type
  := Mk_LooseTypeMap : (TypeMapG a) -> LooseTypeMap a.

Inductive TypeMap a : Type := Mk_TypeMap : (TypeMapG (TypeMapG a)) -> TypeMap a.

Inductive CoreMapX (a : Type) : Type := CORE_MAP_X.

Definition CoreMapG :=
  (GenMap CoreMapX)%type.

Inductive CoreMap a : Type := Mk_CoreMap : (CoreMapG a) -> CoreMap a.

Inductive CoercionMapX a : Type
  := Mk_CoercionMapX : (TypeMapX a) -> CoercionMapX a.

Definition CoercionMapG :=
  (GenMap CoercionMapX)%type.

Inductive CoercionMap a : Type
  := Mk_CoercionMap : (CoercionMapG a) -> CoercionMap a.

Definition BoundVarMap :=
  Data.IntMap.Internal.IntMap%type.

Inductive VarMap a : Type
  := VM (vm_bvar : BoundVarMap a) (vm_fvar : Core.DVarEnv a) : VarMap a.

Definition BoundVar :=
  nat%type.

Inductive CmEnv : Type
  := CME (cme_next : BoundVar) (cme_env : Core.VarEnv BoundVar) : CmEnv.

Inductive DeBruijn a : Type := D : CmEnv -> a -> DeBruijn a.

Definition BndrMap :=
  TypeMapG%type.

Inductive AltMap a : Type
  := AM (am_deflt : CoreMapG a) (am_data : NameEnv.DNameEnv (CoreMapG a)) (am_lit
    : LiteralMap (CoreMapG a))
   : AltMap a.

Arguments TLM {_} _ _.

Arguments MM {_} {_} _ _.

Arguments Mk_LooseTypeMap {_} _.

Arguments Mk_TypeMap {_} _.

Arguments Mk_CoreMap {_} _.

Arguments Mk_CoercionMapX {_} _.

Arguments Mk_CoercionMap {_} _.

Arguments VM {_} _ _.

Arguments D {_} _ _.

Arguments AM {_} _ _ _.

Instance Default__CmEnv : GHC.Err.Default CmEnv :=
  GHC.Err.Build_Default _ (CME GHC.Err.default GHC.Err.default).

Definition tlm_number {a} (arg_0__ : TyLitMap a) :=
  let 'TLM tlm_number _ := arg_0__ in
  tlm_number.

Definition tlm_string {a} (arg_0__ : TyLitMap a) :=
  let 'TLM _ tlm_string := arg_0__ in
  tlm_string.

Definition mm_just {m} {a} (arg_0__ : MaybeMap m a) :=
  let 'MM _ mm_just := arg_0__ in
  mm_just.

Definition mm_nothing {m} {a} (arg_0__ : MaybeMap m a) :=
  let 'MM mm_nothing _ := arg_0__ in
  mm_nothing.

Definition vm_bvar {a} (arg_0__ : VarMap a) :=
  let 'VM vm_bvar _ := arg_0__ in
  vm_bvar.

Definition vm_fvar {a} (arg_0__ : VarMap a) :=
  let 'VM _ vm_fvar := arg_0__ in
  vm_fvar.

Definition cme_env (arg_0__ : CmEnv) :=
  let 'CME _ cme_env := arg_0__ in
  cme_env.

Definition cme_next (arg_0__ : CmEnv) :=
  let 'CME cme_next _ := arg_0__ in
  cme_next.

Definition am_data {a} (arg_0__ : AltMap a) :=
  let 'AM _ am_data _ := arg_0__ in
  am_data.

Definition am_deflt {a} (arg_0__ : AltMap a) :=
  let 'AM am_deflt _ _ := arg_0__ in
  am_deflt.

Definition am_lit {a} (arg_0__ : AltMap a) :=
  let 'AM _ _ am_lit := arg_0__ in
  am_lit.
(* Midamble *)

Instance Eq___DeBruijn__unit : GHC.Base.Eq_ (DeBruijn unit) := {}.
Proof.
Admitted.

Instance TrieMap__GenMap
   : forall {m},
     forall `{TrieMap m} `{GHC.Base.Eq_ (Key m)}, TrieMap (GenMap m) :=
  {}.
Proof.
Admitted.

Axiom xtG : forall {m} {a},
            forall `{TrieMap m} `{GHC.Base.Eq_ (Key m)},
            Key m -> XT a -> GenMap m a -> GenMap m a.

Axiom lkG : forall {m} {a},
            forall `{TrieMap m} `{GHC.Base.Eq_ (Key m)}, Key m -> GenMap m a -> option a.

(* Converted value declarations: *)

Axiom xtVar : forall {a}, CmEnv -> Core.Var -> XT a -> VarMap a -> VarMap a.

Axiom xtTickish : forall {a},
                  Core.Tickish Core.Var -> XT a -> TickishMap a -> TickishMap a.

Axiom xtTT : forall {a}, DeBruijn unit -> XT a -> TypeMap a -> TypeMap a.

Axiom xtT : forall {a}, DeBruijn unit -> XT a -> TypeMapX a -> TypeMapX a.

Axiom xtMaybe : forall {k} {m} {a},
                (forall {b}, k -> XT b -> m b -> m b) ->
                option k -> XT a -> MaybeMap m a -> MaybeMap m a.

Axiom xtLit : forall {a},
              Literal.Literal -> XT a -> LiteralMap a -> LiteralMap a.

Axiom xtList : forall {m} {k} {a},
               forall `{TrieMap m},
               (forall {b}, k -> XT b -> m b -> m b) ->
               list k -> XT a -> ListMap m a -> ListMap m a.

Axiom xtInt : forall {a},
              nat -> XT a -> Data.IntMap.Internal.IntMap a -> Data.IntMap.Internal.IntMap a.

Axiom xtE : forall {a},
            DeBruijn Core.CoreExpr -> XT a -> CoreMapX a -> CoreMapX a.

Axiom xtDNamed : forall {n} {a},
                 forall `{Name.NamedThing n},
                 n -> XT a -> NameEnv.DNameEnv a -> NameEnv.DNameEnv a.

Axiom xtDFreeVar : forall {a},
                   Core.Var -> XT a -> Core.DVarEnv a -> Core.DVarEnv a.

Axiom xtC : forall {a},
            DeBruijn unit -> XT a -> CoercionMapX a -> CoercionMapX a.

Axiom xtBndr : forall {a}, CmEnv -> Core.Var -> XT a -> BndrMap a -> BndrMap a.

Axiom xtA : forall {a}, CmEnv -> Core.CoreAlt -> XT a -> AltMap a -> AltMap a.

Axiom trieMapView : unit -> option unit.

Axiom op_zgzizg__ : forall {a} {b} {c}, (a -> b) -> (b -> c) -> a -> c.

Axiom op_zbzgzg__ : forall {m2} {a} {m1},
                    forall `{TrieMap m2},
                    (XT (m2 a) -> m1 (m2 a) -> m1 (m2 a)) ->
                    (m2 a -> m2 a) -> m1 (m2 a) -> m1 (m2 a).

Axiom op_zbzg__ : forall {a} {b}, a -> (a -> b) -> b.

Axiom mkDeBruijnContext : list Core.Var -> CmEnv.

Axiom mapVar : forall {a} {b}, (a -> b) -> VarMap a -> VarMap b.

Axiom mapTyLit : forall {a} {b}, (a -> b) -> TyLitMap a -> TyLitMap b.

Axiom mapT : forall {a} {b}, (a -> b) -> TypeMapX a -> TypeMapX b.

Axiom mapMb : forall {m} {a} {b},
              forall `{TrieMap m}, (a -> b) -> MaybeMap m a -> MaybeMap m b.

Axiom mapList : forall {m} {a} {b},
                forall `{TrieMap m}, (a -> b) -> ListMap m a -> ListMap m b.

Axiom mapG : forall {m} {a} {b},
             forall `{TrieMap m}, (a -> b) -> GenMap m a -> GenMap m b.

Axiom mapE : forall {a} {b}, (a -> b) -> CoreMapX a -> CoreMapX b.

Axiom mapA : forall {a} {b}, (a -> b) -> AltMap a -> AltMap b.

Axiom lookupTypeMapWithScope : forall {a},
                               TypeMap a -> CmEnv -> unit -> option a.

Axiom lookupTypeMap : forall {a}, TypeMap a -> unit -> option a.

Axiom lookupCoreMap : forall {a}, CoreMap a -> Core.CoreExpr -> option a.

Axiom lookupCME : CmEnv -> Core.Var -> option BoundVar.

Axiom lkVar : forall {a}, CmEnv -> Core.Var -> VarMap a -> option a.

Axiom lkTickish : forall {a}, Core.Tickish Core.Var -> TickishMap a -> option a.

Axiom lkTT : forall {a}, DeBruijn unit -> TypeMap a -> option a.

Axiom lkT : forall {a}, DeBruijn unit -> TypeMapX a -> option a.

Axiom lkMaybe : forall {k} {m} {a},
                (forall {b}, k -> m b -> option b) -> option k -> MaybeMap m a -> option a.

Axiom lkLit : forall {a}, Literal.Literal -> LiteralMap a -> option a.

Axiom lkList : forall {m} {k} {a},
               forall `{TrieMap m},
               (forall {b}, k -> m b -> option b) -> list k -> ListMap m a -> option a.

Axiom lkE : forall {a}, DeBruijn Core.CoreExpr -> CoreMapX a -> option a.

Axiom lkDNamed : forall {n} {a},
                 forall `{Name.NamedThing n}, n -> NameEnv.DNameEnv a -> option a.

Axiom lkDFreeVar : forall {a}, Core.Var -> Core.DVarEnv a -> option a.

Axiom lkC : forall {a}, DeBruijn unit -> CoercionMapX a -> option a.

Axiom lkBndr : forall {a}, CmEnv -> Core.Var -> BndrMap a -> option a.

Axiom lkA : forall {a}, CmEnv -> Core.CoreAlt -> AltMap a -> option a.

Definition insertTM {m} {a} `{TrieMap m} : Key m -> a -> m a -> m a :=
  fun k v m => alterTM k (fun arg_0__ => Some v) m.

Axiom foldTypeMap : forall {a} {b}, (a -> b -> b) -> b -> TypeMap a -> b.

Axiom foldTyLit : forall {a} {b}, (a -> b -> b) -> TyLitMap a -> b -> b.

Axiom foldMaybe : forall {a} {b}, (a -> b -> b) -> option a -> b -> b.

Axiom foldCoreMap : forall {a} {b}, (a -> b -> b) -> b -> CoreMap a -> b.

Axiom fdVar : forall {a} {b}, (a -> b -> b) -> VarMap a -> b -> b.

Axiom fdT : forall {a} {b}, (a -> b -> b) -> TypeMapX a -> b -> b.

Axiom fdMaybe : forall {m} {a} {b},
                forall `{TrieMap m}, (a -> b -> b) -> MaybeMap m a -> b -> b.

Axiom fdList : forall {m} {a} {b},
               forall `{TrieMap m}, (a -> b -> b) -> ListMap m a -> b -> b.

Axiom fdG : forall {m} {a} {b},
            forall `{TrieMap m}, (a -> b -> b) -> GenMap m a -> b -> b.

Axiom fdE : forall {a} {b}, (a -> b -> b) -> CoreMapX a -> b -> b.

Axiom fdA : forall {a} {b}, (a -> b -> b) -> AltMap a -> b -> b.

Axiom extendTypeMapWithScope : forall {a},
                               TypeMap a -> CmEnv -> unit -> a -> TypeMap a.

Axiom extendTypeMap : forall {a}, TypeMap a -> unit -> a -> TypeMap a.

Axiom extendCoreMap : forall {a}, CoreMap a -> Core.CoreExpr -> a -> CoreMap a.

Axiom extendCMEs : CmEnv -> list Core.Var -> CmEnv.

Axiom extendCME : CmEnv -> Core.Var -> CmEnv.

Axiom emptyTypeMap : forall {a}, TypeMap a.

Axiom emptyTyLitMap : forall {a}, TyLitMap a.

Axiom emptyT : forall {a}, TypeMapX a.

Axiom emptyLiteralMap : forall {a}, LiteralMap a.

Axiom emptyE : forall {a}, CoreMapX a.

Axiom emptyCoreMap : forall {a}, CoreMap a.

Axiom emptyCME : CmEnv.

Definition deleteTM {m} {a} `{TrieMap m} : Key m -> m a -> m a :=
  fun k m => alterTM k (fun arg_0__ => None) m.

Axiom deMaybe : forall {m} {a}, forall `{TrieMap m}, option (m a) -> m a.

Axiom deBruijnize : forall {a}, a -> DeBruijn a.

Instance TrieMap__UniqDFM : TrieMap UniqDFM.UniqDFM := {}.
Proof.
Admitted.

Instance TrieMap__Map
   : forall {k}, forall `{GHC.Base.Ord k}, TrieMap (Data.Map.Internal.Map k) :=
  {}.
Proof.
Admitted.

Instance TrieMap__IntMap : TrieMap Data.IntMap.Internal.IntMap := {}.
Proof.
Admitted.

Instance TrieMap__MaybeMap
   : forall {m}, forall `{TrieMap m}, TrieMap (MaybeMap m) :=
  {}.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `TrieMap.Outputable__ListMap' *)

Instance TrieMap__ListMap
   : forall {m}, forall `{TrieMap m}, TrieMap (ListMap m) :=
  {}.
Proof.
Admitted.

(* Skipping instance `TrieMap.TrieMap__GenMap' of class `TrieMap.TrieMap' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `TrieMap.Outputable__GenMap' *)

Instance TrieMap__TyLitMap : TrieMap TyLitMap := {}.
Proof.
Admitted.

Instance Eq___DeBruijn__list
   : forall {a},
     forall `{GHC.Base.Eq_ (DeBruijn a)}, GHC.Base.Eq_ (DeBruijn (list a)) :=
  {}.
Proof.
Admitted.

(* Skipping instance `TrieMap.Eq___DeBruijn__unit' of class `GHC.Base.Eq_' *)

(* Skipping instance `TrieMap.Eq___DeBruijn__unit' of class `GHC.Base.Eq_' *)

Instance Eq___DeBruijn__CoreAlt : GHC.Base.Eq_ (DeBruijn Core.CoreAlt) := {}.
Proof.
Admitted.

Instance Eq___DeBruijn__CoreExpr : GHC.Base.Eq_ (DeBruijn Core.CoreExpr) := {}.
Proof.
Admitted.

Instance TrieMap__VarMap : TrieMap VarMap := {}.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `TrieMap.Outputable__TypeMapG' *)

Instance TrieMap__TypeMapX : TrieMap TypeMapX := {}.
Proof.
Admitted.

Instance TrieMap__LooseTypeMap : TrieMap LooseTypeMap := {}.
Proof.
Admitted.

Instance TrieMap__TypeMap : TrieMap TypeMap := {}.
Proof.
Admitted.

Instance TrieMap__CoercionMapX : TrieMap CoercionMapX := {}.
Proof.
Admitted.

Instance TrieMap__CoercionMap : TrieMap CoercionMap := {}.
Proof.
Admitted.

Instance TrieMap__AltMap : TrieMap AltMap := {}.
Proof.
Admitted.

Instance TrieMap__CoreMapX : TrieMap CoreMapX := {}.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `TrieMap.Outputable__CoreMap' *)

Instance TrieMap__CoreMap : TrieMap CoreMap := {}.
Proof.
Admitted.

(* External variables:
     Key None Some Type list nat option unit Core.CoreAlt Core.CoreExpr Core.DVarEnv
     Core.Tickish Core.Var Core.VarEnv Data.IntMap.Internal.IntMap
     Data.Map.Internal.Map FastString.FastString GHC.Base.Eq_ GHC.Base.Ord
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.default GHC.Num.Integer
     Literal.Literal Name.NamedThing NameEnv.DNameEnv UniqDFM.UniqDFM
*)