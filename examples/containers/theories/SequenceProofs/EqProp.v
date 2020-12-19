From Coq Require Import
  Setoid
  Morphisms.

Require Import GHC.Base.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

(* Ad hoc equivalence relation *)
Class EqProp (a : Type) : Type :=
  eqp : a -> a -> Prop.

Infix "===" := eqp (at level 70).

Class EqLaws (a : Type) `{EqProp a} : Prop :=
  eqlaws :> Equivalence (eqp (a := a)).

(* Monoid laws parameterized by the monoid's equivalence relation *)
Class MonoidLaws m `{Monoid m} `{EqLaws m} : Prop :=
  { monoid_mempty_l : forall x, mappend mempty x === x
  ; monoid_mempty_r : forall x, mappend x mempty === x
  ; mappend_assoc : forall x y z, mappend (mappend x y) z === mappend x (mappend y z)
  ; proper_mappend :> Proper (eqp ==> eqp ==> eqp) mappend
  }.

