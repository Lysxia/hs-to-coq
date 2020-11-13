Require Import GHC.Base.
Require Import Data.Sequence.Internal.

Lemma fmap_fmap__Digit {A B C} (f : A -> B) (g : B -> C) (d : Digit A)
  : fmap g (fmap f d) = fmap (fun a => g (f a)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma fmap_ext__Digit {A B} (f g : A -> B) (d : Digit A)
  : (forall a, f a = g a) -> fmap f d = fmap g d.
Proof.
  intros E; destruct d; cbn; f_equal; reflexivity + apply E.
Qed.
