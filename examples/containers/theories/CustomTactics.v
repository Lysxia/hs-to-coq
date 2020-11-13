(** * General tactics *)

(** These tactics are general proof management tactics, and not specific to any particular theory.
*)

Ltac expand_pairs :=
  match goal with
    |- context[let (_,_) := ?e in _] =>
    rewrite (surjective_pairing e)
  end.

Ltac destruct_match :=
  match goal with
  | [ H :context[match ?a with _ => _ end] |- _] =>
    let Heq := fresh "Heq" in
    destruct a eqn:Heq
  | [ |- context[match ?a with _ => _ end]] =>
    let Heq := fresh "Heq" in
    destruct a eqn:Heq
  end.


(* Pose the proof [prf], unless it already exists. *)
Ltac pose_new prf :=
  let prop := type of prf in
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => pose proof prf
  end.

(* Pose the [prop], using [prf], unless it already exists. *)
Ltac assert_new prop prf :=
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => assert prop by prf
  end.


(* A backtracking variant of [eassumption] *)

(** Source: http://stackissue.com/coq/coq/backtracking-eassumption-287.html *)

Ltac beassumption := multimatch goal with H :_ |- _ => exact H end.


(* If [H] is in the context, [H : X -> Y -> Z], create one new goal for each
   assumption [X], [Y], and continue with [H : Z]. *)
Ltac prove_assumptions_of H :=
  match type of H with
  | (?Y -> ?Z) =>
    let A := fresh "HH" in assert (A : Y); [ | specialize (H A); clear A; prove_assumptions_of H ]
  | _ => idtac
  end.

Ltac splits :=
  repeat
    lazymatch goal with
    | [ |- _ /\ _ ] => split
    end.

Ltac decompose_conj H :=
  repeat
    (hnf in H;
    lazymatch type of H with
    | (_ /\ _) =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      destruct H as [H1 H2];
      tryif (try clear H; rename H2 into H)
      then decompose_conj H
      else decompose_conj H2
    end).
