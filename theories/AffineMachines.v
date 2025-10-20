Require Import ssreflect.
From mathcomp Require Import all_algebra.
From Stdlib Require Import List.
From Undecidability Require Import Synthetic.Undecidability.

Open Scope int_scope.
Open Scope ring_scope.

(* Type of non-zero `int`s. *)
Record nzint := {
    n :> int;
    non_zero: n <> 0;
}.
(* 1 as a `nzint` *)
Definition nzint_one : nzint.
Proof. exists 1; done. Qed.

(* `(p, q): State` represents the set of all `p + qZ` *)
Definition State := (int * nzint) % type.
(* TODO: get rid of the ugly 'n' there: why is the coercion not working? *)
Definition isOnState (s: State) (k: int) : Type :=
  let (p, q) := s in
  { z: int | k = p + (n q)*z }.

Definition Transition := (State * State) % type.
Definition startingState (t: Transition) : State := fst t. 
Definition finalState (t: Transition) : State := snd t. 

(* Returns the position obtained after moving a position `k` laying on
   the initial state of `t: transition` along `t` *)
Definition transitionState (t: Transition) :
  forall (k: int), isOnState (startingState t) k -> int.
Proof.
move: t => [] /= [p q] [p' q'] k [] z _.
exact (p' + (n q') * z).
Defined.

(* If we take a transition `t` from a position `k` laying on the
   starting state of `t`, the position reached is the final state of
   `t` *)
Lemma reachesFinalState : forall (t: Transition),
  forall (k: int) (onState: isOnState (startingState t) k),
  isOnState (finalState t) (transitionState t k onState).
Proof.
move=> [[p q] [p' q']] /= k [z _].
by exists z.
Defined.

(* An affine machine. *)
Definition Machine := list Transition.

Section Affine.
Variable A: Machine.

(* Whether `t: Transition` is a transition of `A: Machine` *)
Definition isTransitionOf (t: Transition) := In t A.

(* `Equivalent a b` is the type of witness of equivalence between
  `a: int` and `b: int` in `A: Machine` *)
Inductive Equivalent (a: int) : int -> Prop :=
  | transition (t: Transition) (onState: isOnState (startingState t) a) :
      isTransitionOf t -> Equivalent a (transitionState t a onState)
  | refl : Equivalent a a
  | symm (a': int) (e: Equivalent a' a) : Equivalent a a'
  | trans (b c: int) (e1: Equivalent a c) (e2: Equivalent c b) :
      Equivalent a b.
End Affine.

(* The equivalence problem. *)
Definition equivalence_problem (A: Machine) (m z: int) : Prop := Equivalent A m z.

Definition equivalence_problem_uncurried := fun '(A, m, z) => equivalence_problem A m z.

Theorem equivalence_problem_undecidable : undecidable equivalence_problem_uncurried.
Admitted.
