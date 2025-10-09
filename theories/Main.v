From mathcomp Require Import all_algebra.
From Stdlib Require Import List.
From Undecidability Require Import Synthetic.Undecidability.

From GWP Require Import AffineMachines.

Import ListNotations.

Section Alphabet.
Open Scope type_scope.

(* The alphabet *)
Variable Sigma: Type.

(* Words on the alphabet `Sigma` *)
Definition word := list Sigma.
(* Concatenation operator on words *)
Definition concat := List.app.
(* The empty word *)
Definition epsilon : word := [].

Definition relation := word * word.
Definition relations := list relation.

Definition initialWord (r: relation) : word := fst r.
Definition finalWord (r: relation) : word := snd r.

End Alphabet.

Notation "u '@' v" := (concat _ u v) (at level 50). (* TODO: think harder about levels *)

Record Presentation := {
    Sigma: Type;
    R: relations Sigma;
}.

Section Presentation.

Variable P: Presentation.
Let Sigma := Sigma P.
Let R := R P.

Let word := word Sigma.
Let relation := relation Sigma.
Let initialWord := initialWord Sigma.
Let finalWord := finalWord Sigma.

(* Whether a rewriting relation `r` is a part of `R` *)
Definition isRelationOf (r: relation) := In r R.

(* `Derivation u v` is the type of witnesses of derivations from
  `u: word` to `v: word` in `P: Presentation` *)
Inductive Derivation (u: word) : word -> Prop :=
  | reduction (r: relation) (a c: word) :
      isRelationOf r ->
      u = a @ (initialWord r) @ c ->
      Derivation u (a @ (finalWord r) @ c)
  | refl : Derivation u u
  | symm (u': word) : Derivation u' u -> Derivation u u'
  | trans (v w: word) :
      Derivation u v -> Derivation v w -> Derivation u w.

Definition word_problem (u v: word) : Prop := Derivation u v.

End Presentation.

Inductive F2_sigma : Type := a | a_inv | b | b_inv.

Definition F2 : Presentation := {|
    Sigma := F2_sigma;
    R := [
      ([a; a_inv], []);
      ([b; b_inv], []);
      ([a_inv; a], []);
      ([b_inv; b], [])
    ];
|}.

(* Les groupes *)
Class Group := {
    G :> Type;
    law : G -> G -> G;
    inv : G -> G;
    e : G;

    associativity : forall x y z, law x (law y z) = law (law x y) z;
    neutral_left : forall x, law e x = x;
    neutral_right : forall x, law x e = x;
    inverse_left : forall x, law x (inv x) = e;
    inverse_right : forall x, law (inv x) x = e;
}.
Arguments law {_}.
Arguments inv {_}.
Arguments e {_}.

Notation "x '.*' y" := (law x y) (at level 50).
Notation "x '.^'" := (inv x) (at level 50).
