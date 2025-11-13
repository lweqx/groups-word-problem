From HB Require Import structures.
Require Import ssreflect RelationClasses.

(* Types with an equality, noted `==`.
   
   All types have an equality in Rocq: `eq`.
   However this equality type is essentially definitional equality,
   while our `==` can be any equivalence relation. This is useful to
   represent quotiented types. *)
HB.mixin Record hasEq T := {
  eq : T -> T -> Prop;

  refl : forall x, eq x x;
  symm : forall x y, eq x y -> eq y x;
  trans : forall x y z, eq x y -> eq y z -> eq x z;
}.
HB.structure Definition EqProp := { T of hasEq T }.

Infix "==" := eq (at level 70, no associativity).
Notation "x == y :> T" := ((x: T) == (y: T)) (at level 70, no associativity).

(* Defining Rocq relation classes.
   This enables the `reflexivity`/`symmetry`/`transitivity` tactics to work with `eqType`s. *)
Section EqEquivalence.
Variable T: EqProp.type.
Let eq := @eq T.

Instance EqReflexivity : Reflexive eq.
Proof. exact: hasEq.refl. Qed.
Instance EqSymmetry : Symmetric eq.
Proof. exact: hasEq.symm. Qed.
Instance EqTransitivity : Transitive eq.
Proof. exact: hasEq.trans. Qed.
Instance EqEquivalence : Equivalence eq := {}.
End EqEquivalence.
Existing Instance EqReflexivity.
Existing Instance EqSymmetry.
Existing Instance EqTransitivity.
Existing Instance EqEquivalence.
