From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype.

From GWP Require Import Equivalence.

HB.mixin Record isMonoid M of hasEq M := {
  law : M -> M -> M;
  e : M;
  associativity : forall x y z, law x (law y z) == law (law x y) z;
  neutral_left : forall x, law e x == x;
  neutral_right : forall x, law x e == x;
}.
#[short(type="monoid")]
HB.structure Definition Monoid := { G of isMonoid G & hasEq G & hasDecEq G }.
Infix "@" := law (at level 50).

HB.mixin Record isGroup G of hasEq G & isMonoid G & hasDecEq G := {
  inv : G -> G;

  inverse_left : forall x, x @ (inv x) == e;
  inverse_right : forall x, (inv x) @ x == e;
}.
#[short(type="group")]
HB.structure Definition Group := { G of isGroup G & hasEq G & isMonoid G & hasDecEq G }.
