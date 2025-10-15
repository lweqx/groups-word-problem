From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.

From GWP Require Import Presentation Equality Algebra.

Import PresentationNotations.

Inductive F2_sigma : Type := a | a_inv | b | b_inv.

Definition F2_sigma_eq (u v: F2_sigma) := match (u, v) with
  | (a, a) | (a_inv, a_inv) | (b, b) | (b_inv, b_inv) => true
  | _ => false
  end.
Lemma F2_sigma_eqP : eq_axiom F2_sigma_eq.
Proof. by elim=> [] []; apply: (iffP idP). Qed.
HB.instance Definition _ := hasDecEq.Build F2_sigma F2_sigma_eqP.

HB.instance Definition _ := isPresentation.Build F2_sigma [::
    (pair `[a; a_inv] `[]);
    (pair `[b; b_inv] `[]);
    (pair `[a_inv; a] `[]);
    (pair `[b_inv; b] `[])
  ].

Notation F2 := (presented F2_sigma).

Definition F2_invl (c: F2_sigma) := match c with
  | a => a_inv
  | a_inv => a
  | b => b_inv
  | b_inv => b
  end.

Lemma F2_invl_left : forall c: F2_sigma, `[c; F2_invl c] == `[].
Proof. move=> c; apply: reduction_rule; by case: c. Qed.

Lemma F2_invl_right : forall c: F2_sigma, `[F2_invl c; c] == `[].
Proof. move=> c; apply: reduction_rule; by case: c. Qed.

HB.instance Definition _ := hasInvertibleLetters.Build F2_sigma F2_invl F2_invl_left F2_invl_right.
