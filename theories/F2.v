From HB Require Import structures.
Require Import ssreflect.
From mathcomp Require Import all_algebra.
From Stdlib Require Import List.
From Undecidability Require Import Synthetic.Undecidability.

From GWP Require Import Presentation Equality Algebra.

Import ListNotations.

Inductive F2_sigma : Type := a | a_inv | b | b_inv.

HB.instance Definition _ := isPresentation.Build F2_sigma [
    ([a; a_inv], []);
    ([b; b_inv], []);
    ([a_inv; a], []);
    ([b_inv; b], [])
  ].

Notation F2 := (presented F2_sigma).

Module F2Group.
Section F2Group.

Definition inv_letter (c: F2_sigma) := match c with
  | a => a_inv
  | a_inv => a
  | b => b_inv
  | b_inv => b
  end.

Lemma inv_letter_is_left_inverse : forall c: F2_sigma, `[c; inv_letter c] == `[].
Proof.
move=> c.
transitivity (`[] @ `[c; inv_letter c]).
  exact: neutral_left.
transitivity (`[] @ `[c; inv_letter c] @ `[]).
  symmetry; exact: neutral_right.
transitivity (`[] @ `[] @ `[] : F2); last first.
  transitivity (`[] @ `[] : F2); [symmetry | ]; exact: neutral_right.
apply: reduction.
by case: c; repeat ((try by left); right).
Qed.

Lemma inv_letter_is_right_inverse : forall c: F2_sigma, `[inv_letter c; c] == `[].
Proof.
move=> c.
transitivity (`[] @ `[inv_letter c; c]).
  exact: neutral_left.
transitivity (`[] @ `[inv_letter c; c] @ `[]).
  symmetry; exact: neutral_right.
transitivity (`[] @ `[] @ `[] : F2); last first.
  transitivity (`[] @ `[] : F2); [symmetry | ]; exact: neutral_right.
apply: reduction.
by case: c; repeat ((try by left); right).
Qed.

Definition inv (w: F2) : F2 := List.map inv_letter (List.rev w).

Lemma inv_is_left_inverse : forall w: F2, w @ (inv w) == e.
Proof.
move=> w; induction w.
  exact: neutral_left.
transitivity (`[a0] @ (w @ (inv w)) @ `[inv_letter a0]).
  rewrite /inv/= map_app.
  rewrite /law/= app_assoc.
  reflexivity.
transitivity (`[a0] @ e @ `[inv_letter a0]).
  by apply: repeated_reduction.
transitivity (`[a0] @ `[inv_letter a0]).
  apply: repeated_reduction_right.
  by apply: neutral_left.
by apply: inv_letter_is_left_inverse.
Qed.

Lemma inv_is_right_inverse : forall w: F2, (inv w) @ w == e.
Proof.
move=> w; induction w.
  exact: neutral_left.
transitivity ((inv w) @ (`[inv_letter a0] @ `[a0]) @ w).
  rewrite /inv/= map_app.
  rewrite /law/= -!app_assoc.
  reflexivity.
transitivity ((inv w) @ e @ w).
  apply: repeated_reduction.
  exact: inv_letter_is_right_inverse.
transitivity (inv w @ w).
  apply: repeated_reduction_right.
  by apply: neutral_right.
done.
Qed.

HB.instance Definition _ := isGroup.Build F2 inv inv_is_left_inverse inv_is_right_inverse.

End F2Group.
End F2Group.
