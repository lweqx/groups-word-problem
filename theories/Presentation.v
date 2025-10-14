From HB Require Import structures.
Require Import ssreflect RelationClasses.
From Stdlib Require Import List.

From GWP Require Import Equality Algebra.

Section Relation.
Open Scope type_scope.

(* The alphabet *)
Variable Sigma: Type.

(* a rewriting rule u -> v *)
Definition relation := (list Sigma) * (list Sigma).
Definition relations := list relation.

End Relation.

(* A presentation with a finite set of relations. *)
Record Presentation := {
    Sigma: Type;
    R: relations Sigma;
}.

Section Presentation.
Local Infix "@" := List.app (at level 50).

Variable P: Presentation.
Let Sigma := Sigma P.
Let R := R P.
Let relation := relation Sigma.
Local Notation word := (list Sigma).

(* Whether a rewriting relation `r` is a part of `R` *)
Let isRelationOf (r: relation) := In r R.

Let initialWord (r: relation) : word := fst r.
Let finalWord (r: relation) : word := snd r.

(* `Derivation u v` is the type of witnesses of derivations from
  `u: word` to `v: word` in `P: Presentation` *)
Inductive Derivation : word -> word -> Prop :=
  | Derivation_reduction (r: relation) (a c: word) :
      isRelationOf r ->
      Derivation (a @ (initialWord r) @ c) (a @ (finalWord r) @ c)
  | Derivation_refl (u: word): Derivation u u
  | Derivation_symm (u u': word) : Derivation u u' -> Derivation u' u
  | Derivation_trans (u v w: word) :
      Derivation u v -> Derivation v w -> Derivation u w.

(* The word problem of the presentation `P`. *)
Definition word_problem (u v: word) : Prop := Derivation u v.

End Presentation.

(* `presented P` is the structure associated to the presentation `P := (Sigma; R)`.
   ie. `presented P` is Sigma^* quotiented by the smallest equivalence relation compatible with R *)
(* Note: a Notation must be used here otherwise HB declares the mixin on the term 'presented P'. *)
Notation "'presented' P" := (list (Sigma P)) (at level 10).

(* In a presented structure, equality is given as whether two words are derived. *)
Section PresentedEq.
Variable P: Presentation.

(* Note: a Notation must be used here otherwise HB declares the mixin on the constant M. *)
Local Notation M := (presented P).
Let eq := word_problem P.

Lemma M_refl : forall x, eq x x.
Proof. exact: Derivation_refl. Qed.
Lemma M_symm : forall x y, eq x y -> eq y x.
Proof. exact: Derivation_symm. Qed.
Lemma M_trans : forall x y z, eq x y -> eq y z -> eq x z.
Proof. exact: Derivation_trans. Qed.

(* HB bug: having a duplicate (P: presentation) results in a Ocaml assertion failure *)
HB.instance Definition _ := @hasEq.Build M eq M_refl M_symm M_trans.
End PresentedEq.

(* All presented structures have a monoid structure *)
Section PresentedMonoid.
Variable P: Presentation.
Local Notation M := (presented P).
Let Sigma := Sigma P.

Let concat := @List.app Sigma.
Let epsilon : list Sigma := nil.

Infix ".@" := (concat: M -> M -> M) (at level 50).

Let associativity : forall (x y z : M), x .@ (y .@ z) == (x .@ y) .@ z.
Proof. by move=> x y z; rewrite /concat app_assoc; reflexivity. Qed.
Let neutral_left : forall (x: M), epsilon .@ x == x.
Proof. move=> x; rewrite /concat /=; reflexivity. Qed.
Let neutral_right : forall (x: M), x .@ epsilon == x.
Proof. move=> x; rewrite /concat app_nil_r; reflexivity. Qed.

HB.instance Definition _ := isMonoid.Build M concat epsilon associativity neutral_left neutral_right.
End PresentedMonoid.

Lemma reduction {P: Presentation}:
  forall (a b u v: presented P),
  In (u, v) (R P) -> a @ u @ b == a @ v @ b.
Proof. by move=> a b u v H; apply: (Derivation_reduction _ (u, v)); done. Qed.

Lemma repeated_reduction_left {P: Presentation}:
  forall (a u v: presented P),
  u == v -> a @ u == a @ v.
Proof.
move=> a u v eq.
induction eq.
- rewrite /law/= -!(app_assoc a0) !(app_assoc a) !(app_assoc (a ++ a0)).
  apply: reduction.
  by move: H; case r.
- reflexivity.
- by symmetry.
- by transitivity (a @ v).
Qed.

Lemma repeated_reduction_right {P: Presentation}:
  forall (b u v: presented P),
  u == v -> u @ b == v @ b.
Proof.
move=> b u v eq.
induction eq.
- rewrite /law/= -!(app_assoc a) -!(app_assoc _ _ b) !(app_assoc a).
  apply: reduction.
  by move: H; case r.
- reflexivity.
- by symmetry.
- by transitivity (v @ b).
Qed.

Lemma repeated_reduction {P: Presentation}:
  forall (a b u v: presented P),
  u == v -> a @ u @ b == a @ v @ b.
Proof.
move=> a b u v eq.
apply: repeated_reduction_right.
by apply: repeated_reduction_left.
Qed.
