From HB Require Import structures.
Require Import RelationClasses.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype.

From GWP Require Import Equality Algebra.

(* a rewriting rule u -> v *)
Definition relation (Sigma: Type) := ((seq Sigma) * (seq Sigma)) % type.

HB.mixin Record isPresentation (Sigma: Type) := {
  (* TODO: it would be cool to do as follow instead of the `sigma` hack below.
     But HB doesn't implement it. *)
  (* sigma := Sigma; *)
  relations: seq (relation Sigma);
}.

#[short(type="presentationType")]
HB.structure Definition Presentation := { Sigma of hasDecEq Sigma & isPresentation Sigma }.

(* The alphabet of a `P: presentationType` is `P` itself.
   Quantifying over `P` is conceptually a bit weird because it doesn't match the mathematical intuition.
   To make things a little simply presented, we defined `sigma P` as just `P`. *)
Definition sigma (P: presentationType) : Type := P.

Section WordProblem.
Local Infix "@" := cat (at level 50).

Variable P: presentationType.

Let word := (seq (sigma P)).
Let relation := (relation (sigma P)).

(* Whether a rewriting relation `r` is a part of the presentation. *)
Let isRelationOf (r: relation) := r \in relations.

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
End WordProblem.

(* `presented P` is the structure associated to the presentation `P := (Sigma; R)`.
   ie. `presented P` is Sigma^* quotiented by the smallest equivalence relation compatible with R *)
(* Note: a Notation must be used here otherwise HB declares the mixin on the term 'presented P'. *)
Notation "'presented' P" := (list (sigma P)) (at level 10).

(* In a presented structure, equality is given as whether two words are derived. *)
Section PresentedEq.
Variable P: presentationType.

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

Variable P: presentationType.

Local Notation M := (presented P).

Let concat := @cat P.
Let epsilon : seq P := nil.

Infix ".@" := (concat: M -> M -> M) (at level 50).

Let associativity : forall (x y z : M), x .@ (y .@ z) == (x .@ y) .@ z.
Proof. move=> x y w; rewrite /concat catA; reflexivity. Qed.
Let neutral_left : forall (x: M), epsilon .@ x == x.
Proof. move=> x; rewrite /concat /=; reflexivity. Qed.
Let neutral_right : forall (x: M), x .@ epsilon == x.
Proof. move=> x; rewrite /concat cats0; reflexivity. Qed.

HB.instance Definition _ := isMonoid.Build M concat epsilon associativity neutral_left neutral_right.
End PresentedMonoid.

Lemma reduction {P: presentationType}:
  forall (a b u v: presented P),
  (u, v) \in relations -> a @ u @ b == a @ v @ b.
Proof. by move=> a b u v H; apply: (Derivation_reduction _ (u, v)); done. Qed.

Lemma reduction_rule {P: presentationType}:
  forall (u v: presented P),
  (u, v) \in relations -> u == v.
Proof.
move=> u v Hin.
transitivity (nil @ u @ nil).
  by symmetry; apply: neutral_right.
transitivity (nil @ v @ nil); last first.
  by apply: neutral_right.
exact: (reduction nil nil).
Qed.

Lemma repeated_reduction_left {P: presentationType}:
  forall (a u v: presented P),
  u == v -> a @ u == a @ v.
Proof.
move=> a u v; elim.
- move=> r c b H.
  rewrite /law/= -!(catA c) !(catA a) !(catA (a ++ c)).
  apply: reduction.
  by move: H; case r.
- reflexivity.
- by symmetry.
- by move=> ? v'; transitivity (a @ v').
Qed.

Lemma repeated_reduction_right {P: presentationType}:
  forall (b u v: presented P),
  u == v -> u @ b == v @ b.
Proof.
move=> b u v; elim.
- move=> r a c H.
  rewrite /law/= -!(catA a) -!(catA _ _ b) !(catA a).
  apply: reduction.
  by move: H; case r.
- reflexivity.
- by symmetry.
- by move=> ? a; transitivity (a @ b).
Qed.

Lemma repeated_reduction {P: presentationType}:
  forall (a b u v: presented P),
  u == v -> a @ u @ b == a @ v @ b.
Proof.
move=> a b u v eq.
apply: repeated_reduction_right.
by apply: repeated_reduction_left.
Qed.

Import ListNotations.

Notation "`[ ]" := ([]) (format "`[ ]") : list_scope.
Notation "`[ x ]" := ([x]) : list_scope.
Notation "`[ x ; y ; .. ; z ]" := ((x :: (cons y .. [z] ..)))
  (format "`[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : list_scope.

HB.mixin Record hasInvertibleLetters (P: presentationType) := {
  invl : (sigma P) -> (sigma P);
  invl_left : forall c, `[c] @ `[invl c] == e;
  invl_right : forall c, `[invl c] @ `[c] == e;
}.
#[short(type="invertiblePresentationType")]
HB.structure Definition InvertiblePresentation := { P & hasInvertibleLetters P }.

Section InvertiblePresentedGroup.

Variable P: invertiblePresentationType.
Notation G := (presented P).

Definition inv (w: G) : G := map invl (rev w).

Lemma inverse_left : forall w: G, w @ (inv w) == e.
Proof.
move=> w; induction w.
  exact: neutral_left.
rewrite /inv/law/= rev_cons map_rcons -rcons_cat -cats1 -cat1s.
have: `[a] @ (w @ inv w) @ `[invl a] == e; last by done.
transitivity (`[a] @ e @ `[invl a]); first by apply: repeated_reduction.
transitivity (`[a] @ `[invl a]); last first.
  by apply: invl_left.
apply: repeated_reduction_right.
by apply: neutral_left.
Qed.

Lemma inverse_right : forall w: G, (inv w) @ w == e.
Proof.
move=> w; induction w.
  exact: neutral_left.
rewrite /inv/law/= rev_cons map_rcons cat_rcons -cat1s -(cat1s a) !(catA _ _ w).
have: (inv w) @ (`[invl a] @ `[a]) @ w == e; last by done.
transitivity ((inv w) @ e @ w).
  apply: repeated_reduction.
  exact: invl_right.
transitivity (inv w @ w); last done.
apply: repeated_reduction_right.
by apply: neutral_right.
Qed.

HB.instance Definition _ := isGroup.Build G inv inverse_left inverse_right.

End InvertiblePresentedGroup.
