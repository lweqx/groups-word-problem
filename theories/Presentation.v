From HB Require Import structures.
Require Import RelationClasses.
Require Import Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype.

From GWP Require Import Equivalence EquivalenceAlgebra.

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
Definition presented P := (list (sigma P)).

Section InstancesFromList.
Variable P: presentationType.
HB.instance Definition _ := Equality.copy (presented P) (list (sigma P)).
End InstancesFromList.

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

Lemma congruent_left: forall (a u v: M),
  u == v -> a .@ u == a .@ v.
Proof.
move=> a u v; elim.
- move=> r c b H.
  rewrite /concat -!(catA c) !(catA a) !(catA (a ++ c)).
  apply: (Derivation_reduction _ (r.1, r.2)).
  by move: H; case r.
- reflexivity.
- by symmetry.
- by move=> ? v'; transitivity (a .@ v').
Qed.

Lemma congruent_right: forall (b u v: M),
  u == v -> u .@ b == v .@ b.
Proof.
move=> b u v; elim.
- move=> r a c H.
  rewrite /concat -!(catA a) -!(catA _ _ b) !(catA a).
  apply: (Derivation_reduction _ (r.1, r.2)).
  by move: H; case r.
- reflexivity.
- by symmetry.
- by move=> ? a; transitivity (a .@ b).
Qed.

HB.instance Definition _ := isMonoid.Build M concat epsilon associativity neutral_left neutral_right congruent_left congruent_right.
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
transitivity (e @ u @ e).
  by symmetry; apply: neutral_right.
transitivity (e @ v @ e); last first.
  by apply: neutral_right.
exact: (reduction e e).
Qed.

Module PresentationNotations.
Notation "`[ ]" := ([::] : presented _) (format "`[ ]").
Notation "'`[' x ']'" := ([:: x] : presented _).
Notation "`[ x ; y ; .. ; z ]" := ((x :: (cons y .. [:: z] ..)) : presented _)
  (format "`[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]").
End PresentationNotations.

Import PresentationNotations.

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

Definition inv_word (w: G) : G := map invl (rev w).

Lemma inv_word_law : forall x y: G, inv_word (x @ y) == (inv_word y) @ (inv_word x).
Proof. by move=> x y; rewrite /inv_word/=/law/= !map_rev map_cat rev_cat. Qed.

Lemma inv_word_left : forall w: G, w @ (inv_word w) == e.
Proof.
elim=> [|a w IH]; first exact: neutral_left.
rewrite /inv_word/law/= rev_cons map_rcons -rcons_cat -cats1 -cat1s.
have: `[a] @ ((w: presented P) @ inv_word w) @ `[invl a] == e; last by done.
rewrite IH invl_left; reflexivity.
Qed.

Lemma inv_word_right : forall w: G, (inv_word w) @ w == e.
Proof.
elim=> [|a w IH]; first exact: neutral_left.
rewrite /inv_word/law/= rev_cons map_rcons cat_rcons -cat1s -(cat1s a) !(catA _ _ w).
have: (inv_word w) @ (`[invl a] @ `[a]) @ w == e; last by done.
rewrite invl_right neutral_right IH; reflexivity.
Qed.

HB.instance Definition _ := isGroup.Build G inv_word inv_word_law inv_word_left inv_word_right.

End InvertiblePresentedGroup.

Section Cancelation.

Variable P: invertiblePresentationType.
Notation G := (presented P).

Variable a x y : G.

Lemma cancel_left : a @ x == a @ y -> x == y.
Proof.
move=> H.
rewrite -(neutral_left x) -(neutral_left y) -(inverse_right a) -!associativity.
rewrite H; reflexivity.
Qed.

Lemma cancel_right : x @ a == y @ a -> x == y.
Proof.
move=> H.
rewrite -(neutral_right x) -(neutral_right y) -(inverse_left a) !associativity.
rewrite H; reflexivity.
Qed.

End Cancelation.
Arguments cancel_left {_}.
Arguments cancel_right {_}.
