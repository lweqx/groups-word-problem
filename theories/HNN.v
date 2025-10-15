From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype.

From GWP Require Import Presentation Algebra Equality.

Import PresentationNotations.

Section HNN.

Variable P: invertiblePresentationType.
Let G := presented P.

(* H, a subgroup of G, given as a list of generators *)
Variable genH: list G.

Inductive HNN_extension : Type :=
  | HNN_group : P -> HNN_extension
  | HNN_b : HNN_extension
  | HNN_b_inv : HNN_extension.

Definition HNN_extension_eq (u v: HNN_extension) := match (u, v) with
  | (HNN_group x, HNN_group y) => eq_op x y
  | (HNN_b, HNN_b) => true
  | (HNN_b_inv, HNN_b_inv) => true
  | _ => false
  end.
Lemma HNN_extension_eqP : eq_axiom HNN_extension_eq.
Proof.
elim=> [p||] [q||]; apply: (iffP idP) => //.
by move=> /eqP ->.
by move => [->]; rewrite /HNN_extension_eq.
Qed.
HB.instance Definition _ := hasDecEq.Build HNN_extension HNN_extension_eqP.

#[local]
Definition inj_word (w: G) := map HNN_group w.

Definition relations := (map (fun '(u, v) => (inj_word u, inj_word v)) (@relations P)) ++
  [::
    (`[HNN_b; HNN_b_inv], `[]);
    (`[HNN_b_inv; HNN_b], `[])
  ] ++
  (map (fun u => (`[HNN_b] ++ (inj_word u), (inj_word u) ++ `[HNN_b])) genH).
HB.instance Definition _ := isPresentation.Build HNN_extension relations.

Notation HNN := (presented HNN_extension).

Lemma inj_word_morphism : forall (u v: G), u == v -> inj_word u == inj_word v.
Proof.
move=> u v; elim=> [r a b H|||].
- rewrite /inj_word !map_cat.
  apply: repeated_reduction.
  apply: reduction_rule.
  rewrite mem_cat.
  apply /orP; left.
  apply /mapP.
  move: r H; case=> a' b' ?.
  by exists (a', b').
- reflexivity.
- by symmetry.
- by move=> u' v' w'; transitivity (inj_word v').
Qed.

#[local]
Definition HNN_invl (f: HNN_extension) := match f with
  | HNN_group l => HNN_group (invl l)
  | HNN_b => HNN_b_inv
  | HNN_b_inv => HNN_b
  end.

#[local]
Lemma HNN_invl_left : forall (c: HNN_extension), `[c] @ `[HNN_invl c] == `[].
Proof.
elim=> [l||]; last 2 first.
- by apply: reduction_rule; rewrite !mem_cat orbT.
- by apply: reduction_rule; rewrite !mem_cat orbT.
- have := inj_word_morphism `[l; invl l] `[]; apply.
  exact: invl_left.
Qed.

#[local]
Lemma HNN_invl_right : forall (c: HNN_extension), `[HNN_invl c] @ `[c] == `[].
elim=> [l||]; last 2 first.
- by apply: reduction_rule; rewrite !mem_cat orbT.
- by apply: reduction_rule; rewrite !mem_cat orbT.
- have := inj_word_morphism `[invl l; l] `[]; apply.
  exact: invl_right.
Qed.

HB.instance Definition _ := hasInvertibleLetters.Build HNN_extension HNN_invl HNN_invl_left HNN_invl_right.

(* H = {x in G | tx = xt} *)

End HNN.

