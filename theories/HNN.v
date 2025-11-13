From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype.

From GWP Require Import Presentation EquivalenceAlgebra Equivalence.

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
elim=> [p||] [q||]; apply: (iffP idP) => // [/eqP -> //|[] ->].
by rewrite /HNN_extension_eq.
Qed.
HB.instance Definition _ := hasDecEq.Build HNN_extension HNN_extension_eqP.

#[local]
Definition inj_word (w: G) := map HNN_group w.

Definition relations := (map (fun '(u, v) => (inj_word u, inj_word v)) (@relations P)) ++
  [::
    ([:: HNN_b; HNN_b_inv], [::]);
    ([:: HNN_b_inv; HNN_b], [::])
  ] ++
  (map (fun u => ([:: HNN_b] ++ (inj_word u), (inj_word u) ++ [:: HNN_b])) genH).
HB.instance Definition _ := isPresentation.Build HNN_extension relations.

Notation HNN := (presented HNN_extension).

Lemma inj_word_morphism : forall (u v: G), u == v -> (inj_word u) == (inj_word v) :> HNN.
Proof.
move=> u v; elim=> [[a' b'] a b H|||].
- rewrite /inj_word !map_cat.
  apply /repeated_reduction /reduction_rule.
  rewrite mem_cat; apply /orP; left; apply /mapP.
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

Let genH': list HNN := map inj_word genH.
Let inj_word v := (inj_word v: HNN).

Lemma comm_b_gens (a: HNN) :
   a \in (genH' ++ map inv genH') -> `[HNN_b] @ a == a @ `[HNN_b].
Proof.
rewrite mem_cat; move=> /orP [] H.
- apply: reduction_rule.
  do 2![rewrite mem_cat; apply /orP; right].
  move: H => /mapP [u /[swap] ->].
  exact: map_f.
- move: H => /mapP [u /[swap] ->] /mapP [v /[swap] ->] ?.
  symmetry.
  apply /(cancel_left (inj_word v)) /(cancel_right (inj_word v)).
  rewrite associativity inverse_left neutral_left.
  rewrite -associativity -[(`[HNN_b] @ (inv (inj_word v))) @ _]associativity.
  rewrite [inv (inj_word v) @ inj_word v]inverse_right neutral_right.
  apply: reduction_rule.
  do 2![rewrite mem_cat; apply /orP; right].
  exact: map_f.
Qed.

(* H < {x in G | tx = xt} *)
Lemma subgroup_caracterization_forward :
  forall (x: HNN), inSubgroup genH' x -> `[HNN_b] @ x == x @ `[HNN_b].
Proof.
move=> x; elim=> [l [H eq]].
transitivity (`[HNN_b] @ (prod l)); first by apply: repeated_reduction_left. 
transitivity ((prod l) @ `[HNN_b]); last by apply: repeated_reduction_right; symmetry.
clear eq x.
move: H; elim: l => [_|a l IH].
  by rewrite prod0 neutral_left neutral_right; reflexivity.
rewrite -cat1s all_cat all_seq1.
move=> /andP [] a_generator Hlgen.
rewrite (prod1s a l) associativity comm_b_gens //.
rewrite -associativity -IH // associativity.
reflexivity.
Qed.

(* H > {x in G | tx = xt} *)
Lemma subgroup_caracterization_backward :
  forall (x: HNN), `[HNN_b] @ x == x @ `[HNN_b] -> inSubgroup genH' x.
Admitted.

(* proof plan:
   - find an equivalent presentation of G that is convergent.
   - prove that the resulting HNN presentation is convergent.
   - if b x == x b, then reduced (b x) == reduced (x b)
     so: reduced (b x) = reduced (x b)
     if x is not in H:
      reduced (b x) = b (reduced x)
      reduced (x b) = (reduced x) b
     so b (reduced x) = (reduced x) b
     (reduced x) doesnt contain any b, so (reduced x) = [] = (reduced e)
     so x = e, thus x in H: boom, explosion

   technical difficulties:
   - the standard convergent presentation of G might not be finite
   - `reduced` is not computable if the presentation is not finite
   - need to introduce the notions of an equivalent presentation
*)

(* H = {x in G | tx = xt} *)
Lemma subgroup_caracterization :
  forall (x: HNN), inSubgroup genH' x <-> `[HNN_b] @ x == x @ `[HNN_b].
Proof.
move=> x; split.
- exact: subgroup_caracterization_forward.
- exact: subgroup_caracterization_backward.
Qed.

End HNN.

