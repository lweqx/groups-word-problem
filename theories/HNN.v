From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype fintype tuple.

From GWP Require Import Presentation EquivalenceAlgebra Equivalence.

(* First HNN extension *)
Section HNN.
Variable G: group.
Variable isos: seq (local_morphism G).
Let isos_count := size isos.

Definition HNN_nth_iso (i: 'I_isos_count): local_morphism G :=
  nth (morphism_to_local_morphism (identity_morphism G)) isos i.

Definition HNN: group.
Admitted.

Definition HNN_extension_base := G.

Definition HNN_injection: injectiveMorphism HNN_extension_base HNN.
Admitted.
HB.instance Definition _ := isSubgroup.Build HNN HNN_extension_base HNN_injection.

Definition HNN_ts: isos_count.-tuple HNN.
Admitted.

Lemma iso_representation: forall i: 'I_isos_count,
  let t := tnth HNN_ts i in
  let lm := HNN_nth_iso i in
  forall (x: lm.(lm_source_subgroup)), subgroup_inj (subgroup_inj (lm x) : HNN_extension_base) == t @ (subgroup_inj (subgroup_inj x : HNN_extension_base)) @ (inv t).
Admitted.

Section HNNStableSubgroup.
Variable K: subgroup G.

Hypothesis K_invariance: forall i: 'I_isos_count, is_subgroup_stable (HNN_nth_iso i) K.

Definition HNN_subgroup_ts_extension : HNN -> Prop.
Admitted.

Lemma HNNsgte_law: forall x y : HNN,
  HNN_subgroup_ts_extension x ->
  HNN_subgroup_ts_extension y -> HNN_subgroup_ts_extension (x @ y).
Admitted.

Lemma HNNsgte_neutral: HNN_subgroup_ts_extension e.
Admitted.

Lemma HNNsgte_inv: forall x : HNN,
  HNN_subgroup_ts_extension x -> HNN_subgroup_ts_extension (inv x).
Admitted.

HB.instance Definition _ := isSubgroupCharacterizer.Build HNN HNN_subgroup_ts_extension HNNsgte_law HNNsgte_neutral HNNsgte_inv.

Let K_extended := subgroup_by HNN_subgroup_ts_extension.

(* <K, t1, ..., tn> \cap G = G *)
(* x \in G -> x \in <K, t1, ..., tn> *)
Lemma HNN_stable_inter_G_is_G : forall (x: G), (subgroup_inj (x: HNN_extension_base)) \insubgroup (K_extended: subgroup HNN).
Admitted.

End HNNStableSubgroup.
End HNN.
Arguments HNN_stable_inter_G_is_G {G} isos K.
Arguments HNN {G}.
Arguments HNN_ts {G}.

(*
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype fintype.

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
Proof.
Admitted.

(* H = {x in G | tx = xt} *)
Lemma subgroup_caracterization :
  forall (x: HNN), inSubgroup genH' x <-> `[HNN_b] @ x == x @ `[HNN_b].
Proof.
move=> x; split.
- exact: subgroup_caracterization_forward.
- exact: subgroup_caracterization_backward.
Qed.

End HNN.

Section HNNIso.

Variable P: invertiblePresentationType.
Let G := presented P.

Variable n: nat.
(* n subgroups of G given by their list of generators.
   H1, ..., Hn *)
Variable subgroups: seq (seq G).
Hypothesis n_subgroups: size subgroups = n.
(* list of isos with domains H1, ..., Hn *)
Variable isos: seq (G -> G).
Hypothesis n_isos: size isos = n.
Let iso i := nth id isos i.

Definition free_familly (f: seq G) :=
  
Definition morphism_is_iso (H: seq G) (iso: G -> G) :=
  [seq iso h | h <- H].

Hypothesis isos_are_iso: forall i: 'I_n,
  [seq iso i.

End HNNIso.

*)
