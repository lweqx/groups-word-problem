From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Stdlib.Program Require Import Equality.
From mathcomp Require Import ssreflect.

Section Step_to_ClosRST.

Variable A B: Type.
Variable R: A -> A -> Prop.
Variable R': B -> B -> Prop.

Hypothesis encoding: B -> A.
Hypothesis encoding_injective: forall x x', encoding x = encoding x' -> x = x'.

Hypothesis equiv_R_R': forall s s', R (encoding s) (encoding s') <-> R' s s'.

Hypothesis R_preserves_encoding_right: forall s x', R (encoding s) x' -> exists s', encoding s' = x'.
Hypothesis R_preserves_encoding_left: forall x s', R x (encoding s') -> exists s, encoding s = x.

Lemma closRST_R_equiv_R' : forall s s',
  (clos_refl_sym_trans _ R (encoding s) (encoding s'))
    <->
  (clos_refl_sym_trans _ R' s s').
Proof.
move=> s s'; split.
- move=> /clos_rst_rst1n_iff H; dependent induction H.
    move: x => /encoding_injective ->.
    exact /rst_refl.
  case: H => /[dup] H.
  - move=> /R_preserves_encoding_right [] s'' y_decoding.
    apply /(rst_trans _ _ _ s'').
      apply /rst_step.
      apply /(equiv_R_R' s s'').
      rewrite y_decoding.
      exact H.
    exact: (IHclos_refl_sym_trans_1n R R' encoding).
  - move=> /R_preserves_encoding_left [] s'' y_decoding.
    apply /(rst_trans _ _ _ s'').
      apply /rst_sym /rst_step.
      apply /(equiv_R_R' s'' s).
      rewrite y_decoding.
      exact H.
    exact: (IHclos_refl_sym_trans_1n R R' encoding).
- move=> /clos_rst_rst1n_iff; elim.
    move=> x; exact /rst_refl.
  move=> x y z [] ? ? ?.
  - apply /(rst_trans _ _ _ (encoding y)) => //.
    exact /rst_step /equiv_R_R'.
  - apply /(rst_trans _ _ _ (encoding y)) => //.
    exact /rst_sym /rst_step /equiv_R_R'.
Qed.

End Step_to_ClosRST.

Section ConfluenceFromDeterminism.

Variable A: Type.
Variable R: A -> A -> Prop.

Hypothesis R_det: forall x y y', R x y -> R x y' -> y = y'.

(* Note: copied from mm2_steps_confluent *)
Lemma R_confluent : forall x y y',
            (clos_refl_trans _ R x y) -> (clos_refl_trans _ R x y') ->
  exists z, (clos_refl_trans _ R y z) /\ (clos_refl_trans _ R y' z).
Proof.
move=> x y y'.
move=> /clos_rt_rt1n_iff H; elim: H y'.
- move=> *. eexists. by split; [|apply rt_refl].
- move=> ? {}y1 z1 Hx /clos_rt_rt1n_iff Hyz IH ? /clos_rt_rt1n_iff Hxy2.
  case: Hxy2 Hx IH.
  + move=> ? _. eexists. split; [apply: rt_refl|].
    apply: rt_trans; [apply: rt_step|]; by eassumption.
  + move=> y2 z2 /R_det Hx /clos_rt_rt1n_iff Hy2z2 /Hx {Hx} ? IH.
    subst y2. move: Hy2z2 => /IH [z [??]].
    by exists z.
Qed.

End ConfluenceFromDeterminism.

Section StepToDeadendReversibility.

Variable A: Type.
Variable R: A -> A -> Prop.

Hypothesis R_confluent : forall x y y',
            (clos_refl_trans _ R x y) -> (clos_refl_trans _ R x y') ->
  exists z, (clos_refl_trans _ R y z) /\ (clos_refl_trans _ R y' z).

Variable ending_state: A.

Hypothesis ending_state_is_dead_end : forall x,
    (clos_refl_trans _ R ending_state x) -> x = ending_state.

Lemma R_to_stop_is_reversible : forall s,
  (clos_refl_trans _ R s ending_state)
    <->
  (clos_refl_sym_trans _ R s ending_state).
Proof.
move=> s; split.
  move=> ?; exact /clos_rt_clos_rst.
move /clos_rst_rst1n_iff.
remember ending_state.
move=> H; dependent induction H; first by apply /rt_refl.
case: H.
- move=> ?; apply /(rt_trans _ _ _ y); first exact: rt_step.
  exact: IHclos_refl_sym_trans_1n.
- move=> H1.
  have H2 : clos_refl_trans _ R y ending_state.
    rewrite -Heqa.
    exact: IHclos_refl_sym_trans_1n.
  case: (R_confluent _ _ _ (rt_step _ _ _ _ H1) H2) => w [] /[swap] ?.
  have ->: w = ending_state.
    rewrite -Heqa.
    apply: ending_state_is_dead_end.
    by rewrite Heqa.
  by rewrite Heqa.
Qed.

End StepToDeadendReversibility.
