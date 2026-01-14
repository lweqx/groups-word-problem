From HB Require Import structures.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec MM2_facts.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq.
From mathcomp Require Import eqtype fintype ssrnat div intdiv.
From mathcomp Require Import ring zify.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Stdlib.Program Require Import Equality.

From GWP Require Import ReductionUtils.

Record MM2_NON_NULL_HALTS_ON_ZERO_arguments := {
  mm2nnhoz_problem :> MM2_PROBLEM;
  mm2nnhoz_ne0: size mm2nnhoz_problem.1.1 > 0;
}.
Definition MM2_NON_NULL_HALTS_ON_ZERO := fun (args: MM2_NON_NULL_HALTS_ON_ZERO_arguments) =>
  MM2_HALTS_ON_ZERO (mm2nnhoz_problem args).

Lemma sizeE {T: Type} (l: seq T): size l = length l.
Proof. elim: l => //. Qed.

Module MM2NNReduction.
Section MM2NNReduction.

Variable P: MM2_PROBLEM.
Let M := P.1.1.

Definition M' := M ++ [:: mm2_inc_a].

Lemma M'_non_nil: size M' > 0.
Proof. rewrite size_cat /=; lia. Qed.

Definition reduction_output := {|
  mm2nnhoz_problem := (M', P.1.2, P.2);
  mm2nnhoz_ne0 := M'_non_nil;
|}.

Lemma step_forward x y:
  (mm2_step M) x y -> (mm2_step M') x y.
Proof.
rewrite /mm2_step; case=> instr [[l1 [l2 [H1 H2]]] ?].
exists instr; split=> //.
rewrite /M'.
exists l1; exists (l2 ++ [:: mm2_inc_a]).
rewrite H1 -catA; split=> //.
Qed.

Lemma steps_forward x y:
  clos_refl_trans _ (mm2_step M) x y
    ->
  clos_refl_trans _ (mm2_step M') x y.
Proof.
move=> H; dependent induction H.
- exact /rt_step /step_forward.
- exact: rt_refl.
- exact: (rt_trans _ _ _ y).
Qed.

Lemma step_back_propagates_property x y:
  MM2Notations.index y <= size M ->
  (mm2_step M') x y ->
  MM2Notations.index x <= size M.
Proof.
move=> H; case=> instr [/[swap] step].
move=> /[dup] /mm2_instr_at_bounds [].
rewrite -sizeE /M' size_cat /= => _ H1.
have /orP [/eqP H'|H'] := orbN (MM2Notations.index x == size M + 1); last lia.
rewrite {1}H'.
case=> l1; case=> l2 [] H2.
rewrite -sizeE -addnE => H3.
have {}H3: size l1 = size M by lia.
have H4: size M + 1 = size l1 + size l2 + 1.
  transitivity (size (M ++ [:: mm2_inc_a])).
    by rewrite size_cat.
  by rewrite H2 size_cat /=; lia.
have /size0nil H5: size l2 = 0 by lia.
move: H2; rewrite H5 => {}H5.
have: rcons M mm2_inc_a = rcons l1 instr.
  by rewrite -!cats1 H5.
move=> /rcons_inj [_ Hinstr].
move: step; rewrite -Hinstr => {}H5.
dependent induction H5.
have: i <= size M + 1; first by move: H1 => /=; lia.
move: H => /=.
lia.
Qed.

Lemma steps_back_propagate_property x y:
  MM2Notations.index y <= size M ->
  clos_refl_trans _ (mm2_step M') x y ->
  MM2Notations.index x <= size M.
Proof.
move=> /[swap] /clos_rt_rtn1_iff H; dependent induction H => //.
by move=> H'; have := step_back_propagates_property H' H.
Qed.

Lemma step_backward x y:
  MM2Notations.index y <= size M ->
  (mm2_step M') x y -> (mm2_step M) x y.
Proof.
move=> Hy H.
have Hx := step_back_propagates_property Hy H.
move: H; case=> instr [instr_at instr_step].
exists instr; split=> //.
move: instr_at; case=> l1 [l2] [] H' H''.
have: size l2 > 0.
  have: size M' = size l1 + size l2 + 1.
    by rewrite H' size_cat /=; lia.
  rewrite /M' size_cat /= => H.
  have {}H: size M = size l1 + size l2 by lia.
  move: Hx.
  rewrite -H'' -sizeE -addnE.
  lia.
case/lastP: l2 H' => [/=|l2 instr' H' _]; first lia.
have/rcons_inj [H _]: rcons M mm2_inc_a = rcons (l1 ++ instr::l2) instr'.
  rewrite -!cats1.
  move: H'; rewrite /M' => ->.
  by rewrite -cats1 -catA.
exists l1; exists l2; split=> //.
Qed.

Lemma steps_backward x y:
  MM2Notations.index y <= size M ->
  clos_refl_trans _ (mm2_step M') x y ->
  clos_refl_trans _ (mm2_step M) x y.
Proof.
move=> H H'; dependent induction H'.
- exact /rt_step /step_backward.
- exact: rt_refl.
- apply: (rt_trans _ _ _ y); last by exact: IHH'2.
  exact /IHH'1 /(steps_back_propagate_property H).
Qed.

End MM2NNReduction.
End MM2NNReduction.

Lemma MM2_NON_NULL_HALTS_ON_ZERO_reduction: MM2_HALTS_ON_ZERO ⪯ MM2_NON_NULL_HALTS_ON_ZERO.
Proof.
exists MM2NNReduction.reduction_output => [[[M x] y]]; split.
- rewrite /MM2_NON_NULL_HALTS_ON_ZERO /MM2_HALTS_ON_ZERO/= => H.
  exact: (@MM2NNReduction.steps_forward (M, x, y)).
- rewrite /MM2_NON_NULL_HALTS_ON_ZERO /MM2_HALTS_ON_ZERO/= => H.
  apply /(MM2NNReduction.steps_backward _ H) => /=.
  lia.
Qed.

Lemma MM2_NON_NULL_HALTS_ON_ZERO_undec: undecidable MM2_NON_NULL_HALTS_ON_ZERO.
Proof.
apply: (undecidability_from_reducibility MM2_HALTS_ON_ZERO_undec).
exact: MM2_NON_NULL_HALTS_ON_ZERO_reduction.
Qed.







Section LM2E_exploding.
(* Number of instructions in the machine. *)
Variable n: nat.
Hypothesis ne0: n > 0.

(* Instruction addresses, 0 = "program end" *)
Inductive lm2e_addr : Type :=
  | lm2e_addr_stop : lm2e_addr
  | lm2e_addr_instr : 'I_n -> lm2e_addr
  | lm2e_addr_boom : nat -> lm2e_addr.

Definition lm2e_addr_eq_op (a a': lm2e_addr) : bool := match (a, a') with
  | (lm2e_addr_stop, lm2e_addr_stop) => true
  | (lm2e_addr_instr pos, lm2e_addr_instr pos') => pos == pos'
  | (lm2e_addr_boom pos, lm2e_addr_boom pos') => pos == pos'
  | _ => false
  end.
Lemma lm2e_addr_eqP : Equality.axiom lm2e_addr_eq_op.
Proof.
move=> s s'; apply /(iffP idP).
- case: s; case: s' => //.
    by move=> i i' /eqP ->.
  by move=> i i' /eqP ->.
- move=> ->; case: s' => // [i|i].
    by rewrite /lm2e_addr_eq_op.
  by rewrite /lm2e_addr_eq_op.
Qed.
HB.instance Definition _ := hasDecEq.Build lm2e_addr lm2e_addr_eqP.

Inductive lm2e_instr : Type :=
  | lm2e_inc_x : lm2e_addr -> lm2e_instr
  | lm2e_inc_y : lm2e_addr -> lm2e_instr
  | lm2e_dec_x : lm2e_addr -> lm2e_addr -> lm2e_instr
  | lm2e_dec_y : lm2e_addr -> lm2e_addr -> lm2e_instr.

Record lm2e_machine := {
  einstructions :> seq lm2e_instr;
  emachine_length : size einstructions == n;
}.

Variable M: lm2e_machine.

Definition lm2e_state := (lm2e_addr * (nat * nat))%type.
Definition e_index (s: lm2e_state) := s.1.
Definition e_value_x (s: lm2e_state) := s.2.1.
Definition e_value_y (s: lm2e_state) := s.2.2.

Definition lm2e_dummy_instr: lm2e_instr.
Proof. exact /lm2e_inc_x /lm2e_addr_stop. Qed.

Definition lm2e_instr_at (pos: 'I_n) := nth lm2e_dummy_instr M pos.

Definition lm2e_step (s s': lm2e_state) := if e_index s is lm2e_addr_instr pos then (
    match lm2e_instr_at pos with
    | lm2e_inc_x i => (e_index s' == i) && (e_value_x s' == (e_value_x s).+1) && (e_value_y s' == e_value_y s)
    | lm2e_inc_y i => (e_index s' == i) && (e_value_x s' == e_value_x s) && (e_value_y s' == (e_value_y s).+1)
    | lm2e_dec_x i j => if e_value_x s is S n
        then (e_index s' == j) && (e_value_x s' == n) && (e_value_y s' == e_value_y s)
        else (e_index s' == i) && (e_value_x s' == 0) && (e_value_y s' == e_value_y s)
    | lm2e_dec_y i j => if e_value_y s is S n
        then (e_index s' == j) && (e_value_x s' == e_value_x s) && (e_value_y s' == n)
        else (e_index s' == i) && (e_value_x s' == e_value_x s) && (e_value_y s' == 0)
    end
  ) else False (* machine is stopped *).

Definition lm2e_initial_state (x y: nat) : lm2e_state.
Proof.
refine ((lm2e_addr_instr _), (x, y)).
exists 0.
exact: ne0.
Defined.

Definition lm2e_ending_state: lm2e_state := (lm2e_addr_stop, (0, 0)).

Definition LM2E_HALTS (x y: nat) :=
  clos_refl_trans _ lm2e_step (lm2e_initial_state x y) lm2e_ending_state.

End LM2E_exploding.
Arguments e_value_x _ _ /.
Arguments e_value_y _ _ /.

Record Lm2eHaltsArguments := {
  lm2e_halts_arguments_n: nat;
  lm2e_halts_arguments_ne0: (lm2e_halts_arguments_n > 0)%B;
  lm2e_halts_arguments_M: lm2e_machine lm2e_halts_arguments_n;
  lm2e_halts_arguments_x: nat;
  lm2e_halts_arguments_y: nat;
}.
Definition LM2E_HALTS_uncurried (args: Lm2eHaltsArguments) :=
  LM2E_HALTS (lm2e_halts_arguments_ne0 args) (lm2e_halts_arguments_M args) (lm2e_halts_arguments_x args) (lm2e_halts_arguments_y args).

Module LM2EReduction.
Section LM2EReduction.

Variable P: MM2_PROBLEM.
Let M := P.1.1.
Let initial_a := P.1.2.
Let initial_b := P.2.

Definition n := size M.

Notation lm2e_addr := (lm2e_addr n).
Notation lm2e_state := (lm2e_state n).
Notation mm2_step := (mm2_step M).

Hypothesis ne0 : n > 0.

Definition fallback_target_address (i: 'I_n) : lm2e_addr :=
  (* if we move to a out-of-bounds address, the machine explodes *)
  if \val (ordS i) == 0 then lm2e_addr_boom _ 0 else lm2e_addr_instr (ordS i).

Definition jump_target_address (i: nat) : lm2e_addr := match i with
  | 0 => lm2e_addr_stop _
  | i.+1 => if insub i is some i
      then lm2e_addr_instr i
      else lm2e_addr_boom _ (i.+1 - n.+1)
  end.

Definition translate_instruction (instr: mm2_instr) (i: 'I_n) := match instr with
  | mm2_inc_a => lm2e_inc_x (fallback_target_address i)
  | mm2_inc_b => lm2e_inc_y (fallback_target_address i)
  | mm2_dec_a j => lm2e_dec_x (fallback_target_address i) (jump_target_address j)
  | mm2_dec_b j => lm2e_dec_y (fallback_target_address i) (jump_target_address j)
  end.

Definition M'_instructions :=
  [seq translate_instruction (nth mm2_inc_a M (\val i)) i | i <- enum 'I_n ].

Lemma M'_machine_length : size M'_instructions == n.
Proof. by rewrite /M'_instructions size_map size_enum_ord. Qed.

Definition M': lm2e_machine n := {|
  einstructions := M'_instructions;
  emachine_length := M'_machine_length;
|}.

Let lm2e_step := (lm2e_step M').

Definition reduction_output : Lm2eHaltsArguments := {|
  lm2e_halts_arguments_n := n;
  lm2e_halts_arguments_ne0 := ne0;
  lm2e_halts_arguments_M := M';
  lm2e_halts_arguments_x := initial_a;
  lm2e_halts_arguments_y := initial_b;
|}.

Definition address_encoding (addr: lm2e_addr) : nat := match addr with
  | lm2e_addr_stop => 0
  | lm2e_addr_instr i => i.+1
  | lm2e_addr_boom i => i + n.+1
  end.

Definition mm2_state := (nat * (nat * nat))%type.

Definition state_encoding (s: lm2e_state) : mm2_state :=
  (address_encoding (e_index s), (e_value_x s, e_value_y s)).

Notation lm2e_ending_state := (lm2e_ending_state n).

Definition ord0: 'I_n.
Proof. exists 0; exact: ne0. Defined.

Definition ordlast: 'I_n.
Proof. exists n.-1; move: ne0; lia. Defined.

Lemma fallback_target_address_edge: address_encoding (fallback_target_address ordlast) = n.+1.
Proof. rewrite /fallback_target_address/= prednK ?ne0 ?modnn //=. Qed.

Lemma fallback_target_address_normal pos: pos != ordlast ->
  address_encoding (fallback_target_address pos) = pos.+2.
Proof.
move=> H.
have: \val (ordS pos) != 0.
  have <-: \val (ordS ordlast) = 0; first by rewrite /ordlast/= prednK ?modnn ?ne0 //.
  by rewrite (inj_eq val_inj) (inj_eq (ordS_inj (n:=n))).
rewrite /fallback_target_address.
move=> /negbTE -> /=.
rewrite modn_small => //.
have /=: \val pos != \val ordlast; last first.
  have := ltn_ord pos.
  lia.
by rewrite (inj_eq val_inj).
Qed.

Lemma jump_target_address_normal i: i <= n -> address_encoding (jump_target_address i) = i.
Proof. by case: i => //= i H; rewrite insubT /=. Qed.

Lemma mm_instr_at_nth (pos: 'I_n): mm2_instr_at (nth mm2_inc_a M pos) pos.+1 M.
Proof.
exists (take pos M); exists (drop pos.+1 M); split; last first.
  by rewrite -sizeE size_take ltn_ord; lia.
rewrite -{1}(cat_take_drop pos M).
have -> //: drop pos M = nth mm2_inc_a M pos :: drop pos.+1 M.
rewrite -{1}(cat_take_drop 1 (drop pos M)) drop_drop.
have ->: 1 + pos = pos.+1 by lia.
rewrite -cat1s.
have -> //: take 1 (drop pos M) = [:: nth mm2_inc_a M pos].
rewrite take_drop -(map_nth_iota0 mm2_inc_a _); last first.
  have := ltn_ord pos.
  rewrite /n.
  lia.
rewrite addnC iotaD map_cat.
rewrite drop_size_cat /=.
  by rewrite add0n.
by rewrite size_map size_iota.
Qed.

Lemma lm2eStep_to_mm2Step : forall s s',
  lm2e_step s s'
    ->
  mm2_step (state_encoding s) (state_encoding s').
Proof.
move=> [i [x y]] [i' [x' y']].
case: i => // i.
rewrite /lm2e_step/LM2.lm2e_step /=.
set instr := lm2e_instr_at M' i.
have: instr = lm2e_instr_at M' i by done.
case: instr => [
  j H /andP [/andP [/eqP -> /eqP ->] /eqP ->]|
  j H /andP [/andP [/eqP -> /eqP ->] /eqP ->]|
  j k H|j k H].
- exists mm2_inc_a => /=.
  move: H.
  rewrite /M'/lm2e_instr_at/=/M'_instructions/=.
  rewrite (nth_map ord0) /=; last first.
    rewrite size_enum_ord; exact: ltn_ord.
  rewrite nth_ord_enum.
  set M_instr := nth mm2_inc_a M i.
  have: M_instr = nth mm2_inc_a M i by done.
  case: M_instr => //= {1}-> H.
  injection H => -> {H}; split.
    exact: mm_instr_at_nth.
  rewrite /state_encoding/=.
  rewrite /fallback_target_address.
  have /orP [/[dup] {}H -> /=|/[dup] {}H /negbTE -> /=] := orbN (\val (ordS i) == 0).
    case: i H => /= i ? H.
    have /orP [/eqP ->|?] := orbN (i.+1 == n).
      by constructor.
    move: H.
    by rewrite modn_small; lia.
  rewrite modn_small; first constructor.
  move: H => /=.
  have /orP [/eqP ->|? _] := orbN (i.+1 == n).
    by rewrite modnn.
  by have := ltn_ord i; lia.
- exists mm2_inc_b => /=.
  move: H.
  rewrite /M'/lm2e_instr_at/=/M'_instructions/=.
  rewrite (nth_map ord0) /=; last first.
    rewrite size_enum_ord; exact: ltn_ord.
  rewrite nth_ord_enum.
  set M_instr := nth mm2_inc_a M i.
  have: M_instr = nth mm2_inc_a M i by done.
  case: M_instr => //= {1}-> H.
  injection H => -> {H}; split.
    exact: mm_instr_at_nth.
  rewrite /state_encoding/=.
  rewrite /fallback_target_address.
  have /orP [/[dup] {}H -> /=|/[dup] {}H /negbTE -> /=] := orbN (\val (ordS i) == 0).
    case: i H => /= i ? H.
    have /orP [/eqP ->|?] := orbN (i.+1 == n).
      by constructor.
    move: H.
    by rewrite modn_small; lia.
  rewrite modn_small; first constructor.
  move: H => /=.
  have /orP [/eqP ->|? _] := orbN (i.+1 == n).
    by rewrite modnn.
  by have := ltn_ord i; lia.
- move: H.
  rewrite /M'/lm2e_instr_at/=/M'_instructions/=.
  rewrite (nth_map ord0) /=; last first.
    rewrite size_enum_ord; exact: ltn_ord.
  rewrite nth_ord_enum.
  set M_instr := nth mm2_inc_a M i.
  have: M_instr = nth mm2_inc_a M i by done.
  case: M_instr => //= l Hinstr H.
  case: x => [/andP [/andP [/eqP -> /eqP ->] /eqP ->]|x /andP [/andP [/eqP -> /eqP ->] /eqP ->]].
    exists (mm2_dec_a l); split.
      rewrite Hinstr.
      exact: mm_instr_at_nth.
    injection H => {H} {Hinstr} _ ->.
    rewrite /state_encoding/= /fallback_target_address.
    have /orP [/[dup] {}H -> /=|/[dup] {}H /negbTE -> /=] := orbN (\val (ordS i) == 0).
      case: i H => /= i ? H.
      have /orP [/eqP ->|?] := orbN (i.+1 == n).
        by constructor.
      move: H.
      by rewrite modn_small; lia.
    rewrite modn_small; first constructor.
    move: H => /=.
    have /orP [/eqP ->|? _] := orbN (i.+1 == n).
      by rewrite modnn.
    by have := ltn_ord i; lia.
  injection H => {H} -> _.
  case: l Hinstr => [Hinstr /=|l Hinstr /=].
    exists (mm2_dec_a 0); split.
      rewrite Hinstr.
      exact: mm_instr_at_nth.
    rewrite /state_encoding/=.
    by constructor.
  case: insubP => [l' ? l'_eq|?].
    exists (mm2_dec_a l.+1); split.
      rewrite Hinstr.
      exact: mm_instr_at_nth.
    rewrite /state_encoding/= l'_eq.
    by constructor.
  exists (mm2_dec_a l.+1); split.
    rewrite Hinstr.
    exact: mm_instr_at_nth.
  rewrite /state_encoding/=.
  have ->: l.+1 - n.+1 + n.+1 = l.+1 by lia.
  by constructor.
- move: H.
  rewrite /M'/lm2e_instr_at/=/M'_instructions/=.
  rewrite (nth_map ord0) /=; last first.
    rewrite size_enum_ord; exact: ltn_ord.
  rewrite nth_ord_enum.
  set M_instr := nth mm2_inc_a M i.
  have: M_instr = nth mm2_inc_a M i by done.
  case: M_instr => //= l Hinstr H.
  case: y => [/andP [/andP [/eqP -> /eqP ->] /eqP ->]|y /andP [/andP [/eqP -> /eqP ->] /eqP ->]].
    exists (mm2_dec_b l); split.
      rewrite Hinstr.
      exact: mm_instr_at_nth.
    injection H => {H} {Hinstr} _ ->.
    rewrite /state_encoding/= /fallback_target_address.
    have /orP [/[dup] {}H -> /=|/[dup] {}H /negbTE -> /=] := orbN (\val (ordS i) == 0).
      case: i H => /= i ? H.
      have /orP [/eqP ->|?] := orbN (i.+1 == n).
        by constructor.
      move: H.
      by rewrite modn_small; lia.
    rewrite modn_small; first constructor.
    move: H => /=.
    have /orP [/eqP ->|? _] := orbN (i.+1 == n).
      by rewrite modnn.
    by have := ltn_ord i; lia.
  injection H => {H} -> _.
  case: l Hinstr => [Hinstr /=|l Hinstr /=].
    exists (mm2_dec_b 0); split.
      rewrite Hinstr.
      exact: mm_instr_at_nth.
    rewrite /state_encoding/=.
    by constructor.
  case: insubP => [l' ? l'_eq|?].
    exists (mm2_dec_b l.+1); split.
      rewrite Hinstr.
      exact: mm_instr_at_nth.
    rewrite /state_encoding/= l'_eq.
    by constructor.
  exists (mm2_dec_b l.+1); split.
    rewrite Hinstr.
    exact: mm_instr_at_nth.
  rewrite /state_encoding/=.
  have ->: l.+1 - n.+1 + n.+1 = l.+1 by lia.
  by constructor.
Qed.

Lemma lm2eInstrAt_when_mm2InstrAt instr (pos: 'I_n) :
  mm2_instr_at instr pos.+1 M ->
  (translate_instruction instr pos) = lm2e_instr_at M' pos.
Proof.
case=> l1 [l2]; case.
rewrite /lm2e_instr_at /M' /= /M'_instructions.
rewrite (nth_map ord0) /=; last first.
  rewrite size_enum_ord; exact: ltn_ord.
rewrite nth_ord_enum => -> /eq_add_S <-.
rewrite nth_cat -sizeE.
have /negbTE ->: ~~ (size l1 < size l1) by lia.
by have ->: size l1 - size l1 = 0 by lia.
Qed.

Lemma mm2_instr_at_bound instr pos :
  mm2_instr_at instr pos M -> 0 < pos <= n.
Proof.
case=> l1; case=> l2; case=> M_eq.
have: size M = size (l1 ++ (instr :: l2)).
  by rewrite M_eq size_cat /=.
rewrite size_cat /= -sizeE.
by rewrite /n => -> <-; lia.
Qed.

Lemma mm2_instr_at_address_encoding instr i:
  mm2_instr_at instr (address_encoding i) M ->
  exists pos, lm2e_addr_instr pos = i /\ address_encoding i = pos.+1.
Proof.
case=> l1; case=> l2; case=> M_eq H.
have Hpos: length l1 < n.
  have: size M = size (l1 ++ (instr :: l2)).
    by rewrite M_eq size_cat /=.
  by rewrite size_cat /= -sizeE /n; lia.
move: H; elim: i => /=; [done|move=> i _|lia]; last first.
by exists i.
Qed.

Lemma mm2Step_to_lm2eStep : forall s s',
  mm2_step (state_encoding s) (state_encoding s') -> lm2e_step s s'.
Proof.
move=> [i [x y]] [i' [x' y']] []; elim.
- case=> /= instr_at H; dependent induction H.
  move: (instr_at) => /mm2_instr_at_address_encoding [i'' [{2}<-]] H.
  move: instr_at; rewrite H => /lm2eInstrAt_when_mm2InstrAt.
  rewrite /lm2e_step0/LM2.lm2e_step/= => <-.
  move: x; rewrite {}H.
  case: i' => //= [i' /eq_add_S H|i' H]; last first.
    have /eqP: \val i'' = \val ordlast; first by have ? /= := ltn_ord i''; lia.
    have ->: i' = 0; first by have ? /= := ltn_ord i''; lia.
    rewrite (inj_eq val_inj) => /eqP ->.
    rewrite /fallback_target_address /=.
    have ->: n.-1.+1 = n by move: ne0; lia.
    by rewrite modnn /= !eq_refl.
  rewrite /fallback_target_address/= H.
  rewrite modn_small; last by rewrite ltn_ord.
  have /negbTE ->: \val i' != 0 by move: H => /= <-; lia.
  have ->: ordS i'' = i'; last first.
    by rewrite !eq_refl.
  apply /eqP.
  by rewrite -(inj_eq (@ord_inj n)) /= H modn_small.
- case=> /= instr_at H; dependent induction H.
  move: (instr_at) => /mm2_instr_at_address_encoding [i'' [{2}<-]] H.
  move: instr_at; rewrite H => /lm2eInstrAt_when_mm2InstrAt.
  rewrite /lm2e_step0/LM2.lm2e_step/= => <-.
  move: x; rewrite {}H.
  case: i' => //= [i' /eq_add_S H|i' H]; last first.
    have /eqP: \val i'' = \val ordlast; first by have ? /= := ltn_ord i''; lia.
    have ->: i' = 0; first by have ? /= := ltn_ord i''; lia.
    rewrite (inj_eq val_inj) => /eqP ->.
    rewrite /fallback_target_address /=.
    have ->: n.-1.+1 = n by move: ne0; lia.
    by rewrite modnn /= !eq_refl.
  rewrite /fallback_target_address/= H.
  rewrite modn_small; last by rewrite ltn_ord.
  have /negbTE ->: \val i' != 0 by move: H => /= <-; lia.
  have ->: ordS i'' = i'; last first.
    by rewrite !eq_refl.
  apply /eqP.
  by rewrite -(inj_eq (@ord_inj n)) /= H modn_small.
- move=> j; case=> /= instr_at H; dependent induction H.
  move: (instr_at) => /mm2_instr_at_address_encoding [i'' [{2}<-]] H.
  move: instr_at; rewrite H => /lm2eInstrAt_when_mm2InstrAt.
  rewrite /lm2e_step0/LM2.lm2e_step/= => <-.
  case: i' => /= [|n| l]; rewrite ?valK ?insubN ?eq_refl //.
  rewrite /jump_target_address.
  have ->: l + n.+1 = (l + n).+1 by lia.
  rewrite insubN; last by lia.
  have ->: (l + n).+1 - n.+1 = l by lia.
  by rewrite eq_refl.
- move: (instr_at) => /mm2_instr_at_address_encoding [i'' [{2}<-]] H.
  move: instr_at; rewrite H => /lm2eInstrAt_when_mm2InstrAt.
  rewrite /lm2e_step0/LM2.lm2e_step/= => <-.
  move: x; rewrite {}H.
  case: i' => //= [i' /eq_add_S H|i' H]; last first.
    have /eqP: \val i'' = \val ordlast; first by have ? /= := ltn_ord i''; lia.
    have ->: i' = 0; first by have ? /= := ltn_ord i''; lia.
    rewrite (inj_eq val_inj) => /eqP ->.
    rewrite /fallback_target_address /=.
    have ->: n.-1.+1 = n by move: ne0; lia.
    by rewrite modnn /= !eq_refl.
  rewrite /fallback_target_address/= H.
  rewrite modn_small; last by rewrite ltn_ord.
  have /negbTE ->: \val i' != 0 by move: H => /= <-; lia.
  have ->: ordS i'' = i'; last first.
    by rewrite !eq_refl.
  apply /eqP.
  by rewrite -(inj_eq (@ord_inj n)) /= H modn_small.
- move=> j; case=> /= instr_at H; dependent induction H.
  move: (instr_at) => /mm2_instr_at_address_encoding [i'' [{2}<-]] H.
  move: instr_at; rewrite H => /lm2eInstrAt_when_mm2InstrAt.
  rewrite /lm2e_step0/LM2.lm2e_step/= => <-.
  case: i' => /= [|n|l]; rewrite ?valK ?insubN ?eq_refl //.
  rewrite /jump_target_address.
  have ->: l + n.+1 = (l + n).+1 by lia.
  rewrite insubN; last by lia.
  have ->: (l + n).+1 - n.+1 = l by lia.
  by rewrite eq_refl.
- move: (instr_at) => /mm2_instr_at_address_encoding [i'' [{2}<-]] H.
  move: instr_at; rewrite H => /lm2eInstrAt_when_mm2InstrAt.
  rewrite /lm2e_step0/LM2.lm2e_step/= => <-.
  move: x; rewrite {}H.
  case: i' => //= [i' /eq_add_S H|i' H]; last first.
    have /eqP: \val i'' = \val ordlast; first by have ? /= := ltn_ord i''; lia.
    have ->: i' = 0; first by have ? /= := ltn_ord i''; lia.
    rewrite (inj_eq val_inj) => /eqP ->.
    rewrite /fallback_target_address /=.
    have ->: n.-1.+1 = n by move: ne0; lia.
    by rewrite modnn /= !eq_refl.
  rewrite /fallback_target_address/= H.
  rewrite modn_small; last by rewrite ltn_ord.
  have /negbTE ->: \val i' != 0 by move: H => /= <-; lia.
  have ->: ordS i'' = i'; last first.
    by rewrite !eq_refl.
  apply /eqP.
  by rewrite -(inj_eq (@ord_inj n)) /= H modn_small.
Qed.

Lemma mm2Step_equiv_lm2eStep : forall s s',
  mm2_step (state_encoding s) (state_encoding s')
    <->
  lm2e_step s s'.
Proof.
move=> s s'; split.
- exact: mm2Step_to_lm2eStep.
- exact: lm2eStep_to_mm2Step.
Qed.

Lemma state_encoding_inj x y:
  state_encoding x = state_encoding y -> x = y.
Proof.
case: x => [i [a b]].
case: y => [i' [a' b']].
case: i => [|i|i]; case: i' => [|i'|i']; try by case; lia.
- by case=> -> ->.
- case=> /eqP.
  by rewrite (inj_eq (@ord_inj n)) => /eqP -> -> ->.
- case.
  have := ltn_ord i.
  lia.
- case.
  have := ltn_ord i'.
  lia.
- case=> H.
  have {H} ->: i = i' by lia.
  by move=> -> ->.
Qed.

Lemma inv_addr_encoding i:
  exists i', address_encoding i' = i.
Proof.
case: i => [|i].
  by exists (lm2e_addr_stop _).
have /orP [H|?] := orbN (i < n).
  by exists (lm2e_addr_instr (Ordinal H)).
exists (lm2e_addr_boom _ (i - n)) => /=.
lia.
Qed.  

Lemma mm2Step_preserves_encoding_right: forall s x',
    mm2_step (state_encoding s) x' -> exists s', state_encoding s' = x'.
Proof.
move=> [i [a b]] [i' [a' b']].
case=> [instr [_]].
elim: instr => /= [| |l|l]; elim; do [
  move=> i'' a'' b'' /=;
  case: (inv_addr_encoding i''.+1) => j H;
  exists (j, (a''.+1, b''));
  by rewrite /state_encoding/= H
    |
  move=> i'' a'' b'' /=;
  case: (inv_addr_encoding i''.+1) => j H;
  exists (j, (a'', b''.+1));
  by rewrite /state_encoding/= H
    |
  move=> _ i'' a'' b'' /=;
  case: (inv_addr_encoding i'') => j H;
  exists (j, (a'', b''));
  by rewrite /state_encoding/= H
    |
  move=> _ i'' a'' b'' /=;
  case: (inv_addr_encoding i'') => j H;
  exists (j, (a'', b''));
  by rewrite /state_encoding/= H
    |
  move=> k _ b'' /=;
  case: (inv_addr_encoding k.+1) => j H;
  exists (j, (0, b''));
  by rewrite /state_encoding/= H
    |
  move=> k _ a'' /=;
  case: (inv_addr_encoding k.+1) => j H;
  exists (j, (a'', 0));
  by rewrite /state_encoding/= H
].
Qed.

Lemma mm2Steps_equiv_lm2eSteps: forall s s' : lm2e_state,
  clos_refl_trans _ mm2_step (state_encoding s) (state_encoding s') <->
  clos_refl_trans _ lm2e_step s s'.
Proof.
exact: (closRT_R_equiv_R' _ _ mm2_step lm2e_step state_encoding
  state_encoding_inj
  mm2Step_equiv_lm2eStep
  mm2Step_preserves_encoding_right).
Qed.

End LM2EReduction.
End LM2EReduction.

Lemma LM2E_HALTS_reduction : MM2_NON_NULL_HALTS_ON_ZERO ⪯ LM2E_HALTS_uncurried.
Proof.
exists (fun args => LM2EReduction.reduction_output (mm2nnhoz_ne0 args)) => [[[[M x] y]] /= ne0].
split.
- rewrite /LM2EReduction.reduction_output/=.
  rewrite /LM2E_HALTS_uncurried /LM2E_HALTS /=.
  by rewrite -LM2EReduction.mm2Steps_equiv_lm2eSteps.
- rewrite /LM2EReduction.reduction_output/=.
  rewrite /LM2E_HALTS_uncurried /LM2E_HALTS /=.
  by rewrite -LM2EReduction.mm2Steps_equiv_lm2eSteps.
Qed.

Lemma LM2E_HALTS_undec : undecidable LM2E_HALTS_uncurried.
apply: (undecidability_from_reducibility MM2_NON_NULL_HALTS_ON_ZERO_undec).
exact: LM2E_HALTS_reduction.
Qed.












Section LM2.
(* Number of instructions in the machine. *)
Variable n: nat.
Hypothesis machine_non_empty: (n > 0)%N.

(* Instruction addresses, 0 = "program end" *)
Inductive lm2_addr : Type :=
  | lm2_addr_stop : lm2_addr
  | lm2_addr_instr : 'I_n -> lm2_addr.

Definition lm2_addr_eq_op (a a': lm2_addr) : bool := match (a, a') with
  | (lm2_addr_stop, lm2_addr_stop) => true
  | (lm2_addr_instr pos, lm2_addr_instr pos') => pos == pos'
  | _ => false
  end.
Lemma lm2_addr_eqP : Equality.axiom lm2_addr_eq_op.
Proof.
move=> s s'; apply /(iffP idP).
- case: s; case: s' => //.
  by move=> i i' /eqP ->.
- move=> ->; case: s' => //.
  move=> i.
  by rewrite /lm2_addr_eq_op.
Qed.
HB.instance Definition _ := hasDecEq.Build lm2_addr lm2_addr_eqP.

Inductive lm2_instr : Type :=
  | lm2_inc_x : lm2_addr -> lm2_instr
  | lm2_inc_y : lm2_addr -> lm2_instr
  | lm2_dec_x : lm2_addr -> lm2_addr -> lm2_instr
  | lm2_dec_y : lm2_addr -> lm2_addr -> lm2_instr.

Record lm2_machine := {
  instructions :> seq lm2_instr;
  machine_length : size instructions == n;
}.

Variable M: lm2_machine.

Definition lm2_state := (lm2_addr * (nat * nat))%type.
Definition index (s: lm2_state) := s.1.
Definition value_x (s: lm2_state) := s.2.1.
Definition value_y (s: lm2_state) := s.2.2.

Definition lm2_dummy_instr: lm2_instr.
Proof. exact /lm2_inc_x /lm2_addr_stop. Qed.

Definition lm2_instr_at (pos: 'I_n) := nth lm2_dummy_instr M pos.

Definition lm2_step (s s': lm2_state) := if index s is lm2_addr_instr pos then (
    match lm2_instr_at pos with
    | lm2_inc_x i => (index s' == i) && (value_x s' == (value_x s).+1) && (value_y s' == value_y s)
    | lm2_inc_y i => (index s' == i) && (value_x s' == value_x s) && (value_y s' == (value_y s).+1)
    | lm2_dec_x i j => if value_x s is S n
        then (index s' == j) && (value_x s' == n) && (value_y s' == value_y s)
        else (index s' == i) && (value_x s' == 0) && (value_y s' == value_y s)
    | lm2_dec_y i j => if value_y s is S n
        then (index s' == j) && (value_x s' == value_x s) && (value_y s' == n)
        else (index s' == i) && (value_x s' == value_x s) && (value_y s' == 0)
    end
  ) else False (* machine is stopped *).

Definition lm2_initial_state (x y: nat) : lm2_state.
Proof.
apply: pair.
  apply: lm2_addr_instr.
  by exists 0.
exact: (x, y).
Defined.

Definition lm2_ending_state: lm2_state := (lm2_addr_stop, (0, 0)).

Definition LM2_HALTS (x y: nat) :=
  clos_refl_trans _ lm2_step (lm2_initial_state x y) lm2_ending_state.

End LM2.
Arguments value_x _ _ /.
Arguments value_y _ _ /.

Record Lm2HaltsArguments := {
  lm2_halts_arguments_n: nat;
  lm2_halts_arguments_M: lm2_machine lm2_halts_arguments_n;
  lm2_halts_arguments_ne0: (0 < lm2_halts_arguments_n)%N;
  lm2_halts_arguments_x: nat;
  lm2_halts_arguments_y: nat;
}.
Definition LM2_HALTS_uncurried (args: Lm2HaltsArguments) :=
  LM2_HALTS (lm2_halts_arguments_ne0 args) (lm2_halts_arguments_M args) (lm2_halts_arguments_x args) (lm2_halts_arguments_y args).

Module LM2Reduction.
Section LM2Reduction.

Variable args: Lm2eHaltsArguments.

Let n := lm2e_halts_arguments_n args.
Let M := lm2e_halts_arguments_M args.
Let a := lm2e_halts_arguments_x args.
Let b := lm2e_halts_arguments_y args.

Let n_encoded := n.+1.

Lemma n_encoded_wider: n <= n_encoded.
Proof. lia. Qed.

Lemma n_encoded_pos: n_encoded > 0.
Proof. by rewrite /n_encoded. Defined.

Notation lm2_addr := (lm2_addr n_encoded).
Notation lm2_state := (lm2_state n_encoded).
Notation lm2e_addr := (lm2e_addr n).
Notation lm2e_instr := (lm2e_instr n).
Notation lm2e_state := (lm2e_state n).

Definition ord_n: 'I_(n_encoded).
Proof. by exists n; lia. Defined.

Definition lm2_boom_encoding: lm2_addr.
Proof.
apply lm2_addr_instr.
exact: ord_n.
Defined.

Definition translate_addr (addr: lm2e_addr) := match addr with
  | lm2e_addr_stop => lm2_addr_stop _
  | lm2e_addr_instr i => lm2_addr_instr (widen_ord n_encoded_wider i)
  | lm2e_addr_boom i => lm2_boom_encoding
  end.

Definition translate_instruction (instr: lm2e_instr) := match instr with
  | lm2e_inc_x i => lm2_inc_x (translate_addr i)
  | lm2e_inc_y i => lm2_inc_y (translate_addr i)
  | lm2e_dec_x i j => lm2_dec_x (translate_addr i) (translate_addr j)
  | lm2e_dec_y i j => lm2_dec_y (translate_addr i) (translate_addr j)
  end.

Definition M'_instructions := [seq translate_instruction instr | instr <- (einstructions M) ]
  ++ [:: lm2_inc_x lm2_boom_encoding ].

Lemma M'_machine_length : size M'_instructions == n_encoded.
Proof. rewrite /M'_instructions size_cat size_map /=.
have /eqP -> := emachine_length M.
lia.
Qed.

Definition M': lm2_machine n_encoded := {|
  instructions := M'_instructions;
  machine_length := M'_machine_length;
|}.

Let lm2_step := (lm2_step M').
Let lm2e_step := (lm2e_step M).

Definition state_encoding (s: lm2e_state) :=
  let '(i, (a, b)) := s in (translate_addr i, (a, b)).

Lemma lm2eStep_to_lm2Step : forall s s',
  lm2e_step s s'
    ->
  lm2_step (state_encoding s) (state_encoding s').
Proof.
move=> [i [x y]] [i' [x' y']].
rewrite /lm2e_step/LM2.lm2e_step/=.
rewrite /lm2_step/LM2.lm2_step/=.
case: i => //= i.
rewrite /lm2_instr_at/lm2e_instr_at/=/M'_instructions.
rewrite nth_cat size_map (eqP (emachine_length M)) (ltn_ord i).
rewrite (nth_map (lm2e_dummy_instr _)); last first.
  by rewrite (eqP (emachine_length M)) (ltn_ord i).
case: (nth (lm2e_dummy_instr n) M i).
- move=> l /= /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /eqP ->.
  by rewrite !eq_refl.
- move=> l /= /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /eqP ->.
  by rewrite !eq_refl.
- move=> l j.
  case: x => [|x].
    move=> /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /eqP -> /=.
    by rewrite !eq_refl.
  move=> /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /eqP -> /=.
  by rewrite !eq_refl.
- move=> l j.
  case: y => [|y].
    move=> /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /eqP -> /=.
    by rewrite !eq_refl.
  move=> /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /eqP -> /=.
  by rewrite !eq_refl.
Qed.

Lemma lm2Step_to_lm2eStep : forall s s',
  index (state_encoding s') != lm2_boom_encoding
    ->
  lm2_step (state_encoding s) (state_encoding s')
    ->
  lm2e_step s s'.
Proof.
move=> [i [x y]] [i' [x' y']] /=.
rewrite /lm2_step/LM2.lm2_step/=.
rewrite /lm2e_step/LM2.lm2e_step/=.
rewrite /lm2_instr_at/M'/=/M'_instructions.
rewrite /lm2e_instr_at/M'/=/M'_instructions.
case: i => //= i.
case: i' => [/= _|i' /= _|i']; last by rewrite eq_refl.
- rewrite nth_cat size_map (eqP (emachine_length M)) (ltn_ord i).
  rewrite (nth_map (lm2e_dummy_instr _)); last first.
    by rewrite (eqP (emachine_length M)) (ltn_ord i).
  case: (nth (lm2e_dummy_instr n) M i) => /=.
  - by elim=> //=.
  - by elim=> //=.
  - by case: x => [|x _]; elim=> //=.
  - by case: y => [|y _]; elim=> //=.
- rewrite nth_cat size_map (eqP (emachine_length M)) (ltn_ord i).
  rewrite (nth_map (lm2e_dummy_instr _)); last first.
    by rewrite (eqP (emachine_length M)) (ltn_ord i).
  case: (nth (lm2e_dummy_instr n) M i) => /=.
  - elim=> //= _.
    rewrite /lm2_boom_encoding => /andP [/andP []] /eqP H.
    injection H => {}H.
    have := ltn_ord i'.
    by rewrite H; lia.
  - elim=> //= _.
    rewrite /lm2_boom_encoding => /andP [/andP []] /eqP H.
    injection H => {}H.
    have := ltn_ord i'.
    by rewrite H; lia.
  - case: x => [|x _].
    - elim=> //= _ _.
      rewrite /lm2_boom_encoding => /andP [/andP []] /eqP H.
      injection H => {}H.
      have := ltn_ord i'.
      by rewrite H; lia.
    elim=> //= _.
    rewrite /lm2_boom_encoding => /andP [/andP []] /eqP H.
    injection H => {}H.
    have := ltn_ord i'.
    by rewrite H; lia.
  - case: y => [|y _].
    - elim=> //= _ _.
      rewrite /lm2_boom_encoding => /andP [/andP []] /eqP H.
      injection H => {}H.
      have := ltn_ord i'.
      by rewrite H; lia.
    elim=> //= _.
    rewrite /lm2_boom_encoding => /andP [/andP []] /eqP H.
    injection H => {}H.
    have := ltn_ord i'.
    by rewrite H; lia.
- rewrite nth_cat size_map (eqP (emachine_length M)).
  have /negbTE -> : ~~ (n < n) by lia.
  have -> /=: n - n = 0 by lia.
  by move=> /[swap] /andP [/andP []] ->.
Qed.

Lemma lm2eSteps_to_lm2Steps : forall s s',
  clos_refl_trans _ lm2e_step s s'
    ->
  clos_refl_trans _ lm2_step (state_encoding s) (state_encoding s').
Proof.
move=> s s' H; dependent induction H.
- exact /rt_step /lm2eStep_to_lm2Step.
- exact /rt_refl.
- exact /(rt_trans _ _ _ (state_encoding y)).
Qed.

Lemma translate_addr_injective: forall i i',
  translate_addr i' != lm2_boom_encoding ->
  translate_addr i = translate_addr i' -> i = i'.
Proof.
elim=> [|i|i].
- by elim=> //.
- elim=> //= j _ H; injection H => /eqP.
    by rewrite (inj_eq (@ord_inj n)) => /eqP ->.
  by have := ltn_ord i; lia.
- elim=> //= j H' H.
    injection H.
    by have := ltn_ord j; lia.
  move: H'.
  by rewrite eq_refl.
Qed.

Lemma state_encoding_injective: forall s s',
  index (state_encoding s') != lm2_boom_encoding
    ->
  state_encoding s = state_encoding s' -> s = s'.
Proof.
move=> [i [x y]] [i' [x' y']] /=.
move=> H' [].
by elim: i => [|i|i]; move=> /(translate_addr_injective H') {H'} -> -> ->.
Qed.

Lemma lm2Step_preserve_encoding: forall (s : lm2e_state) (x' : lm2_state),
  lm2_step (state_encoding s) x' -> exists s' : lm2e_state, state_encoding s' = x'.
Proof.
move=> [i [x y]] x'.
rewrite /lm2_step/LM2.lm2_step/=.
case: i => //= i; last first.
  rewrite /lm2_instr_at/=/M'_instructions/=.
  rewrite nth_cat size_map (eqP (emachine_length M)).
  have /negbTE ->: ~~ (n < n) by lia.
  have -> /=: (n - n = 0) by lia.
  move=> /andP [/andP [/eqP H1 /eqP H2] /eqP H3].
  exists (lm2e_addr_boom _ 0, (x.+1, y)).
  rewrite /state_encoding -{}H2 -{}H3 /= -{}H1.
  by case: x' => ? [? ?] /=.
rewrite /lm2_instr_at/=/M'_instructions/=.
rewrite nth_cat size_map (eqP (emachine_length M)) (ltn_ord _).
rewrite (nth_map (lm2e_dummy_instr _)); last first.
  by rewrite (eqP (emachine_length M)) (ltn_ord _).
case: (nth (lm2e_dummy_instr _) M i) => /=.
- move=> j /andP [/andP [/eqP H1 /eqP H2] /eqP H3].
  exists (j, (x.+1, y)).
  rewrite /state_encoding -{}H1 -{}H2 -{}H3.
  by case: x' => ? [? ?] /=.
- move=> j /andP [/andP [/eqP H1 /eqP H2] /eqP H3].
  exists (j, (x, y.+1)).
  rewrite /state_encoding -{}H1 -{}H2 -{}H3.
  by case: x' => ? [? ?] /=.
- case: x => [|x].
    move=> j l /andP [/andP [/eqP H1 /eqP H2] /eqP H3].
    exists (j, (0, y)).
    rewrite /state_encoding -{}H1 -{}H2 -{}H3.
    by case: x' => ? [? ?] /=.
  move=> j l /andP [/andP [/eqP H1 /eqP H2] /eqP H3].
  exists (l, (x, y)).
  rewrite /state_encoding -{}H1 -{}H2 -{}H3.
  by case: x' => ? [? ?] /=.
- case: y => [|y].
    move=> j l /andP [/andP [/eqP H1 /eqP H2] /eqP H3].
    exists (j, (x, 0)).
    rewrite /state_encoding -{}H1 -{}H2 -{}H3.
    by case: x' => ? [? ?] /=.
  move=> j l /andP [/andP [/eqP H1 /eqP H2] /eqP H3].
  exists (l, (x, y)).
  rewrite /state_encoding -{}H1 -{}H2 -{}H3.
  by case: x' => ? [? ?] /=.
Qed.

Lemma lm2Step_backpropagates: forall x y : lm2_state,
  index y != lm2_boom_encoding -> lm2_step x y -> index x != lm2_boom_encoding.
Proof.
move=> [i [x y]] [i' [x' y']] /=.
rewrite /lm2_step/LM2.lm2_step/=.
case: i => i //.
rewrite /M'/lm2_instr_at/=/M'_instructions.
rewrite nth_cat size_map (eqP (emachine_length M)).
have /orP [/= /eqP ->|] := orbN (\val i == n).
  have /negbTE ->: ~~(n < n) by lia.
  have -> /=: n - n = 0 by lia.
  lia.
do 2 ! move=> /[swap] _.
apply /contra => /eqP H.
by injection H => ->.
Qed.

Lemma lm2Steps_to_lm2eSteps : forall s s',
  index (state_encoding s') != lm2_boom_encoding
    ->
  clos_refl_trans _ lm2_step (state_encoding s) (state_encoding s')
    ->
  clos_refl_trans _ lm2e_step s s'.
Proof.
apply: (clos_rt_impl_with_cond _ _ (fun x => index x != lm2_boom_encoding)).
- exact: state_encoding_injective.
- exact: lm2Step_to_lm2eStep.
- exact: lm2Step_preserve_encoding.
- exact: lm2Step_backpropagates.
Qed.

Definition reduction_output: Lm2HaltsArguments := {|
  lm2_halts_arguments_n := n_encoded;
  lm2_halts_arguments_M := M';
  lm2_halts_arguments_ne0 := n_encoded_pos;
  lm2_halts_arguments_x := a;
  lm2_halts_arguments_y := b;
|}.

End LM2Reduction.
End LM2Reduction.

Lemma LM2_HALTS_reduction : LM2E_HALTS_uncurried ⪯ LM2_HALTS_uncurried.
Proof.
exists LM2Reduction.reduction_output => [x]; split.
- rewrite /LM2_HALTS_uncurried /LM2_HALTS /=.
  rewrite /LM2E_HALTS_uncurried /LM2E_HALTS /=.
  move=> H.
  have /= := @LM2Reduction.lm2eSteps_to_lm2Steps x (lm2e_initial_state _ _ _) (lm2e_ending_state _) H.
  have -> //: widen_ord (LM2Reduction.n_encoded_wider x) (Ordinal (lm2e_halts_arguments_ne0 x)) = Ordinal (LM2Reduction.n_encoded_pos x).
  by apply /eqP.
  rewrite /LM2Reduction.n_encoded_wider/=.
- rewrite /LM2_HALTS_uncurried /LM2_HALTS /=.
  rewrite /LM2E_HALTS_uncurried /LM2E_HALTS /=.
  move=> H.
  apply: (@LM2Reduction.lm2Steps_to_lm2eSteps x (lm2e_initial_state _ _ _) (lm2e_ending_state _) isT).
  rewrite /lm2e_initial_state/=.
  have -> //: widen_ord (LM2Reduction.n_encoded_wider x) (Ordinal (lm2e_halts_arguments_ne0 x)) = Ordinal (LM2Reduction.n_encoded_pos x).
  by apply /eqP.
Qed.

Lemma LM2_HALTS_undec : undecidable LM2_HALTS_uncurried.
apply: (undecidability_from_reducibility LM2E_HALTS_undec).
exact: LM2_HALTS_reduction.
Qed.
