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

Section LM2E_exploding.
(* Number of instructions in the machine. *)
Variable n: nat.
Hypothesis machine_non_empty: (n > 0)%N.

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
apply: pair.
  apply: lm2e_addr_instr.
  by exists 0.
exact: (x, y).
Qed.

Definition lm2e_ending_state: lm2e_state := (lm2e_addr_stop, (0, 0)).

Definition LM2E_HALTS (x y: nat) :=
  clos_refl_trans _ lm2e_step (lm2e_initial_state x y) lm2e_ending_state.

End LM2E_exploding.
Arguments e_value_x _ _ /.
Arguments e_value_y _ _ /.

Record Lm2eHaltsArguments := {
  lm2e_halts_arguments_n: nat;
  lm2e_halts_arguments_M: lm2e_machine lm2e_halts_arguments_n;
  lm2e_halts_arguments_ne0: (0 < lm2e_halts_arguments_n)%N;
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

(* TODO: do a case analysis whether the machine is empty *)
Definition ne0 : n > 0.
Admitted.

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
  lm2e_halts_arguments_M := M';
  lm2e_halts_arguments_ne0 := ne0;
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

Lemma sizeE {T: Type} (l: seq T): size l = length l.
Proof. elim: l => //. Qed.

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
Admitted.

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
    case: i H => /= i ? ?.
    have ->: i.+1 = n by admit.
    by constructor.
  rewrite modn_small; first constructor.
  admit.
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
    case: i H => /= i ? ?.
    have ->: i.+1 = n by admit.
    by constructor.
  rewrite modn_small; first constructor.
  admit.
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
      case: i H => /= i ? ?.
      have ->: i.+1 = n by admit.
      by constructor.
    rewrite modn_small; first constructor.
    admit.
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
      case: i H => /= i ? ?.
      have ->: i.+1 = n by admit.
      by constructor.
    rewrite modn_small; first constructor.
    admit.
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
Admitted.

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
case: i => [|i|i]; case: i' => [|i'|i'].
- by case=> -> ->.
- by case; lia.
- by case; lia.
- by case; lia.
- case=> /eqP.
  by rewrite (inj_eq (@ord_inj n)) => /eqP -> -> ->.
- case.
  have := ltn_ord i.
  lia.
- by case; lia.
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

Lemma mm2Step_preserves_encoding_left: forall x s',
    mm2_step x (state_encoding s') -> exists s, state_encoding s = x.
Proof.
move=> [i [a b]] [i' [a' b']].
case=> [instr [_]].
elim: instr => /= [| |l|l]; elim; do [
  move=> i'' a'' b'' /=;
  case: (inv_addr_encoding i'') => j H;
  exists (j, (a'', b''));
  by rewrite /state_encoding/= H
    |
  move=> i'' a'' b'' /=;
  case: (inv_addr_encoding i'') => j H;
  exists (j, (a'', b''));
  by rewrite /state_encoding/= H
    |
  move=> i'' _ a'' b'' /=;
  case: (inv_addr_encoding i'') => j H;
  exists (j, (a''.+1, b''));
  by rewrite /state_encoding/= H
    |
  move=> i'' _ a'' b'' /=;
  case: (inv_addr_encoding i'') => j H;
  exists (j, (a'', b''.+1));
  by rewrite /state_encoding/= H
    |
  move=> k _ b'' /=;
  case: (inv_addr_encoding k) => j H;
  exists (j, (0, b''));
  by rewrite /state_encoding/= H
    |
  move=> k _ a'' /=;
  case: (inv_addr_encoding k) => j H;
  exists (j, (a'', 0));
  by rewrite /state_encoding/= H
].
Qed.

Lemma mm2Steps_equiv_lm2eSteps: forall s s' : lm2e_state,
  clos_refl_sym_trans MM2Notations.mm2_state mm2_step (state_encoding s) (state_encoding s') <->
  clos_refl_sym_trans lm2e_state lm2e_step s s'.
Proof.
exact: (closRST_R_equiv_R' _ _ mm2_step lm2e_step state_encoding
  state_encoding_inj
  mm2Step_equiv_lm2eStep
  mm2Step_preserves_encoding_right
  mm2Step_preserves_encoding_left).
Qed.

End LM2EReduction.
End LM2EReduction.

Lemma LM2E_HALTS_reduction : MM2_HALTS_ON_ZERO ⪯ LM2E_HALTS_uncurried.
Proof.
exists LM2EReduction.reduction_output => [[[M x] y]].
split.
- rewrite /MM2_HALTS_ON_ZERO /=.
  rewrite /LM2E_HALTS_uncurried /LM2E_HALTS /=.
  move=> H.
  have := @LM2EReduction.mm2Steps_equiv_lm2eSteps (M, x, y)
    (lm2e_initial_state (LM2EReduction.ne0 (M, x, y)) x y)
    (lm2e_ending_state (LM2EReduction.n (M, x, y))).
  move=> <-.

Admitted.

Lemma LM2E_HALTS_undec : undecidable LM2E_HALTS_uncurried.
apply: (undecidability_from_reducibility MM2_HALTS_ON_ZERO_undec).
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
Qed.

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

Variable n: nat.
Variable M: lm2e_machine n.
Variable a b: nat.

Notation lm2_addr := (lm2_addr n).
Notation lm2_state := (lm2_state n).
Notation lm2e_addr := (lm2e_addr n).
Notation lm2e_instr := (lm2e_instr n).

Definition translate_addr (addr: lm2e_addr) := match addr with
  | lm2e_addr_stop => lm2_addr_stop n
  | lm2e_addr_instr i => lm2_addr_instr i
  | lm2e_addr_boom _ => lm2_addr_stop n (* doesn't matter *)
  end.

Definition translate_addr' (addr: lm2_addr) := match addr with
  | lm2_addr_stop => lm2e_addr_stop n
  | lm2_addr_instr i => lm2e_addr_instr i
  end.

Definition translate_instruction (instr: lm2e_instr) := match instr with
  | lm2e_inc_x i => lm2_inc_x (translate_addr i)
  | lm2e_inc_y i => lm2_inc_y (translate_addr i)
  | lm2e_dec_x i j => lm2_dec_x (translate_addr i) (translate_addr j)
  | lm2e_dec_y i j => lm2_dec_y (translate_addr i) (translate_addr j)
  end.

Definition M'_instructions := [seq translate_instruction instr | instr <- (einstructions M) ].

Lemma M'_machine_length : size M'_instructions == n.
Proof. rewrite /M'_instructions size_map; exact: emachine_length. Qed.

Definition M': lm2_machine n := {|
  instructions := M'_instructions;
  machine_length := M'_machine_length;
|}.

Let lm2_step := (lm2_step M').
Let lm2e_step := (lm2e_step M).

Definition state_encoding (s: lm2_state) :=
  let '(i, (a, b)) := s in (translate_addr' i, (a, b)).

Lemma translate_addrK j: translate_addr (translate_addr' j) = j.
Proof. by case: j. Qed.

Lemma lm2eStep_to_lm2Step : forall s s',
  lm2e_step (state_encoding s) (state_encoding s')
    ->
  lm2_step s s'.
Proof.
move=> [i [x y]] [i' [x' y']].
rewrite /lm2e_step/LM2.lm2e_step/=.
case: i => //= i.
set instr := lm2e_instr_at M i.
have: instr = lm2e_instr_at M i by done.
case: instr => [
  j Hinstr /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /= |
  j Hinstr /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /= |
  j l Hinstr |
  j l Hinstr
].
- case: i' => [|i'].
    move: Hinstr => /[swap] /eqP <-.
    rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
      by rewrite (eqP (emachine_length M)) ltn_ord.
    rewrite /lm2e_instr_at => <- /=.
    by rewrite !eq_refl.
  move: Hinstr => /[swap] /eqP <-.
  rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
    by rewrite (eqP (emachine_length M)) ltn_ord.
  rewrite /lm2e_instr_at => <- /=.
  by rewrite !eq_refl.
- case: i' => [|i'].
    move: Hinstr => /[swap] /eqP <-.
    rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
      by rewrite (eqP (emachine_length M)) ltn_ord.
    rewrite /lm2e_instr_at => <- /=.
    by rewrite !eq_refl.
  move: Hinstr => /[swap] /eqP <-.
  rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
    by rewrite (eqP (emachine_length M)) ltn_ord.
  rewrite /lm2e_instr_at => <- /=.
  by rewrite !eq_refl.
- case: x => [/andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /=|x /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /=].
    case: i' => [|i'].
      move: Hinstr => /[swap] /eqP <-.
      rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
        by rewrite (eqP (emachine_length M)) ltn_ord.
      rewrite /lm2e_instr_at => <- /=.
      by rewrite !eq_refl.
    move: Hinstr => /[swap] /eqP <-.
    rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
      by rewrite (eqP (emachine_length M)) ltn_ord.
    rewrite /lm2e_instr_at => <- /=.
    by rewrite !eq_refl.
  case: i' => [|i'].
    move: Hinstr => /[swap] /eqP <-.
    rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
      by rewrite (eqP (emachine_length M)) ltn_ord.
    rewrite /lm2e_instr_at => <- /=.
    by rewrite !eq_refl.
  move: Hinstr => /[swap] /eqP <-.
  rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
    by rewrite (eqP (emachine_length M)) ltn_ord.
  rewrite /lm2e_instr_at => <- /=.
  by rewrite !eq_refl.
- case: y => [/andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /=|y /andP [/andP []] /[swap] /eqP -> /[swap] /eqP -> /=].
    case: i' => [|i'].
      move: Hinstr => /[swap] /eqP <-.
      rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
        by rewrite (eqP (emachine_length M)) ltn_ord.
      rewrite /lm2e_instr_at => <- /=.
      by rewrite !eq_refl.
    move: Hinstr => /[swap] /eqP <-.
    rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
      by rewrite (eqP (emachine_length M)) ltn_ord.
    rewrite /lm2e_instr_at => <- /=.
    by rewrite !eq_refl.
  case: i' => [|i'].
    move: Hinstr => /[swap] /eqP <-.
    rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
      by rewrite (eqP (emachine_length M)) ltn_ord.
    rewrite /lm2e_instr_at => <- /=.
    by rewrite !eq_refl.
  move: Hinstr => /[swap] /eqP <-.
  rewrite /lm2_step/LM2.lm2_step/=/lm2_instr_at/M'/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
    by rewrite (eqP (emachine_length M)) ltn_ord.
  rewrite /lm2e_instr_at => <- /=.
  by rewrite !eq_refl.
Qed.

Lemma lm2Step_to_lm2eStep_nonstop : forall s s',
  (index s') != lm2_addr_stop _
    ->
  lm2_step s s'
    ->
  lm2e_step (state_encoding s) (state_encoding s').
Proof.
move=> [i [x y]] [i' [x' y']].
rewrite /lm2_step/LM2.lm2_step/=.
case: i => // i.
move=> H'' /[dup] H'.
set instr := lm2_instr_at M' i.
have: instr = lm2_instr_at M' i by done.
rewrite /M'/lm2_instr_at/=/M'_instructions (nth_map (lm2e_dummy_instr n)); last first.
  by rewrite (eqP (emachine_length M)) ?(ltn_ord i).
have: instr = lm2_instr_at M' i by done.
have ->: nth (lm2e_dummy_instr n) M i = lm2e_instr_at M i by done.
case: instr.
- move=> j Hinstr' Hinstr /andP [/andP [/eqP -> /eqP ->] /eqP ->] /=.
  have {H' H''}: j != lm2_addr_stop _.
    move: H'.
    rewrite -Hinstr'.
    by move: H'' => /[swap] /andP [/andP [/eqP -> _] _].
  rewrite /lm2e_step/LM2.lm2e_step/=.
  move: Hinstr.
  case: (lm2e_instr_at M i) => //= j' H.
  injection H => {H}.
  case: j' => /= [-> //|j' -> _ /=|j' -> //].
  by rewrite !eq_refl.
- move=> j Hinstr' Hinstr /andP [/andP [/eqP -> /eqP ->] /eqP ->] /=.
  have {H' H''}: j != lm2_addr_stop _.
    move: H'.
    rewrite -Hinstr'.
    by move: H'' => /[swap] /andP [/andP [/eqP -> _] _].
  rewrite /lm2e_step/LM2.lm2e_step/=.
  move: Hinstr.
  case: (lm2e_instr_at M i) => //= j' H.
  injection H => {H}.
  case: j' => /= [-> //|j' -> _ /=|j' -> //].
  by rewrite !eq_refl.
- move=> j k Hinstr' Hinstr.
  case: x H' => [H'|x H'].
    have {H' H''}: j != lm2_addr_stop _.
      move: H'.
      rewrite -Hinstr'.
      by move: H'' => /[swap] /andP [/andP [/eqP -> _] _].
    move=> /[swap] /andP [/andP [/eqP -> /eqP ->] /eqP ->] /=.
    rewrite /lm2e_step/LM2.lm2e_step/=.
    move: Hinstr.
    case: (lm2e_instr_at M i) => //= j' k' H.
    injection H => {H}.
    case: j' => [_ -> //|j' _ -> _|j' _ -> //].
    by rewrite !eq_refl.
  have {H' H''}: k != lm2_addr_stop _.
    move: H'.
    rewrite -Hinstr'.
    by move: H'' => /[swap] /andP [/andP [/eqP -> _] _].
  move=> /[swap] /andP [/andP [/eqP -> /eqP ->] /eqP ->] /=.
  rewrite /lm2e_step/LM2.lm2e_step/=.
  move: Hinstr.
  case: (lm2e_instr_at M i) => //= j' k' H.
  injection H => {H}.
  case: k' => [-> _ //|k' -> _ _|k' -> _ //].
  by rewrite !eq_refl.
- move=> j k Hinstr' Hinstr.
  case: y H' => [H'|y H'].
    have {H' H''}: j != lm2_addr_stop _.
      move: H'.
      rewrite -Hinstr'.
      by move: H'' => /[swap] /andP [/andP [/eqP -> _] _].
    move=> /[swap] /andP [/andP [/eqP -> /eqP ->] /eqP ->] /=.
    rewrite /lm2e_step/LM2.lm2e_step/=.
    move: Hinstr.
    case: (lm2e_instr_at M i) => //= j' k' H.
    injection H => {H}.
    case: j' => [_ -> //|j' _ -> _|j' _ -> //].
    by rewrite !eq_refl.
  have {H' H''}: k != lm2_addr_stop _.
    move: H'.
    rewrite -Hinstr'.
    by move: H'' => /[swap] /andP [/andP [/eqP -> _] _].
  move=> /[swap] /andP [/andP [/eqP -> /eqP ->] /eqP ->] /=.
  rewrite /lm2e_step/LM2.lm2e_step/=.
  move: Hinstr.
  case: (lm2e_instr_at M i) => //= j' k' H.
  injection H => {H}.
  case: k' => [-> _ //|k' -> _ _|k' -> _ //].
  by rewrite !eq_refl.
Qed.

Lemma lm2Step_to_lm2eStep_stop : forall s a b,
  lm2_step s ((lm2_addr_stop _), (a, b))
    ->
  lm2e_step (state_encoding s) ((lm2e_addr_stop _), (a, b)).
Proof.
Admitted.

Lemma lm2Step_to_lm2eStep : forall s s',
  lm2_step s s'
    ->
  lm2e_step (state_encoding s) (state_encoding s').
Proof.
move=> [i [x y]] [i' [x' y']].
case: i' => [|i']; do [
  exact: lm2Step_to_lm2eStep_stop |
  exact: lm2Step_to_lm2eStep_nonstop
].
Qed.

End LM2Reduction.
End LM2Reduction.

Lemma LM2_HALTS_reduction : MM2_HALTS_ON_ZERO ⪯ LM2_HALTS_uncurried.
Proof.
exists LM2Reduction.reduction_output => [[[M x] y]].
split.
- rewrite /MM2_HALTS_ON_ZERO /=.
  rewrite /LM2_HALTS_uncurried /LM2_HALTS /=.
Admitted.

Lemma LM2_HALTS_undec : undecidable LM2_HALTS_uncurried.
apply: (undecidability_from_reducibility MM2_HALTS_ON_ZERO_undec).
exact: LM2_HALTS_reduction.
Qed.
