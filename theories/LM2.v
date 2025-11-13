From HB Require Import structures.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec MM2_facts.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq.
From mathcomp Require Import eqtype fintype ssrnat div intdiv.
From mathcomp Require Import ring zify.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Stdlib.Program Require Import Equality.

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

(* TODO: investigating the output type being bool *)
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

Variable P: MM2_PROBLEM.
Let M := P.1.1.
Let initial_a := P.1.2.
Let initial_b := P.2.

Definition n := size M.

Notation lm2_addr := (lm2_addr n).
Notation lm2_state := (lm2_state n).
Notation mm2_step := (mm2_step M).

(* TODO: do a case analysis whether the machine is empty *)
Definition ne0 : n > 0.
Admitted.

Definition fallback_target_address (i: 'I_n) : lm2_addr :=
  if \val (ordS i) == 0 then lm2_addr_stop _ else lm2_addr_instr (ordS i).

Definition jump_target_address (i: nat) : lm2_addr.
Admitted.
(*
Definition jump_target_address (i: nat) : lm2_addr := match i with
  | 0 => lm2_addr_stop _
  | i.+1 => if orP (orbN (i < n)%N) is or_introl x
      then lm2_addr_instr (Ordinal x)
      else lm2_addr_stop _
  end.
*)

Definition translate_instruction (instr: mm2_instr) (i: 'I_n) := match instr with
  | mm2_inc_a => lm2_inc_x (fallback_target_address i)
  | mm2_inc_b => lm2_inc_y (fallback_target_address i)
  | mm2_dec_a j => lm2_dec_x (fallback_target_address i) (jump_target_address j)
  | mm2_dec_b j => lm2_dec_y (fallback_target_address i) (jump_target_address j)
  end.

Definition M'_instructions :=
  [seq translate_instruction (nth mm2_inc_a M (\val i)) i | i <- enum 'I_n ].

Lemma M'_machine_length : size M'_instructions == n.
Proof. by rewrite /M'_instructions size_map size_enum_ord. Qed.

Definition M': lm2_machine n := {|
  instructions := M'_instructions;
  machine_length := M'_machine_length;
|}.

Let lm2_step := (lm2_step M').

Definition reduction_output : Lm2HaltsArguments := {|
  lm2_halts_arguments_n := n;
  lm2_halts_arguments_M := M';
  lm2_halts_arguments_ne0 := ne0;
  lm2_halts_arguments_x := initial_a;
  lm2_halts_arguments_y := initial_b;
|}.

Definition address_encoding (addr: lm2_addr) : nat := match addr with
  | lm2_addr_stop => 0
  | lm2_addr_instr i => i.+1
  end.

Definition mm2_state := (nat * (nat * nat))%type.

Definition state_encoding (s: lm2_state) : mm2_state :=
  (address_encoding (index s), (value_x s, value_y s)).

Notation lm2_ending_state := (lm2_ending_state n).

Definition ord0: 'I_n.
Proof. exists 0; exact: ne0. Defined.

Definition ordlast: 'I_n.
Proof. exists n.-1; move: ne0; lia. Defined.

Lemma fallback_target_address_edge: address_encoding (fallback_target_address ordlast) = 0.
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

Lemma mm_instr_at_nth (pos: 'I_n): mm2_instr_at (nth mm2_inc_a M pos) pos.+1 M.
Admitted.

Lemma mm2Steps_extra_return_path xy : clos_refl_trans MM2Notations.mm2_state mm2_step (n, xy) (0, (0, 0)).
Admitted.

Lemma lm2Step_to_mm2Steps : forall s,
  clos_refl_trans _ lm2_step s lm2_ending_state
    ->
  clos_refl_trans _ mm2_step (state_encoding s) (state_encoding lm2_ending_state).
Proof.
move=> s /clos_rt_rt1n_iff H; dependent induction H.
  exact /rt_refl.
move: IHclos_refl_trans_1n => /(_ erefl) IH {H0}.
move: x y H IH => [[//|pos] [x y]] [i' [x' y']].
rewrite /lm2_step /LM2.lm2_step /lm2_instr_at /M' /M'_instructions /state_encoding /=.
rewrite (nth_map pos) ?size_enum_ord // nth_ord_enum.
set instr := nth mm2_inc_a M pos.
have Hinstr: instr = nth mm2_inc_a M pos by done.
elim: instr Hinstr => [Hinstr |Hinstr |j Hinstr |j Hinstr] /=; [| | case: x => [|x] | case: y => [|y]].
- move=> /andP [/andP [/eqP -> /eqP ->]] /eqP ->.
  have /orP [/eqP ->| ?] := orbN (pos == ordlast).
    rewrite fallback_target_address_edge prednK ?ne0 //= => _.
    exact /mm2Steps_extra_return_path.
  rewrite fallback_target_address_normal //= => Hend.
  apply /(rt_trans _ _ _ (pos.+2, (x.+1, y))) => // {Hend}.
  apply /rt_step.
  exists mm2_inc_a; split; last exact /in_mm2s_inc_a.
  rewrite /= Hinstr; exact /mm_instr_at_nth.
- move=> /andP [/andP [/eqP -> /eqP ->]] /eqP ->.
  have /orP [/eqP ->| ?] := orbN (pos == ordlast).
    rewrite fallback_target_address_edge prednK ?ne0 //= => _.
    exact /mm2Steps_extra_return_path.
  rewrite fallback_target_address_normal //= => Hend.
  apply /(rt_trans _ _ _ (pos.+2, (x, y.+1))) => // {Hend}.
  apply /rt_step.
  exists mm2_inc_b; split; last exact /in_mm2s_inc_b.
  rewrite /= Hinstr; exact /mm_instr_at_nth.
- move=> /andP [/andP [/eqP -> /eqP ->]] /eqP ->.
  have /orP [/eqP ->| ?] := orbN (pos == ordlast).
    rewrite fallback_target_address_edge prednK ?ne0 //= => _.
    exact /mm2Steps_extra_return_path.
  rewrite fallback_target_address_normal //= => Hend.
  apply /(rt_trans _ _ _ (pos.+2, (0, y))) => // {Hend}.
  apply /rt_step.
  exists (mm2_dec_a j); split; last exact /in_mm2s_dec_a0.
  rewrite /= Hinstr; exact /mm_instr_at_nth.
- admit.
- admit.
- admit.
Admitted.
(*
  move=> Hend.
  apply /(rt_trans _ _ _ (address_encoding (jump_target_address j), (x, y))) => //.
  apply /rt_step.
rewrite /jump_target_address.
  exists (mm2_dec_a j); split.
admit.
exact /in_mm2s_dec_aS.

  move=> H.

  have /orP [/eqP ->| ?] := orbN (pos == ordlast).
    rewrite fallback_target_address_edge prednK ?ne0 //= => _.
    exact /mm2Steps_extra_return_path.
  rewrite fallback_target_address_normal //= => Hend.
  apply /(rt_trans _ _ _ (pos.+2, (0, y))) => // {Hend}.
  apply /rt_step.
  exists (mm2_dec_a j); split; last exact /in_mm2s_dec_a0.
  rewrite /= Hinstr; exact /mm_instr_at_nth.
- move=> /andP [/andP [/eqP -> /eqP ->]] /eqP ->.
  have /orP [/eqP ->| ?] := orbN (pos == ordlast).
    rewrite fallback_target_address_edge prednK ?ne0 //=.
    admit.


apply /(rt_trans _ _ _ (state_encoding y)); last first.
  exact /IHclos_refl_trans_1n.
move=> {IHclos_refl_trans_1n} {H0}.
case: i => [//|pos].
rewrite /lm2_step /LM2.lm2_step /=.
rewrite /lm2_instr_at /M' /M'_instructions /state_encoding /=.
rewrite (nth_map pos) ?size_enum_ord // nth_ord_enum.
set instr := nth mm2_inc_a M pos.
elim: instr => [ | | j | j] /=.
- move=> /andP [/andP [/eqP -> /eqP ->]] /eqP ->.
  
  rewrite /fallback_target_address /=.
  have
Admitted.
*)

Lemma lm2InstrAt_when_mm2InstrAt instr (pos: 'I_n) :
  mm2_instr_at instr pos.+1 M ->
  (translate_instruction instr pos) = lm2_instr_at M' pos.
Admitted.

Lemma nm2Step_to_lm2Step : forall s s',
  mm2_step (state_encoding s) (state_encoding s') -> lm2_step s s'.
Proof.
Admitted.

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
