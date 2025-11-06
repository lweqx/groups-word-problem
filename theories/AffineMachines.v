From HB Require Import structures.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq.
From mathcomp Require Import all_algebra eqtype fintype ssrnat intdiv prime.
From mathcomp Require Import ring lra zify.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Stdlib.Program Require Import Equality.

Import GRing.Theory.
Open Scope int_scope.
Open Scope ring_scope.

(* `(p, q): State` represents the set of all `p + qZ` *)
(* TODO: should be int * non-zero int but it's a pain, let's see where this gets us. *)
Definition State := (int * int) % type.
Definition isOnState (s: State) (k: int) : Type :=
  let (p, q) := s in
  { z: int | k = p + q*z }.

Definition Transition := (State * State) % type.
Definition startingState (t: Transition) : State := fst t. 
Definition finalState (t: Transition) : State := snd t. 

(* Returns the position obtained after moving a position `k` laying on
   the initial state of `t: transition` along `t` *)
Definition transitionState (t: Transition) :
  forall (k: int), isOnState (startingState t) k -> int.
Proof.
move: t => [] /= [p q] [p' q'] k [] z _.
exact (p' + q' * z).
Defined.

(* If we take a transition `t` from a position `k` laying on the
   starting state of `t`, the position reached is the final state of
   `t` *)
Lemma reachesFinalState : forall (t: Transition),
  forall (k: int) (onState: isOnState (startingState t) k),
  isOnState (finalState t) (transitionState onState).
Proof.
move=> [[p q] [p' q']] /= k [z _].
by exists z.
Defined.

(* An affine machine. *)
Definition Machine := seq Transition.

Section Affine.
Variable A: Machine.

(* Whether `t: Transition` is a transition of `A: Machine` *)
Definition isTransitionOf (t: Transition) := t \in A.

Definition transitionStep (t: Transition) a b :=
  (isTransitionOf t) /\ exists (onState: isOnState (startingState t) a), b = transitionState onState.

Definition affineStep a b := exists (t: Transition), transitionStep t a b.

End Affine.

(* The equivalence problem. *)
Definition equivalence_problem (A: Machine) (m z: int) : Prop := clos_refl_sym_trans _ (affineStep A) m z.
Definition equivalence_problem_uncurried := fun '(A, m, z) => equivalence_problem A m z.

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
  machine_length : size instructions = n;
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
    | lm2_inc_x i => (index s' = i) /\ (value_x s' = (value_x s).+1) /\ (value_y s' = value_y s)
    | lm2_inc_y i => (index s' = i) /\ (value_x s' = value_x s) /\ (value_y s' = (value_y s).+1)
    | lm2_dec_x i j => if value_x s is S n
        then (index s' = j) /\ (value_x s' = n) /\ (value_y s' = value_y s)
        else (index s' = i) /\ (value_x s' = 0) /\ (value_y s' = value_y s)
    | lm2_dec_y i j => if value_y s is S n
        then (index s' = j) /\ (value_x s' = value_x s) /\ (value_y s' = n)
        else (index s' = i) /\ (value_x s' = value_x s) /\ (value_y s' = 0)
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

Lemma LM2_HALTS_undec : undecidable LM2_HALTS_uncurried.
Admitted.

Section Reduction.
Import MM2Notations.

Variable n: nat.
Variable machine_non_empty: (n > 0)%N.
Variable M: lm2_machine n.
Variable initial_x : nat.
Variable initial_y : nat.

Notation m := ((size M).+1)%:Z.

Notation lm2_instr := (lm2_instr n).
Notation lm2_state := (lm2_state n).
Notation lm2_addr := (lm2_addr n).
Notation lm2_step := (lm2_step M).
Notation machine_length := (machine_length M).

Definition initial_state := lm2_initial_state machine_non_empty initial_x initial_y.
Definition ending_state: lm2_state := lm2_ending_state n.

Definition address_encoding (addr: lm2_addr) : nat := match addr with
  | lm2_addr_stop => 0
  | lm2_addr_instr i => i.+1
  end.

Definition state_encoding (s: lm2_state) : int := let '(i, (x, y)) := s in
  (address_encoding i)%:Z + m * (2 ^+ x) * (3 ^+ y).

(* encodes the instruction `instr` at address `i` *)
Definition instruction_encoding (instr: lm2_instr) (i: 'I_n) : list Transition :=
  let i: int := address_encoding (lm2_addr_instr i) in
  match instr with
  | lm2_inc_x j => [:: ((i, m), ((address_encoding j)%:Z, 2 * m))]
  | lm2_inc_y j => [:: ((i, m), ((address_encoding j)%:Z, 3 * m))]
  | lm2_dec_x j k => let j := (address_encoding j)%:Z in let k := (address_encoding k)%:Z in [::
      (* i + m(2z + 1) -> k + m(2z + 1) : x is zero, continue to j *)
      ((i + m, 2 * m), (j + m, 2 * m));

      (* i + 2mz -> k + mz : x is not-zero, decrement and jump to k *)
      ((i, 2 * m), (k, m))
    ]
  | lm2_dec_y j k => let j := (address_encoding j)%:Z in let k := (address_encoding k)%:Z in [::
      (* i + m(3z + 1) -> j + m(3z + 1) : y is zero, continue to j *)
      ((i + m, 3 * m), (j + m, 3 * m));
      (* i + m(3z + 2) -> j + m(3z + 2) : y is zero, continue to j *)
      ((i + 2 * m, 3 * m), (j + 2 * m, 3 * m));

      (* i + 3mz -> k + mz : y is not-zero, decrement and jump to k *)
      ((i, 3 * m), (k, m))
    ]
  end.

Definition A : Machine := flatten (
    map (
      fun i => instruction_encoding (lm2_instr_at M i) i
    ) (enum 'I_n)
  ).

Definition reduction_output : Machine * int * int := (A, state_encoding initial_state, state_encoding ending_state).

Notation affineStep := (affineStep A).

Notation affineStepEncoding s s' := (affineStep (state_encoding s) (state_encoding s')).

Lemma lm2Step_to_affineStep : forall s s',
  (lm2_step s s') -> (affineStepEncoding s s').
Proof.
move=> [i [x y]] [i' [x' y']].
elim: i; rewrite /lm2_step //=.
move=> pos.
set instr := lm2_instr_at M pos.
have: instr = lm2_instr_at M pos by done.
elim: instr.
- (* inc_x *)
  move=> j instr_at_pos; do ! case=> [->].
  exists (((address_encoding (lm2_addr_instr pos))%:Z, m), ((address_encoding j)%:Z, 2 * m)).
  split.
    apply /flattenP.
    exists (instruction_encoding (lm2_inc_x j) pos); last first.
      rewrite inE //=.
    rewrite instr_at_pos.
    apply /mapP; exists pos => //.
    by rewrite mem_enum.
  unshelve eexists.
    exists (2^+x * 3^+y) => /=.
    by rewrite -mulrA.
  rewrite /= exprS.
  lia.
- (* inc_y *)
  move=> j instr_at_pos; do ! case=> [->].
  exists (((address_encoding (lm2_addr_instr pos))%:Z, m), ((address_encoding j)%:Z, 3 * m)).
  split.
    apply /flattenP.
    exists (instruction_encoding (lm2_inc_y j) pos); last first.
      rewrite inE //=.
    rewrite instr_at_pos.
    apply /mapP; exists pos => //.
    by rewrite mem_enum.
  unshelve eexists.
    exists (2^+x * 3^+y) => /=.
    by rewrite -mulrA.
  rewrite /= exprS.
  lia.
- (* dec_x *)
  move=> j k instr_at_pos.
  case: x.
  - do ! case=> [->].
    exists (((address_encoding (lm2_addr_instr pos))%:Z + m, 2 * m), ((address_encoding j)%:Z + m, 2 * m)).
    split.
      apply /flattenP.
      exists (instruction_encoding (lm2_dec_x j k) pos); last first.
        by rewrite inE; apply /orP; left.
      rewrite instr_at_pos.
      apply /mapP; exists pos => //.
      by rewrite mem_enum.
    have remainder_1: ((2 ^+ 0 * 3 ^+ y) %% 2)%Z = 1.
      rewrite expr0 mul1r -modzXm.
      have ->: (3 %% 2)%Z = 1 by done.
      by rewrite expr1n.
    unshelve eexists.
      exists ((2^+0 * 3^+y) %/ 2)%Z => /=.
      rewrite -mulrA {1}(divz_eq (2^+0 * 3^+y) 2).
      rewrite remainder_1; lia.
    rewrite /=.
    transitivity ((address_encoding j)%:Z + m * (((2 ^+ 0 * 3 ^+ y) %/ 2)%Z * 2 + 1)); last lia.
    rewrite -{7}remainder_1.
    rewrite -(divz_eq (2^+0 * 3^+y) 2).
    lia.
  - move=> l; do ! case=> [->].
    exists (((address_encoding (lm2_addr_instr pos))%:Z, 2 * m), ((address_encoding k)%:Z, m)).
    split.
      apply /flattenP.
      exists (instruction_encoding (lm2_dec_x j k) pos); last first.
        by rewrite inE; apply /orP; right; rewrite inE.
      rewrite instr_at_pos.
      apply /mapP; exists pos => //.
      by rewrite mem_enum.
    unshelve eexists.
      exists (2 ^+ l * 3 ^+ y) => /=.
      rewrite exprS; lia.
    rewrite /=; lia.
- (* dec_y *)
  move=> j k instr_at_pos.
  case: y.
  - do ! case=> [->].
    have []: ((2 ^+ x * 3 ^+ 0) %% 3)%Z = 1 \/ ((2 ^+ x * 3 ^+ 0) %% 3)%Z = 2.
      have: ((2 ^+ x * 3 ^+ 0) %% 3)%Z < 3 by apply: ltz_pmod.
      admit.
    - move=> remainder.
      exists (((address_encoding (lm2_addr_instr pos))%:Z + m, 3 * m), ((address_encoding j)%:Z + m, 3 * m)).
      split.
        apply /flattenP.
        exists (instruction_encoding (lm2_dec_y j k) pos); last first.
          by rewrite inE; apply /orP; left.
        rewrite instr_at_pos.
        apply /mapP; exists pos => //.
        by rewrite mem_enum.
      unshelve eexists.
        exists ((2 ^+ x * 3 ^+ 0) %/ 3)%Z => /=.
        rewrite -mulrA {1}(divz_eq (2^+x * 3^+0) 3).
        rewrite remainder; lia.
      rewrite /=; lia.
    - move=> remainder.
      exists (((address_encoding (lm2_addr_instr pos))%:Z + 2 * m, 3 * m), ((address_encoding j)%:Z + 2 * m, 3 * m)).
      split.
        apply /flattenP.
        exists (instruction_encoding (lm2_dec_y j k) pos); last first.
          by rewrite inE; apply /orP; right; rewrite inE; apply /orP; left.
        rewrite instr_at_pos.
        apply /mapP; exists pos => //.
        by rewrite mem_enum.
      unshelve eexists.
        exists ((2 ^+ x * 3 ^+ 0) %/ 3)%Z => /=.
        rewrite -mulrA {1}(divz_eq (2^+x * 3^+0) 3).
        rewrite remainder; lia.
      rewrite /=; lia.
  - move=> l; do ! case=> [->].
    exists (((address_encoding (lm2_addr_instr pos))%:Z, 3 * m), ((address_encoding k)%:Z, m)).
    split.
      apply /flattenP.
      exists (instruction_encoding (lm2_dec_y j k) pos); last first.
        by rewrite inE; apply /orP; right; rewrite inE; apply /orP; right; rewrite inE.
      rewrite instr_at_pos.
      apply /mapP; exists pos => //.
      by rewrite mem_enum.
    unshelve eexists.
      exists (2 ^+ x * 3 ^+ l) => /=.
      rewrite exprS; lia.
    rewrite /=; lia.
Admitted.

Lemma simplify_modulo : forall (a b c d K: int),
    (0 <= a <= K - 1)%R ->
    (0 <= b <= K - 1)%R ->
  a + K * c = b + K * d -> a = b.
Proof.
move=> a b c d K ? ? Heq.
have: a = b %[mod K].
  rewrite -(addr0 a) -(modzMr c K) modzDmr.
  rewrite -(addr0 b) -(modzMr d K) modzDmr.
  by rewrite Heq.
move=> /eqP.
rewrite -(eqz_modDr (-0)).
rewrite !modz_small; lia.
Qed.
Arguments simplify_modulo {a b} c d K.

Lemma simplify_quotient : forall (a b c d K: int),
    (0 <= a <= K - 1)%R ->
    (0 <= b <= K - 1)%R ->
  a + K * c = b + K * d -> c = d.
Proof.
move=> a b c d K ? ? Heq.
have: a = b by exact /(simplify_modulo c d K).
move: Heq => /[swap] ->.
move=> /addrI /mulfI H.
apply /H; lia.
Qed.
Arguments simplify_quotient a b {c d} K.

Lemma address_encoding_bound : forall a, (address_encoding a <= (size M).+1 - 1)%N.
Proof.
rewrite machine_length.
case=> /=; first lia.
move=> pos.
have := ltn_ord pos; lia.
Qed.

Lemma address_encoding_injective : forall i j,
  address_encoding i = address_encoding j -> i = j.
Proof.
case=> [|o]; case; rewrite /address_encoding => //.
move=> o' /eqP ?; exact: eqP.
Qed.

Lemma powers_injective : forall (x y x' y': nat),
  2^+x * 3^+y = 2^+x' * 3^+y' :> int -> (x = x') /\ (y = y').
Proof.
move=> x y x' y' H.
have {}H: (2^+x * 3^+y = 2^+x' * 3^+y')%N by lia.
have: logn 2 (2 ^+ x * 3 ^+ y : nat) = logn 2 (2 ^+ x' * 3 ^+ y') by rewrite H.
have: logn 3 (2 ^+ x * 3 ^+ y : nat) = logn 3 (2 ^+ x' * 3 ^+ y') by rewrite H.
rewrite !lognM; try lia.
rewrite !lognX /=.
have ->: logn 3 3 = 1 by done.
have ->: logn 2 2 = 1 by done.
have ->: logn 2 3 = 0 by done.
have ->: logn 3 2 = 0 by done.
lia.
Qed.
Arguments powers_injective {_ _ _ _} _.

Lemma affineStep_to_lm2Step : forall s s',
  (affineStepEncoding s s') -> (lm2_step s s').
Proof.
move=> [i [x y]] [i' [x' y']].
case=> [[[p q] [p' q']]] [].
move=> /flattenP [] transitions /mapP [] pos _.
move=> -> trans_is_encoded [] /= [k].
move: trans_is_encoded.
set instr := lm2_instr_at M pos.
have: instr = lm2_instr_at M pos by done.
elim: instr => [j instr_at_pos|j instr_at_pos|j l instr_at_pos|j l instr_at_pos].
- rewrite inE => /eqP [] -> -> -> ->.
  rewrite -mulrA.
  have ->: 2 * m * k = m * (2 * k) by lia.
  rewrite -mulrA => s_eq s'_eq.
  have ->: i' = j.
    apply /address_encoding_injective /eqP.
    rewrite -eqz_nat.
    apply /eqP /(simplify_modulo _ _ m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: s'_eq.
  have: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: s_eq.
  move: s'_eq => /[swap] <- s'_eq.
  have: (2 ^+ x' * 3 ^+ y') = (2 * (2 ^+ x * 3 ^+ y) : int).
    apply /(simplify_quotient (address_encoding i') (address_encoding j) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: s'_eq.
  rewrite mulrA -exprS.
  move=> /powers_injective [-> ->].
  have /eqP: address_encoding i == pos.+1.
    rewrite -eqz_nat.
    apply /eqP /(simplify_modulo _ _ m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: s_eq.
  move=> {s_eq} {s'_eq}; elim: i => [/=|pos' /= /eqP].
    lia.
  rewrite eqSS.
  move=> /eqP /ord_inj -> {pos'}.
  rewrite /lm2_step/= -instr_at_pos.
  done.
- rewrite inE.
  move=> /eqP [] -> -> -> ->.
  rewrite -mulrA.
  have ->: 3 * m * k = m * (3 * k) by lia.
  rewrite -mulrA => s_eq s'_eq.
  have ->: i' = j.
    apply /address_encoding_injective /eqP.
    rewrite -eqz_nat.
    apply /eqP /(simplify_modulo _ _ m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: s'_eq.
  have: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: s_eq.
  move: s'_eq => /[swap] <- s'_eq.
  have: (2 ^+ x' * 3 ^+ y') = (3 * (2 ^+ x * 3 ^+ y) : int).
    apply /(simplify_quotient (address_encoding i') (address_encoding j) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: s'_eq.
  rewrite mulrA (mulrC 3) -mulrA -exprS.
  move=> /powers_injective [-> ->].
  have: address_encoding i = pos.+1.
    apply /eqP.
    rewrite -eqz_nat.
    apply /eqP /(simplify_modulo _ _ m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: s_eq.
  move=> {s_eq} {s'_eq}; elim: i.
    move=> /=; lia.
  move=> pos' /= /eqP.
  rewrite eqSS.
  move=> /eqP /ord_inj -> {pos'}.
  rewrite /lm2_step/= -instr_at_pos.
  done.
- rewrite inE; move=> /orP; case.
  - move=> /eqP [] -> -> -> ->.
    rewrite -![m * _ * _]mulrA.
    have ->: 2 * m * k = m * (2 * k) by lia.
    rewrite -{2 5}[m]mulr1 -!addrA -!mulrDr => s_eq s'_eq.
    have ->: i' = j.
      apply /address_encoding_injective /eqP.
      rewrite -eqz_nat.
      apply /eqP /(simplify_modulo _ _ m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: s'_eq.
    have H: (2^+x * 3^+y) = 1 + 2*k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: s_eq.
    have x_eq_0: x = 0.
      admit.
    move: H s'_eq => <- s'_eq.
    have: (2 ^+ x' * 3 ^+ y') = ((2 ^+ x * 3 ^+ y) : int).
      apply /(simplify_quotient (address_encoding i') (address_encoding j) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: s'_eq.
    move=> /powers_injective [-> ->].
    have: address_encoding i = pos.+1.
      apply /eqP.
      rewrite -eqz_nat.
      apply /eqP /(simplify_modulo _ _ m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: s_eq.
    move=> {s_eq} {s'_eq}; elim: i.
      move=> /=; lia.
    move=> pos' /= /eqP.
    rewrite eqSS.
    move=> /eqP /ord_inj -> {pos'}.
    rewrite /lm2_step/= -instr_at_pos.
    by rewrite x_eq_0.
  - rewrite inE; move=> /eqP [] -> -> -> ->.
    rewrite -![m * _ * _]mulrA.
    have ->: 2 * m * k = m * (2 * k) by lia.
    move=> s_eq s'_eq.
    have ->: i' = l.
      apply /address_encoding_injective /eqP.
      rewrite -eqz_nat.
      apply /eqP /(simplify_modulo _ _ m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: s'_eq.
    have H: (2^+x * 3^+y) = 2 * k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: s_eq.
    move: s'_eq s_eq H.
    case: x; first admit; move=> x.
    move=> s'_eq s_eq H.
    have {H}: (2^+x * 3^+y) = k.
      apply /(simplify_quotient (address_encoding i) pos.+1 (m * 2)).
      move: (address_encoding_bound i); lia.
      by rewrite machine_length; have := ltn_ord pos; lia.
      rewrite -mulrA [2 * (_ * _)]mulrA -exprS -[_ * _ * k]mulrA.
      exact: s_eq.
    move: s'_eq => /[swap] <- s'_eq.
    have: (2 ^+ x' * 3 ^+ y') = ((2 ^+ x * 3 ^+ y) : int).
      apply /(simplify_quotient (address_encoding i') (address_encoding l) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: s'_eq.
    move=> /powers_injective [-> ->].
    have: address_encoding i = pos.+1.
      apply /eqP.
      rewrite -eqz_nat.
      apply /eqP /(simplify_modulo _ _ m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: s_eq.
    move=> {s_eq} {s'_eq}; elim: i.
      move=> /=; lia.
    move=> pos' /= /eqP.
    rewrite eqSS.
    move=> /eqP /ord_inj -> {pos'}.
    by rewrite /lm2_step/= -instr_at_pos.
- rewrite inE; move=> /orP; case.
    move=> /eqP [] -> -> -> ->.
    rewrite -![m * _ * _]mulrA.
    have ->: 3 * m * k = m * (3 * k) by lia.
    rewrite -{2 5}[m]mulr1 -!addrA -!mulrDr => s_eq s'_eq.
    have ->: i' = j.
      apply /address_encoding_injective /eqP.
      rewrite -eqz_nat.
      apply /eqP /(simplify_modulo _ _ m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: s'_eq.
    have H: (2^+x * 3^+y) = 1 + 3*k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: s_eq.
    have y_eq_0: y = 0.
      admit.
    move: H s'_eq => <- s'_eq.
    have: (2 ^+ x' * 3 ^+ y') = ((2 ^+ x * 3 ^+ y) : int).
      apply /(simplify_quotient (address_encoding i') (address_encoding j) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: s'_eq.
    move=> /powers_injective [-> ->].
    have: address_encoding i = pos.+1.
      apply /eqP.
      rewrite -eqz_nat.
      apply /eqP /(simplify_modulo _ _ m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: s_eq.
    move=> {s_eq} {s'_eq}; elim: i.
      move=> /=; lia.
    move=> pos' /= /eqP.
    rewrite eqSS.
    move=> /eqP /ord_inj -> {pos'}.
    rewrite /lm2_step/= -instr_at_pos.
    by rewrite y_eq_0.
  rewrite inE; move=> /orP; case.
    move=> /eqP [] -> -> -> ->.
    rewrite -![m * _ * _]mulrA.
    have ->: 3 * m * k = m * (3 * k) by lia.
    rewrite -!addrA [2 * _]mulrC -!mulrDr => s_eq s'_eq.
    have ->: i' = j.
      apply /address_encoding_injective /eqP.
      rewrite -eqz_nat.
      apply /eqP /(simplify_modulo _ _ m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: s'_eq.
    have H: (2^+x * 3^+y) = 2 + 3*k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: s_eq.
    have y_eq_0: y = 0.
      admit.
    move: H s'_eq => <- s'_eq.
    have: (2 ^+ x' * 3 ^+ y') = ((2 ^+ x * 3 ^+ y) : int).
      apply /(simplify_quotient (address_encoding i') (address_encoding j) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: s'_eq.
    move=> /powers_injective [-> ->].
    have: address_encoding i = pos.+1.
      apply /eqP.
      rewrite -eqz_nat.
      apply /eqP /(simplify_modulo _ _ m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: s_eq.
    move=> {s_eq} {s'_eq}; elim: i.
      move=> /=; lia.
    move=> pos' /= /eqP.
    rewrite eqSS.
    move=> /eqP /ord_inj -> {pos'}.
    rewrite /lm2_step/= -instr_at_pos.
    by rewrite y_eq_0.
  rewrite inE; move=> /eqP [] -> -> -> ->.
  rewrite -![m * _ * _]mulrA.
  have ->: 3 * m * k = m * (3 * k) by lia.
  move=> s_eq s'_eq.
  have ->: i' = l.
    apply /address_encoding_injective /eqP.
    rewrite -eqz_nat.
    apply /eqP /(simplify_modulo _ _ m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: s'_eq.
  have H: (2^+x * 3^+y) = 3*k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: s_eq.
  move: s'_eq s_eq H.
  case: y; first admit; move=> y.
  move=> s'_eq s_eq H.
  have {H}: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) pos.+1 (m * 3)).
    move: (address_encoding_bound i); lia.
    by rewrite machine_length; have := ltn_ord pos; lia.
    rewrite -mulrA [3 * _]mulrA [3 * _]mulrC -[2^+x * 3 * _]mulrA -exprS -mulrA.
    exact: s_eq.
  move: s'_eq => /[swap] <- s'_eq.
  have: (2 ^+ x' * 3 ^+ y') = ((2 ^+ x * 3 ^+ y) : int).
    apply /(simplify_quotient (address_encoding i') (address_encoding l) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: s'_eq.
  move=> /powers_injective [-> ->].
  have: address_encoding i = pos.+1.
    apply /eqP.
    rewrite -eqz_nat.
    apply /eqP /(simplify_modulo _ _ m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: s_eq.
  move=> {s_eq} {s'_eq}; elim: i.
    move=> /=; lia.
  move=> pos' /= /eqP.
  rewrite eqSS.
  move=> /eqP /ord_inj -> {pos'}.
  by rewrite /lm2_step /= -instr_at_pos.
Admitted.

Lemma affineStep_equiv_lm2Step : forall s s',
  (affineStepEncoding s s') <-> (lm2_step s s').
Proof.
move=> s s'; split.
- exact: affineStep_to_lm2Step.
- exact: lm2Step_to_affineStep.
Qed.

Lemma state_encoding_injective : forall s s',
  state_encoding s = state_encoding s' -> s = s'.
Proof.
move=> [i [x y]] [i' [x' y']] /=.
rewrite -!mulrA => H.
have ->: i = i'.
  apply /address_encoding_injective /eqP.
  rewrite -eqz_nat.
  apply /eqP /(simplify_modulo _ _ m).
  exact: address_encoding_bound.
  exact: address_encoding_bound.
  exact: H.
have: (2 ^+ x * 3 ^+ y) = ((2 ^+ x' * 3 ^+ y') : int).
  apply /(simplify_quotient (address_encoding i) (address_encoding i') m).
  exact: address_encoding_bound.
  exact: address_encoding_bound.
  exact: H.
by move=> /powers_injective [-> ->].
Qed.

(* Idea: this lemma could be used to simplify proofs above. *)
Lemma affineStep_preserves_encoding : forall s y,
  affineStep (state_encoding s) y -> exists s', y = state_encoding s'.
Proof.
move=> [i [x y]] z.
case=> [[[p q] [p' q']]] [].
move=> /flattenP [] transitions /mapP [] pos _ ->.
set instr := lm2_instr_at M pos.
elim: instr => [j|j|j l|j l].
- rewrite inE => /eqP -> /=.
  case=> [] [] k.
  rewrite -mulrA => eq.
  have <-: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: eq.
  rewrite (divz_eq z m) addrC mulrC [2 * _]mulrC.
  rewrite -[m * 2 * _]mulrA [2 * (_ * _)]mulrA -exprS => {}eq.
  have Hzi: (z %% m)%Z = address_encoding j.
    apply /(simplify_modulo _ _ m).
    lia.
    exact: address_encoding_bound.
    exact: eq.
  have Hzxy: (z %/ (size M).+1)%Z = 2 ^+ x.+1 * 3 ^+ y.
    apply /(simplify_quotient (z %% m)%Z (address_encoding j) m).
    lia.
    exact: address_encoding_bound.
    exact: eq.
  exists (j, (x.+1, y)).
  rewrite Hzi Hzxy /=.
  lia.
- rewrite inE => /eqP -> /=.
  case=> [] [] k.
  rewrite -mulrA => eq.
  have <-: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: eq.
  rewrite (divz_eq z m) addrC mulrC [3 * _]mulrC.
  rewrite -[m * 3 * _]mulrA.
  rewrite [3 * (_ * _)]mulrA [3 * _]mulrC -[_ * 3 * _]mulrA -exprS => {}eq.
  have Hzi: (z %% m)%Z = address_encoding j.
    apply /(simplify_modulo _ _ m).
    lia.
    exact: address_encoding_bound.
    exact: eq.
  have Hzxy: (z %/ (size M).+1)%Z = 2 ^+ x * 3 ^+ y.+1.
    apply /(simplify_quotient (z %% m)%Z (address_encoding j) m).
    lia.
    exact: address_encoding_bound.
    exact: eq.
  exists (j, (x, y.+1)).
  rewrite Hzi Hzxy /=.
  lia.
- rewrite inE => /orP [/eqP ->|].
    case=> [] [] k /=.
    rewrite -mulrA -[2 * _]mulrC -mulrA -{2}[m]mulr1 -addrA -mulrDr => eq.
    rewrite -{1}[m]mulr1 -addrA -mulrDr.
    have <-: (2^+x * 3^+y) = 1 + 2*k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: eq.
    move=> H.
    exists (j, (x, y)).
    rewrite H /=.
    lia.
  rewrite inE => [/eqP ->].
  case=> [] [] k /=.
  rewrite -mulrA -[2 * _]mulrC -mulrA => eq.
  have {eq}: (2^+x * 3^+y) = 2*k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: eq.
  case: x; first admit; move=> x.
  rewrite exprS => eq.
  (have {eq} <-: 2 ^+ x * 3 ^+ y = k by lia) => [H].
  exists (l, (x, y)).
  rewrite H /=.
  lia.
- rewrite inE => /orP [/eqP ->|].
    case=> [] [] k /=.
    rewrite -mulrA -[3 * _]mulrC -mulrA -{2}[m]mulr1 -addrA -mulrDr => eq.
    rewrite -{1}[m]mulr1 -addrA -mulrDr.
    have <-: (2^+x * 3^+y) = 1 + 3*k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: eq.
    move=> H.
    exists (j, (x, y)).
    rewrite H /=.
    lia.
  rewrite inE => /orP [/eqP ->|].
    case=> [] [] k /=.
    rewrite -mulrA -[3 * _]mulrC -mulrA -addrA -[2 * _]mulrC -mulrDr => eq.
    rewrite -addrA -mulrDr.
    have <-: (2^+x * 3^+y) = 2 + 3*k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite machine_length; have := ltn_ord pos; lia.
      exact: eq.
    move=> H.
    exists (j, (x, y)).
    rewrite H /=.
    lia.
  rewrite inE => [/eqP ->].
  case=> [] [] k /=.
  rewrite -mulrA -[3 * _]mulrC -mulrA => eq.
  have {eq}: (2^+x * 3^+y) = 3*k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite machine_length; have := ltn_ord pos; lia.
    exact: eq.
  case: y; first admit; move=> y.
  rewrite exprS => eq.
  (have {eq} <-: 2 ^+ x * 3 ^+ y = k by lia) => [H].
  exists (l, (x, y)).
  rewrite H /=.
  lia.
Admitted.

Lemma affineStep_preserves_encoding_rev : forall s y,
  affineStep y (state_encoding s) -> exists s', y = state_encoding s'.
Proof.
move=> [i [x y]] z.
case=> [[[p q] [p' q']]] [].
move=> /flattenP [] transitions /mapP [] pos _ ->.
set instr := lm2_instr_at M pos.
elim: instr => [j|j|j l|j l].
- rewrite inE => [/eqP -> /=].
  case=> [] [] k /[swap].
  rewrite -mulrA [2 * _]mulrC -[_ * 2 * _]mulrA => eq.
  have H: (2^+x * 3^+y) = 2 * k.
    apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: eq.
  move=> H'.
  case: x eq H; first admit; move=> x.
  exists (lm2_addr_instr pos, (x, y)).
  rewrite H' /=.
  move: H; rewrite exprS => H.
  have {H} <-: 2 ^+ x * 3 ^+ y = k by lia.
  lia.
- rewrite inE => /eqP -> /=.
  case=> [] [] k /[swap].
  rewrite -mulrA [3 * _]mulrC -[_ * 3 * _]mulrA => eq.
  have H: (2^+x * 3^+y) = 3 * k.
    apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: eq.
  move=> H'.
  case: y eq H; first admit; move=> y.
  exists (lm2_addr_instr pos, (x, y)).
  rewrite H' /=.
  move: H; rewrite exprS => H.
  have {H} <-: 2 ^+ x * 3 ^+ y = k by lia.
  lia.
- rewrite inE => /orP [/eqP -> /=|].
    case=> [] [] k /[swap].
    rewrite -mulrA -[2 * _]mulrC -mulrA -{2}[m]mulr1 -addrA -mulrDr => eq.
    rewrite -{1}[m]mulr1 -addrA -mulrDr.
    have <-: (2^+x * 3^+y) = 1 + 2*k.
      apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: eq.
    move=> H.
    exists (lm2_addr_instr pos, (x, y)).
    rewrite H /=.
    lia.
  rewrite inE => /eqP -> /=.
  case=> [] [] k /[swap].
  rewrite -mulrA [2 * _]mulrC -[_ * 2 * _]mulrA => eq.
  have H: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) (address_encoding l) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: eq.
  move=> H'.
  exists (lm2_addr_instr pos, (x.+1, y)).
  rewrite H' /= exprS.
  lia.
- rewrite inE => /orP [/eqP -> /=|].
    case=> [] [] k /[swap].
    rewrite -mulrA -[3 * _]mulrC -mulrA -{2}[m]mulr1 -addrA -mulrDr => eq.
    rewrite -{1}[m]mulr1 -addrA -mulrDr.
    have <-: (2^+x * 3^+y) = 1 + 3*k.
      apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: eq.
    move=> H.
    exists (lm2_addr_instr pos, (x, y)).
    rewrite H /=.
    lia.
  rewrite inE => /orP [/eqP -> /=|].
    case=> [] [] k /[swap].
    rewrite -mulrA -[3 * _]mulrC -mulrA [2 * _]mulrC -addrA -mulrDr => eq.
    rewrite -addrA -mulrDr.
    have <-: (2^+x * 3^+y) = 2 + 3*k.
      apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: eq.
    move=> H.
    exists (lm2_addr_instr pos, (x, y)).
    rewrite H /=.
    lia.
  rewrite inE => /eqP -> /=.
  case=> [] [] k /[swap].
  rewrite -mulrA [3 * _]mulrC -[_ * 3 * _]mulrA => eq.
  have H: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) (address_encoding l) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: eq.
  move=> H'.
  exists (lm2_addr_instr pos, (x, y.+1)).
  rewrite H' /= exprS.
  lia.
Admitted.

Lemma affineSteps_equiv_lm2Steps : forall s s',
  (clos_refl_sym_trans _ affineStep (state_encoding s) (state_encoding s'))
    <->
  (clos_refl_sym_trans _ lm2_step s s').
Proof.
move=> s s'; split.
- move=> /clos_rst_rst1n_iff H; dependent induction H.
    move: x => /state_encoding_injective ->.
    exact /rst_refl.
  case: H => /[dup] H.
  - move=> /affineStep_preserves_encoding [] s'' y_decoding.
    apply /(rst_trans _ _ _ s'').
      apply /rst_step.
      apply /(affineStep_equiv_lm2Step s s'').
      rewrite -y_decoding.
      exact H.
    by apply: IHclos_refl_sym_trans_1n.
  - move=> /affineStep_preserves_encoding_rev [] s'' y_decoding.
    apply /(rst_trans _ _ _ s'').
      apply /rst_sym /rst_step.
      apply /(affineStep_equiv_lm2Step s'' s).
      rewrite -y_decoding.
      exact H.
    by apply: IHclos_refl_sym_trans_1n.
- move=> /clos_rst_rst1n_iff; elim.
    move=> x; exact /rst_refl.
  move=> x y z [] ? ? ?.
  - apply /(rst_trans _ _ _ (state_encoding y)) => //.
    exact /rst_step /affineStep_equiv_lm2Step.
  - apply /(rst_trans _ _ _ (state_encoding y)) => //.
    exact /rst_sym /rst_step /affineStep_equiv_lm2Step.
(* Unset Printing Notations.
Qed. *)
Admitted.

Lemma lm2Step_det: forall x y y',
  lm2_step x y -> lm2_step x y' -> y = y'.
Proof.
move=> [i [x y]] [j [w t]] [j' [w' t']].
elim: i => //.
move=> p.
rewrite /lm2_step /=.
set instr := lm2_instr_at M p.
dependent induction instr.
- by do ! case=> [->].
- by do ! case=> [->].
- dependent induction x;
  by do ! case=> [->].
- dependent induction y;
  by do ! case=> [->].
Qed.

(* Note: copied from mm2_steps_confluent *)
Lemma lm2Steps_confluent : forall x y y',
            (clos_refl_trans _ lm2_step x y) -> (clos_refl_trans _ lm2_step x y') ->
  exists z, (clos_refl_trans _ lm2_step y z) /\ (clos_refl_trans _ lm2_step y' z).
Proof.
move=> x y y'.
move=> /clos_rt_rt1n_iff H; elim: H y'.
- move=> *. eexists. by split; [|apply rt_refl].
- move=> ? {}y1 z1 Hx /clos_rt_rt1n_iff Hyz IH ? /clos_rt_rt1n_iff Hxy2.
  case: Hxy2 Hx IH.
  + move=> ? _. eexists. split; [apply: rt_refl|].
    apply: rt_trans; [apply: rt_step|]; by eassumption.
  + move=> y2 z2 /lm2Step_det Hx /clos_rt_rt1n_iff Hy2z2 /Hx {Hx} ? IH.
    subst y2. move: Hy2z2 => /IH [z [??]].
    by exists z.
Qed.

Lemma ending_state_is_dead_end : forall x,
    (clos_refl_trans _ lm2_step ending_state x) -> x = ending_state.
Proof.
move=> x.
move /clos_rt_rt1n_iff => H.
dependent induction H => //.
Qed.

Lemma lm2Steps_to_stop_is_reversible : forall s,
  (clos_refl_trans _ lm2_step s ending_state)
    <->
  (clos_refl_sym_trans _ lm2_step s ending_state).
Proof.
move=> s; split.
  move=> ?; exact /clos_rt_clos_rst.
move /clos_rst_rst1n_iff.
move=> H; dependent induction H; first by apply /rt_refl.
case: H.
- move=> ?; apply /(rt_trans _ _ _ y); first exact: rt_step.
  exact: IHclos_refl_sym_trans_1n.
- move=> H1.
  have H2 : clos_refl_trans _ lm2_step y ending_state; first exact: IHclos_refl_sym_trans_1n.
  case: (lm2Steps_confluent (rt_step _ _ _ _ H1) H2) => w [] /[swap] ?.
  have : w = ending_state; last by move=> ->.
  exact: ending_state_is_dead_end.
Qed.

End Reduction.

Lemma equivalence_problem_reduction : LM2_HALTS_uncurried ⪯ equivalence_problem_uncurried.
Proof.
exists (fun args =>
  @reduction_output
    (lm2_halts_arguments_n args) (lm2_halts_arguments_ne0 args)
    (lm2_halts_arguments_M args)
    (lm2_halts_arguments_x args) (lm2_halts_arguments_y args)
).
move=> [n M ne0 x y]; split.
- move=> H.
  rewrite /equivalence_problem_uncurried /reduction_output /equivalence_problem /=.
  (* I can't get the ending state encoding not to simplify -_- *)
  have ->: (0%Z + (size M).+1 * 2 ^+ 0 * 3 ^+ 0) = (state_encoding M (ending_state n)) by done.
  apply /affineSteps_equiv_lm2Steps => //.
  apply /lm2Steps_to_stop_is_reversible.
  exact: H.
- rewrite /equivalence_problem_uncurried /reduction_output.
  move=> H.
  rewrite /LM2_HALTS_uncurried /LM2_HALTS /=.
  rewrite lm2Steps_to_stop_is_reversible /=.
  exact /affineSteps_equiv_lm2Steps.
Qed.

Theorem equivalence_problem_undecidable : undecidable equivalence_problem_uncurried.
Proof.
apply: (undecidability_from_reducibility LM2_HALTS_undec).
exact: equivalence_problem_reduction.
Qed.
