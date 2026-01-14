From HB Require Import structures.
From Undecidability.Synthetic Require Import Undecidability.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype.
From mathcomp Require Import all_algebra eqtype fintype ssrnat intdiv prime.
From mathcomp Require Import ring lra zify.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Stdlib.Program Require Import Equality.

From GWP Require Import LM2 ReductionUtils.

Import GRing.Theory.
Open Scope int_scope.
Open Scope ring_scope.

Record nzint := {
  nzint_val :> int;
  nzint_non_nul: nzint_val != 0;
}.

Definition nzint_eq_op (x y: nzint) := (x == y :> int).
Lemma nzint_eqP x y: reflect (x = y) (nzint_eq_op x y).
Proof.
apply /(iffP idP) => [|->].
- rewrite /nzint_eq_op.
  case: x => [x x_non_null] /=.
  case: y => [y y_non_null] /=.
  move=> /eqP H.
  move: x_non_null.
  move: y_non_null.
  rewrite H => eq1 eq2.
  by rewrite (bool_irrelevance eq1 eq2).
- by rewrite /nzint_eq_op eq_refl.
Qed.

HB.instance Definition _ := hasDecEq.Build nzint nzint_eqP.

Definition State := (int * nzint) % type.
Definition Transition := (State * State) % type.
Definition Machine := seq Transition.

Section Affine.
Variable A: Machine.

(* Whether `t: Transition` is a transition of `A: Machine` *)
Definition isTransitionOf (t: Transition) := t \in A.

Definition transitionStep (t: Transition) a b :=
  (isTransitionOf t) /\ (
    let '((p, q), (p', q')) := t in
    exists (z: int), (a == p + (q: int)*z) && (b == p' + (q': int)*z)
  ).

Definition affineStep a b := exists (t: Transition), transitionStep t a b.

End Affine.

(* The equivalence problem. *)
Definition equivalence_problem (A: Machine) (m z: int) : Prop := clos_refl_sym_trans _ (affineStep A) m z.
Definition equivalence_problem_uncurried := fun '(A, m, z) => equivalence_problem A m z.

Section Reduction.

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

Definition m_as_nzint: nzint.
Proof. exists m; lia. Defined.
Definition m2_as_nzint: nzint.
Proof. exists (2 * m); lia. Defined.
Definition m3_as_nzint: nzint.
Proof. exists (3 * m); lia. Defined.

(* encodes the instruction `instr` at address `i` *)
Definition instruction_encoding (instr: lm2_instr) (i: 'I_n) : list Transition :=
  let i: int := address_encoding (lm2_addr_instr i) in
  match instr with
  | lm2_inc_x j => [:: ((i, m_as_nzint), ((address_encoding j)%:Z, m2_as_nzint))]
  | lm2_inc_y j => [:: ((i, m_as_nzint), ((address_encoding j)%:Z, m3_as_nzint))]
  | lm2_dec_x j k => let j := (address_encoding j)%:Z in let k := (address_encoding k)%:Z in [::
      (* i + m(2z + 1) -> k + m(2z + 1) : x is zero, continue to j *)
      ((i + m, m2_as_nzint), (j + m, m2_as_nzint));

      (* i + 2mz -> k + mz : x is not-zero, decrement and jump to k *)
      ((i, m2_as_nzint), (k, m_as_nzint))
    ]
  | lm2_dec_y j k => let j := (address_encoding j)%:Z in let k := (address_encoding k)%:Z in [::
      (* i + m(3z + 1) -> j + m(3z + 1) : y is zero, continue to j *)
      ((i + m, m3_as_nzint), (j + m, m3_as_nzint));
      (* i + m(3z + 2) -> j + m(3z + 2) : y is zero, continue to j *)
      ((i + 2 * m, m3_as_nzint), (j + 2 * m, m3_as_nzint));

      (* i + 3mz -> k + mz : y is not-zero, decrement and jump to k *)
      ((i, m3_as_nzint), (k, m_as_nzint))
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

Lemma power2_mod_3 x: (2 ^+ x %% 3)%Z = 1 \/ (2 ^+ x %% 3)%Z = 2.
Proof.
elim: x => [|x].
  rewrite expr0 modz_small; last lia.
  by left.
rewrite exprS -modzMmr; case=> ->; do [by right|by left].
Qed.

Lemma lm2Step_to_affineStep : forall s s',
  (lm2_step s s') -> (affineStepEncoding s s').
Proof.
move=> [i [x y]] [i' [x' y']].
elim: i; rewrite /lm2_step //=.
move=> pos.
set instr := lm2_instr_at M pos.
have: instr = lm2_instr_at M pos by done.
elim: instr => [
  j instr_at_pos /andP [[/andP [/eqP -> /eqP ->]] /eqP ->] |
  j instr_at_pos /andP [[/andP [/eqP -> /eqP ->]] /eqP ->] |
  j k instr_at_pos |
  j k instr_at_pos
].
- (* inc_x *)
  exists (((address_encoding (lm2_addr_instr pos))%:Z, m_as_nzint), ((address_encoding j)%:Z, m2_as_nzint)).
  split.
    apply /flattenP.
    exists (instruction_encoding (lm2_inc_x j) pos); last first.
      rewrite inE //=.
    rewrite instr_at_pos.
    apply /mapP; exists pos => //.
    by rewrite mem_enum.
  exists (2^+x * 3^+y) => /=.
  by rewrite exprS /=; lia.
- (* inc_y *)
  exists (((address_encoding (lm2_addr_instr pos))%:Z, m_as_nzint), ((address_encoding j)%:Z, m3_as_nzint)).
  split.
    apply /flattenP.
    exists (instruction_encoding (lm2_inc_y j) pos); last first.
      rewrite inE //=.
    rewrite instr_at_pos.
    apply /mapP; exists pos => //.
    by rewrite mem_enum.
  exists (2^+x * 3^+y) => /=.
  by rewrite exprS; lia.
- (* dec_x *)
  case: x => [/andP [[/andP [/eqP -> /eqP ->]] /eqP ->]|l /andP [[/andP [/eqP -> /eqP ->]] /eqP ->]].
  - exists (((address_encoding (lm2_addr_instr pos))%:Z + m, m2_as_nzint), ((address_encoding j)%:Z + m, m2_as_nzint)).
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
    exists ((2^+0 * 3^+y) %/ 2)%Z => /=.
    rewrite -mulrA {1}(divz_eq (2^+0 * 3^+y) 2) remainder_1 /=.
    lia.
  - exists (((address_encoding (lm2_addr_instr pos))%:Z, m2_as_nzint), ((address_encoding k)%:Z, m_as_nzint)).
    split.
      apply /flattenP.
      exists (instruction_encoding (lm2_dec_x j k) pos); last first.
        by rewrite inE; apply /orP; right; rewrite inE.
      rewrite instr_at_pos.
      apply /mapP; exists pos => //.
      by rewrite mem_enum.
    exists (2 ^+ l * 3 ^+ y) => /=.
    rewrite exprS; lia.
- (* dec_y *)
  case: y => [/andP [[/andP [/eqP -> /eqP ->]] /eqP ->]|l /andP [[/andP [/eqP -> /eqP ->]] /eqP ->]].
  - have []: ((2 ^+ x * 3 ^+ 0) %% 3)%Z = 1 \/ ((2 ^+ x * 3 ^+ 0) %% 3)%Z = 2.
      rewrite expr0 mulr1.
      exact: power2_mod_3.
    - move=> remainder.
      exists (((address_encoding (lm2_addr_instr pos))%:Z + m, m3_as_nzint), ((address_encoding j)%:Z + m, m3_as_nzint)).
      split.
        apply /flattenP.
        exists (instruction_encoding (lm2_dec_y j k) pos); last first.
          by rewrite inE; apply /orP; left.
        rewrite instr_at_pos.
        apply /mapP; exists pos => //.
        by rewrite mem_enum.
      exists ((2 ^+ x * 3 ^+ 0) %/ 3)%Z => /=.
      rewrite -mulrA {1}(divz_eq (2^+x * 3^+0) 3) remainder; lia.
    - move=> remainder.
      exists (((address_encoding (lm2_addr_instr pos))%:Z + 2 * m, m3_as_nzint), ((address_encoding j)%:Z + 2 * m, m3_as_nzint)).
      split.
        apply /flattenP.
        exists (instruction_encoding (lm2_dec_y j k) pos); last first.
          by rewrite inE; apply /orP; right; rewrite inE; apply /orP; left.
        rewrite instr_at_pos.
        apply /mapP; exists pos => //.
        by rewrite mem_enum.
      exists ((2 ^+ x * 3 ^+ 0) %/ 3)%Z => /=.
      rewrite -mulrA {1}(divz_eq (2^+x * 3^+0) 3) remainder; lia.
  - exists (((address_encoding (lm2_addr_instr pos))%:Z, m3_as_nzint), ((address_encoding k)%:Z, m_as_nzint)).
    split.
      apply /flattenP.
      exists (instruction_encoding (lm2_dec_y j k) pos); last first.
        by rewrite inE; apply /orP; right; rewrite inE; apply /orP; right; rewrite inE.
      rewrite instr_at_pos.
      apply /mapP; exists pos => //.
      by rewrite mem_enum.
    exists (2 ^+ x * 3 ^+ l) => /=.
    rewrite exprS; lia.
Qed.

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
rewrite (eqP machine_length).
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

Lemma power3_mod2 x: ((3 ^+ x) %% 2)%Z = 1.
Proof.
elim: x => [|x]; first by rewrite expr0.
rewrite exprS -modzMm => ->.
by rewrite mulr1.
Qed.

Lemma affineStep_to_lm2Step : forall s s',
  (affineStepEncoding s s') -> (lm2_step s s').
Proof.
move=> [i [x y]] [i' [x' y']].
case=> [[[p q] [p' q']]] [].
move=> /flattenP [] transitions /mapP [] pos _.
move=> -> trans_is_encoded [] /= k /andP [].
move: trans_is_encoded.
set instr := lm2_instr_at M pos.
have: instr = lm2_instr_at M pos by done.
elim: instr => [j instr_at_pos|j instr_at_pos|j l instr_at_pos|j l instr_at_pos].
- rewrite inE => /eqP [] -> -> -> ->.
  rewrite -mulrA.
  have ->: 2 * m * k = m * (2 * k) by lia.
  rewrite -mulrA => /eqP s_eq /eqP s'_eq.
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
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
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
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
    exact: s_eq.
  move=> {s_eq} {s'_eq}; elim: i => [/=|pos' /= /eqP].
    lia.
  rewrite eqSS.
  move=> /eqP /ord_inj -> {pos'}.
  by rewrite /lm2_step/= -instr_at_pos !eq_refl.
- rewrite inE.
  move=> /eqP [] -> -> -> ->.
  rewrite -mulrA.
  have ->: 3 * m * k = m * (3 * k) by lia.
  rewrite -mulrA => /eqP s_eq /eqP s'_eq.
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
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
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
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
    exact: s_eq.
  move=> {s_eq} {s'_eq}; elim: i.
    move=> /=; lia.
  move=> pos' /= /eqP.
  rewrite eqSS.
  move=> /eqP /ord_inj -> {pos'}.
  by rewrite /lm2_step/= -instr_at_pos !eq_refl.
- rewrite inE; move=> /orP; case.
  - move=> /eqP [] -> -> -> ->.
    rewrite -![m * _ * _]mulrA.
    have ->: 2 * m * k = m * (2 * k) by lia.
    rewrite -{2 5}[m]mulr1 -!addrA -!mulrDr => /eqP s_eq /eqP s'_eq.
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
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: s_eq.
    have x_eq_0: x = 0.
      case: x {s_eq} H => // x H.
      have: 2 ^+ x.+1 * 3 ^+ y = 1 + 2 * k %[mod 2] by rewrite H.
      rewrite -modzDm modzMr addr0 exprS.
      rewrite -mulrA modzMr.
      have ->: ((1 %% 2)%Z %% 2)%Z = 1 by done.
      lia.
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
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: s_eq.
    move=> {s_eq} {s'_eq}; elim: i.
      move=> /=; lia.
    move=> pos' /= /eqP.
    rewrite eqSS.
    move=> /eqP /ord_inj -> {pos'}.
    rewrite /lm2_step/= -instr_at_pos.
    by rewrite x_eq_0 !eq_refl.
  - rewrite inE; move=> /eqP [] -> -> -> ->.
    rewrite -![m * _ * _]mulrA.
    have ->: 2 * m * k = m * (2 * k) by lia.
    move=> /eqP s_eq /eqP s'_eq.
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
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: s_eq.
    move: s'_eq s_eq H.
    case: x => [_ _|x].
      rewrite expr0 mul1r => H.
      have {H}: 3 ^+ y = 2 * k %[mod 2] by rewrite H.
      rewrite modzMr power3_mod2.
      lia.
    move=> s'_eq s_eq H.
    have {H}: (2^+x * 3^+y) = k.
      apply /(simplify_quotient (address_encoding i) pos.+1 (m * 2)).
      move: (address_encoding_bound i); lia.
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
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
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: s_eq.
    move=> {s_eq} {s'_eq}; elim: i.
      move=> /=; lia.
    move=> pos' /= /eqP.
    rewrite eqSS.
    move=> /eqP /ord_inj -> {pos'}.
    by rewrite /lm2_step/= -instr_at_pos !eq_refl.
- rewrite inE; move=> /orP; case.
    move=> /eqP [] -> -> -> ->.
    rewrite -![m * _ * _]mulrA.
    have ->: 3 * m * k = m * (3 * k) by lia.
    rewrite -{2 5}[m]mulr1 -!addrA -!mulrDr => /eqP s_eq /eqP s'_eq.
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
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: s_eq.
    have y_eq_0: y = 0.
      case: y {s_eq} H => // y H.
      have: 2 ^+ x * 3 ^+ y.+1 = 1 + 3 * k %[mod 3] by rewrite H.
      rewrite -modzDm modzMr addr0 exprS.
      rewrite -modzMm -[((3 * 3 ^+ _) %% 3)%Z]modzMm.
      rewrite modzz mul0r mod0z mulr0 mod0z.
      have <-: 1 = ((1 %% 3)%Z %% 3)%Z by done.
      lia.
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
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: s_eq.
    move=> {s_eq} {s'_eq}; elim: i.
      move=> /=; lia.
    move=> pos' /= /eqP.
    rewrite eqSS.
    move=> /eqP /ord_inj -> {pos'}.
    rewrite /lm2_step/= -instr_at_pos.
    by rewrite y_eq_0 !eq_refl.
  rewrite inE; move=> /orP; case.
    move=> /eqP [] -> -> -> ->.
    rewrite -![m * _ * _]mulrA.
    have ->: 3 * m * k = m * (3 * k) by lia.
    rewrite -!addrA [2 * _]mulrC -!mulrDr => /eqP s_eq /eqP s'_eq.
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
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: s_eq.
    have y_eq_0: y = 0.
      case: y {s_eq} H => // y H.
      have: 2 ^+ x * 3 ^+ y.+1 = 2 + 3 * k %[mod 3] by rewrite H.
      rewrite -modzDm modzMr addr0 exprS.
      rewrite -modzMm -[((3 * 3 ^+ _) %% 3)%Z]modzMm.
      rewrite modzz mul0r mod0z mulr0 mod0z.
      have <-: 2 = ((2 %% 3)%Z %% 3)%Z by done.
      lia.
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
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: s_eq.
    move=> {s_eq} {s'_eq}; elim: i.
      move=> /=; lia.
    move=> pos' /= /eqP.
    rewrite eqSS.
    move=> /eqP /ord_inj -> {pos'}.
    rewrite /lm2_step/= -instr_at_pos.
    by rewrite y_eq_0 !eq_refl.
  rewrite inE; move=> /eqP [] -> -> -> ->.
  rewrite -![m * _ * _]mulrA.
  have ->: 3 * m * k = m * (3 * k) by lia.
  move=> /eqP s_eq /eqP s'_eq.
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
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
    exact: s_eq.
  move: s'_eq s_eq H.
  case: y => [_ _|y].
    rewrite expr0 mulr1 => H.
    have {H}: 2 ^+ x = 3 * k %[mod 3] by rewrite H.
    rewrite modzMr.
    have [->|->] := power2_mod_3 x; lia.
  move=> s'_eq s_eq H.
  have {H}: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) pos.+1 (m * 3)).
    move: (address_encoding_bound i); lia.
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
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
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
    exact: s_eq.
  move=> {s_eq} {s'_eq}; elim: i.
    move=> /=; lia.
  move=> pos' /= /eqP.
  rewrite eqSS.
  move=> /eqP /ord_inj -> {pos'}.
  by rewrite /lm2_step /= -instr_at_pos !eq_refl.
Qed.

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

Lemma affineStep_preserves_encoding : forall s y,
  affineStep (state_encoding s) y -> exists s', state_encoding s' = y.
Proof.
move=> [i [x y]] z.
case=> [[[p q] [p' q']]] [].
move=> /flattenP [] transitions /mapP [] pos _ ->.
set instr := lm2_instr_at M pos.
elim: instr => [j|j|j l|j l].
- rewrite inE => /eqP [-> -> -> ->] /=.
  case=> k.
  move=> /andP [] /eqP eq.
  have <-: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
    rewrite mulrA; exact: eq.
  move=> /eqP ->.
  exists (j, (x.+1, y)) => /=.
  rewrite exprS; lia.
- rewrite inE => /eqP [-> -> -> ->] /=.
  case=> k.
  move=> /andP [] /eqP eq.
  have <-: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
    rewrite mulrA; exact: eq.
  move=> /eqP ->.
  exists (j, (x, y.+1)) => /=.
  rewrite exprS; lia.
- rewrite inE => /= /orP [/eqP [-> -> -> ->]|].
    case=> k /=.
    rewrite [2 * _]mulrC -!mulrA -{2}[m]mulr1 -{4}[m]mulr1 -!addrA -!mulrDr.
    move=> /andP [] /eqP /= eq.
    have <-: (2^+x * 3^+y) = 1 + 2*k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: eq.
    move=> /eqP ->.
    exists (j, (x, y)) => /=.
    lia.
  rewrite inE => /= [/eqP [-> -> -> ->]].
  case=> k /=.
  rewrite [2 * _]mulrC -!mulrA.
  move=> /andP [] /eqP /= eq.
  have {eq}: (2^+x * 3^+y) = 2*k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
    exact: eq.
  case: x => [|x].
    rewrite expr0 mul1r => H.
    have {H}: 3 ^+ y = 2 * k %[mod 2] by rewrite H.
    rewrite modzMr power3_mod2.
    lia.
  rewrite exprS => eq.
  (have {eq} <-: 2 ^+ x * 3 ^+ y = k by lia) => [H].
  exists (l, (x, y)) => /=.
  lia.
- rewrite inE => /= /orP [/eqP [-> -> -> ->]|].
    case=> k /=.
    rewrite -mulrA -[3 * _]mulrC -mulrA -{2}[m]mulr1 -{4}[m]mulr1 -!addrA -!mulrDr.
    move=> /andP [] /eqP /= eq.
    have <-: (2^+x * 3^+y) = 1 + 3*k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: eq.
    exists (j, (x, y)) => /=.
    lia.
  rewrite inE => /orP [/eqP [-> -> -> ->]|].
    case=> k /=.
    rewrite -mulrA -[3 * _]mulrC -mulrA -addrA -![2 * _]mulrC -!addrA -!mulrDr.
    move=> /andP [] /eqP /= eq.
    have <-: (2^+x * 3^+y) = 2 + 3*k.
      apply /(simplify_quotient (address_encoding i) pos.+1 m).
      exact: address_encoding_bound.
      by rewrite (eqP machine_length); have := ltn_ord pos; lia.
      exact: eq.
    exists (j, (x, y)) => /=.
    lia.
  rewrite inE => /= [/eqP [-> -> -> ->]].
  case=> k.
  rewrite -!mulrA -[3 * _]mulrC -mulrA -[_ * 3]mulrC.
  move=> /andP [] /eqP /= eq.
  have {eq}: (2^+x * 3^+y) = 3*k.
    apply /(simplify_quotient (address_encoding i) pos.+1 m).
    exact: address_encoding_bound.
    by rewrite (eqP machine_length); have := ltn_ord pos; lia.
    exact: eq.
  case: y => [|y].
    rewrite expr0 mulr1 => H.
    have {H}: 2 ^+ x = 3 * k %[mod 3] by rewrite H.
    rewrite modzMr.
    have [->|->] := power2_mod_3 x; lia.
  rewrite exprS => eq.
  have {eq} <-: 2 ^+ x * 3 ^+ y = k; first lia; move=> /eqP ->.
  exists (l, (x, y)) => /=.
  lia.
Qed.

Lemma affineStep_preserves_encoding_rev : forall y s,
  affineStep y (state_encoding s) -> exists s', state_encoding s' = y.
Proof.
move=> z [i [x y]].
case=> [[[p q] [p' q']]] [].
move=> /flattenP [] transitions /mapP [] pos _ ->.
set instr := lm2_instr_at M pos.
elim: instr => [j|j|j l|j l].
- rewrite inE => /= [/eqP [-> -> -> ->]].
  case=> k /=.
  rewrite -mulrA [2 * _]mulrC -[_ * 2 * _]mulrA.
  move=> /andP [] /eqP -> /eqP /= eq.
  have H: (2^+x * 3^+y) = 2 * k.
    apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: eq.
  case: x eq H => [_|x eq H].
    rewrite expr0 mul1r => H.
    have {H}: 3 ^+ y = 2 * k %[mod 2] by rewrite H.
    rewrite modzMr power3_mod2.
    lia.
  exists (lm2_addr_instr pos, (x, y)) => /=.
  move: H; rewrite exprS => H.
  have {H} <-: 2 ^+ x * 3 ^+ y = k by lia.
  lia.
- rewrite inE => /= [/eqP [-> -> -> ->]].
  case=> k /=.
  rewrite -mulrA [3 * _]mulrC -[_ * 3 * _]mulrA.
  move=> /andP [] /eqP -> /eqP /= eq.
  have H: (2^+x * 3^+y) = 3 * k.
    apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: eq.
  case: y eq H => [_|y eq H].
    rewrite expr0 mulr1 => H.
    have {H}: 2 ^+ x = 3 * k %[mod 3] by rewrite H.
    rewrite modzMr.
    have [->|->] := power2_mod_3 x; lia.
  exists (lm2_addr_instr pos, (x, y)) => /=.
  move: H; rewrite exprS => H.
  have {H} <-: 2 ^+ x * 3 ^+ y = k by lia.
  lia.
- rewrite inE => /= /orP [/eqP [-> -> -> ->]|].
    case=> k.
    rewrite -!mulrA -![2 * _]mulrC -!mulrA -{1}[m]mulr1 -{4}[m]mulr1 -!addrA -!mulrDr.
    move=> /andP [] /eqP -> /eqP /= eq.
    have <-: (2^+x * 3^+y) = 1 + k * 2.
      apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: eq.
    exists (lm2_addr_instr pos, (x, y)) => /=.
    lia.
  rewrite inE => /= /eqP [-> -> -> ->].
  case=> k /=.
  rewrite [2 * _]mulrC -!mulrA.
  move=> /andP [] /eqP -> /eqP /= eq.
  have H: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) (address_encoding l) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: eq.
  exists (lm2_addr_instr pos, (x.+1, y)) => /=.
  rewrite exprS; lia.
- rewrite inE => /= /orP [/eqP [-> -> -> ->]|].
    case=> k /=.
    rewrite -![3 * _]mulrC -!mulrA -{1}[m]mulr1 -{4}[m]mulr1 -!addrA -!mulrDr.
    move=> /andP [] /eqP -> /eqP /= eq.
    have <-: (2^+x * 3^+y) = 1 + 3 * k.
      apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: eq.
    exists (lm2_addr_instr pos, (x, y)) => /=.
    lia.
  rewrite inE => /= /orP [/eqP [-> -> -> ->]|].
    case=> k /=.
    rewrite -![3 * _]mulrC -!mulrA -![2 * _]mulrC -!addrA -!mulrDr.
    move=> /andP [] /eqP -> /eqP /= eq.
    have <-: (2^+x * 3^+y) = 2 + 3 * k.
      apply /(simplify_quotient (address_encoding i) (address_encoding j) m).
      exact: address_encoding_bound.
      exact: address_encoding_bound.
      exact: eq.
    exists (lm2_addr_instr pos, (x, y)) => /=.
    lia.
  rewrite inE => /= /eqP [-> -> -> ->].
  case=> k /=.
  rewrite [3 * _]mulrC -!mulrA.
  move=> /andP [] /eqP -> /eqP /= eq.
  have H: (2^+x * 3^+y) = k.
    apply /(simplify_quotient (address_encoding i) (address_encoding l) m).
    exact: address_encoding_bound.
    exact: address_encoding_bound.
    exact: eq.
  exists (lm2_addr_instr pos, (x, y.+1)) => /=.
  rewrite exprS; lia.
Qed.

Lemma affineSteps_equiv_lm2Steps : forall s s',
  (clos_refl_sym_trans _ affineStep (state_encoding s) (state_encoding s'))
    <->
  (clos_refl_sym_trans _ lm2_step s s').
Proof.
move=> s s'; apply: closRST_R_equiv_R'.
- exact: state_encoding_injective.
- exact: affineStep_equiv_lm2Step.
- exact: affineStep_preserves_encoding.
- exact: affineStep_preserves_encoding_rev.
Qed.

Lemma lm2Step_det: forall x y y',
  lm2_step x y -> lm2_step x y' -> y = y'.
Proof.
move=> [i [x y]] [j [w t]] [j' [w' t']].
elim: i => //.
move=> p.
rewrite /lm2_step /=.
set instr := lm2_instr_at M p.
dependent induction instr.
- by do ! move=> /andP [/andP [/eqP -> /eqP ->]] /eqP ->.
- by do ! move=> /andP [/andP [/eqP -> /eqP ->]] /eqP ->.
- dependent induction x;
  by do ! move=> /andP [/andP [/eqP -> /eqP ->]] /eqP ->.
- dependent induction y;
  by do ! move=> /andP [/andP [/eqP -> /eqP ->]] /eqP ->.
Qed.

Lemma lm2Steps_confluent : forall x y y',
            (clos_refl_trans _ lm2_step x y) -> (clos_refl_trans _ lm2_step x y') ->
  exists z, (clos_refl_trans _ lm2_step y z) /\ (clos_refl_trans _ lm2_step y' z).
Proof. exact /R_confluent /lm2Step_det. Qed.

Lemma ending_state_is_dead_end x:
    (clos_refl_trans _ lm2_step ending_state x) -> x = ending_state.
Proof. move /clos_rt_rt1n_iff => H; dependent induction H => //. Qed.

Lemma lm2Steps_to_stop_is_reversible : forall s,
  (clos_refl_trans _ lm2_step s ending_state)
    <->
  (clos_refl_sym_trans _ lm2_step s ending_state).
Proof. by apply /R_to_stop_is_reversible; [exact: lm2Steps_confluent|exact: ending_state_is_dead_end]. Qed.

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
