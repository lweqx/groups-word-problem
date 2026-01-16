From HB Require Import structures.
From Undecidability Require Import Synthetic.Definitions Synthetic.Undecidability.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra tuple.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.

From GWP Require Import Presentation AffineMachines F2 EquivalenceAlgebra Equivalence HNN.

(*
HB.factory Record isMorphismBase (G: group) (gens gens': seq G) (map: G -> G) := {
  mb_preserve_eq x y: x == y -> map x == map y;
  mb_preserve_e: map e == e;
  mb_preserve_gen x: List.In x gens -> List.In (map x) gens'
}.

HB.builders Context G gens gens' map of isMorphismBase G gens gens' map.

Let H := finGeneratedSubgroup gens.
Let H' := finGeneratedSubgroup gens'.

Definition map_extended (x: H): H'.
Proof.
case: x => [point_x] Hx.
induction Hx.
- exists (map x).
  exact /igs_gen /mb_preserve_gen.
- exact: e.
- exact: (IHHx1 @ IHHx2).
- exact: (inv IHHx).
Defined.

Lemma extension_preserve_e: map_extended e == e.
Proof. done. Qed.

Lemma extension_preserve_law x y: map_extended (x @ y) == (map_extended x) @ (map_extended y).
Proof. done. Qed.

Lemma extension_preserve_inv x: map_extended (inv x) == inv (map_extended x).
Proof. done. Qed.

Lemma extension_preserve_equiv' x:
  x == e -> map_extended x == e.
Proof.
Admitted.
(*
case: x => x x_in_subgroup Heq.
elim: x_in_subgroup Heq.
- move=> x' x'_in_gens /=.
  rewrite /eq/=/subgroupby_eq/=.
  rewrite -{2}map_preserve_e.
  exact: map_preserve_eq.
- by rewrite /eq/=/subgroupby_eq/=.
- rewrite /eq/=/subgroupby_eq/=.
  move=> x' y' x'_in_gens IHx'.
  move=> y'_in_gens IHy'.
  move=> Heq.
  transitivity (
    subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
      (map_extended
         (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) x' x'_in_gens))
      @
    subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
      (map_extended
         (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) y' y'_in_gens))
  ); first done.
  rewrite IHx' //.
  rewrite IHy' //.
- rewrite /eq/=/subgroupby_eq/=.
  move=> x' x'_in_gens IHx' Hinvx'.
  transitivity (
    inv (
      subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
        (map_extended
          (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) x' x'_in_gens))
    )
  ); first done.
  by rewrite -inv_e IHx' // -inv_e -[x']inv_involutive Hinvx'.
Admitted.
*)

Lemma extension_preserve_equiv x y:
  x == y -> map_extended x == map_extended y.
Proof.
have Heq: x @ (inv y) == e -> (map_extended x) @ (map_extended (inv y)) == e; last first.
  move=> H1.
  have {}H1: x @ (inv y) == e by rewrite H1 inverse_left.
  move: Heq => /(_ H1) {H1}.
  rewrite extension_preserve_inv => H1.
  transitivity (((map_extended x) @ (inv (map_extended y))) @ (map_extended y)).
    by rewrite -associativity inverse_right neutral_right.
  by rewrite H1 neutral_left.
move=> Heq.
rewrite -extension_preserve_law.
exact: extension_preserve_equiv'.
Qed.

HB.instance Definition _ := isMonoidMorphism.Build H H' map_extended extension_preserve_equiv extension_preserve_e extension_preserve_law.
HB.instance Definition _ := isInvMorphism.Build H H' map_extended extension_preserve_inv.

HB.end.
*)

Section MapSubgroupGens.
Variable G: group.
Variable gens gens': seq G.

Variable map: G -> G.
Hypothesis map_preserve_gen: forall x, List.In x gens -> List.In (map x) gens'.
(* these hypotheses are not minimal *)
Hypothesis map_preserve_eq: forall x y, x == y -> map x == map y.
Hypothesis map_preserve_e: map e == e.

Let H := finGeneratedSubgroup gens.
Let H' := finGeneratedSubgroup gens'.

Definition map_extended (x: H): H'.
Proof.
case: x => [point_x] Hx.
induction Hx.
- exists (map x).
  exact /igs_gen /map_preserve_gen.
- exact: e.
- exact: (IHHx1 @ IHHx2).
- exact: (inv IHHx).
Defined.

Lemma extension_preserve_e: map_extended e == e.
Proof. done. Qed.

Lemma extension_preserve_law x y: map_extended (x @ y) == (map_extended x) @ (map_extended y).
Proof. done. Qed.

Lemma extension_preserve_inv x: map_extended (inv x) == inv (map_extended x).
Proof. done. Qed.

Lemma extension_preserve_equiv' x:
  x == e -> map_extended x == e.
Proof.
Admitted.
(*
case: x => x x_in_subgroup Heq.
elim: x_in_subgroup Heq.
- move=> x' x'_in_gens /=.
  rewrite /eq/=/subgroupby_eq/=.
  rewrite -{2}map_preserve_e.
  exact: map_preserve_eq.
- by rewrite /eq/=/subgroupby_eq/=.
- rewrite /eq/=/subgroupby_eq/=.
  move=> x' y' x'_in_gens IHx'.
  move=> y'_in_gens IHy'.
  move=> Heq.
  transitivity (
    subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
      (map_extended
         (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) x' x'_in_gens))
      @
    subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
      (map_extended
         (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) y' y'_in_gens))
  ); first done.
  rewrite IHx' //.
  rewrite IHy' //.
- rewrite /eq/=/subgroupby_eq/=.
  move=> x' x'_in_gens IHx' Hinvx'.
  transitivity (
    inv (
      subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
        (map_extended
          (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) x' x'_in_gens))
    )
  ); first done.
  by rewrite -inv_e IHx' // -inv_e -[x']inv_involutive Hinvx'.
Admitted.
*)

Lemma extension_preserve_equiv x y:
  x == y -> map_extended x == map_extended y.
Proof.
have Heq: x @ (inv y) == e -> (map_extended x) @ (map_extended (inv y)) == e; last first.
  move=> H1.
  have {}H1: x @ (inv y) == e by rewrite H1 inverse_left.
  move: Heq => /(_ H1) {H1}.
  rewrite extension_preserve_inv => H1.
  transitivity (((map_extended x) @ (inv (map_extended y))) @ (map_extended y)).
    by rewrite -associativity inverse_right neutral_right.
  by rewrite H1 neutral_left.
move=> Heq.
rewrite -extension_preserve_law.
exact: extension_preserve_equiv'.
Qed.

HB.instance Definition _ := isMonoidMorphism.Build H H' map_extended extension_preserve_equiv extension_preserve_e extension_preserve_law.
HB.instance Definition _ := isInvMorphism.Build H H' map_extended extension_preserve_inv.

End MapSubgroupGens.

Record GWPArguments := {
  P : invertiblePresentationType;
  u : presented P;
  v : presented P;
}.
Definition GWP_uncurried args := word_problem (P args) (u args) (v args).

Section Reduction.

Variable A: Machine.
Variable z m: int.
Let n := size A.

Import PresentationNotations.
Import intZmod.

(* `encoding k` is `a_k = b^k a b^-k` *)
Definition encoding (k: int) : F2 := (power (`[b]: F2) k) @ `[a] @ (power (`[b]: F2) (oppz k)).

Definition affine_state_encoding_gens (s: State) := [::
    (encoding s.1);
    (power (`[b]: F2) s.2)
  ].
Definition affine_state_encoding (s: State) := finGeneratedSubgroup (affine_state_encoding_gens s).

Lemma catE {T: Type} (x y: seq T): x ++ y = (x ++ y)%list.
Proof. by elim: x => [//|a l /= ->]. Qed.

(*
Definition encoding_state_k (s: State) (k: int) : affine_state_encoding s.
Proof.
exists (
  (power (power (`[b]: F2) s.2) k) @ (encoding s.1) @ (power (power (`[b]: F2) s.2) (-k))
).
elim: k.
- rewrite power0.
  exists [:: encoding s.1]; split; last first.
    by rewrite /= neutral_left neutral_right.
  apply /List.Forall_cons /List.Forall_nil.
  rewrite /affine_state_encoding_gens.
  by apply /List.Exists_cons; left; left.
- move=> k; case=> decomp [? decomp_eq].
  exists (
    [:: (power (`[b]: F2) s.2)] ++
    decomp ++
    [:: (inv (power (`[b]: F2) s.2))]
  ); split; first last.
    rewrite !prod_cat -decomp_eq !prod1s !prod0 !neutral_right.
    rewrite !powerS powerC' !powerP -powerC''.
    rewrite associativity associativity.
    by rewrite [power (`[b]: F2) s.2 @ (_ @ _)]associativity [power (`[b]: F2) s.2 @ (_ @ _)]associativity.
  rewrite !catE List.Forall_app; split=> //.
    apply /List.Forall_cons; last by apply /List.Forall_nil.
    rewrite /affine_state_encoding_gens.
    apply /List.Exists_cons; right.
    by apply /List.Exists_cons; left; left.
  rewrite List.Forall_app; split=> //.
  apply /List.Forall_cons; last by apply /List.Forall_nil.
  rewrite /affine_state_encoding_gens.
  apply /List.Exists_cons; right.
  by apply /List.Exists_cons; left; right.
- move=> k; case=> decomp [? decomp_eq].
  rewrite opprK.
  exists (
    [:: (inv (power (`[b]: F2) s.2))] ++
    decomp ++
    [:: (power (`[b]: F2) s.2)]
  ); split; first last.
    rewrite !prod_cat -decomp_eq !prod1s !prod0 !neutral_right.
    rewrite !powerS !powerP opprK.
    by rewrite 2!associativity 2![(inv (power (`[b]: F2) s.2)) @ (_ @ _)]associativity.
  rewrite !catE List.Forall_app; split=> //.
    apply /List.Forall_cons; last by apply /List.Forall_nil.
    rewrite /affine_state_encoding_gens.
    apply /List.Exists_cons; right.
    by apply /List.Exists_cons; left; right.
  rewrite List.Forall_app; split=> //.
  apply /List.Forall_cons; last by apply /List.Forall_nil.
  rewrite /affine_state_encoding_gens.
  apply /List.Exists_cons; right.
  by apply /List.Exists_cons; left; left.
Defined.
*)

(*
Lemma encoding_state_k_value: forall s k,
  subgroup_inj (s:=(affine_state_encoding s)) (encoding_state_k s k) == encoding (s.1 + k*s.2).
Proof.
move=> s k /=.
rewrite -!powermul /encoding.
have ->: (s.2: int) * -k = -(s.2: int) * k by lia.
rewrite 2!associativity.
rewrite -poweradd addrC.
have ->: oppz s.1 = -s.1 by lia.
rewrite -2!associativity.
rewrite -poweradd.
have ->: (- s.1 + - (s.2: int) * k) = oppz (s.1 + k * s.2) by lia.
by rewrite associativity mulrC.
Qed.
*)

(* TODO: move to EquivalenceAlgebra.v *)
Lemma prod_map: forall {M N: monoid} (s: seq M) (f: monoidMorphism M N), prod (map f s) == f (prod s).
Proof.
move=> M N s f; elim: s => /= [|a l eq].
  by rewrite morphism_preserve_e.
by rewrite morphism_preserve_law eq.
Qed.

(* TODO: move to EquivalenceAlgebra.v *)
Lemma prod_inv {G: group} (decomp: seq G) :
  inv (prod decomp) == prod (rev (map inv decomp)).
Proof.
elim: decomp => [/=|a decomp IH /=]; first by rewrite inv_e.
by rewrite inverse_law IH -cat1s rev_cat prod_cat /= neutral_right.
Qed.

(*
Definition normalize_F2_letter (c: F2_sigma): F2_sigma * int := match c with
  | a => (a, 1)
  | a_inv => (a, -1)
  | b => (b, 1)
  | b_inv => (b, -1)
  end.

(*
Definition append_letters_to_count_head (a: F2_sigma) (occ: int) (count_head: F2_sigma * int) :=
  let '(topn, topc) := count_head in
  let '(an, ac) := normalize_F2_letter a in
  if an == topn then (
    let count := topc + ac * occ in
    [::(topn, count)]
  )
  else [:: (an, ac * occ); (topn, topc)].

Definition append_letters_to_count_prefilter (a: F2_sigma) (occ: int) (count: seq (F2_sigma * int)) :=
  match count with
  | nil => let '(an, ac) := normalize_F2_letter a in [::(an, ac * occ)]
  | top::l => (append_letters_to_count_head a occ top) ++ l
  end.

Definition counts_remove_zeroes (count: seq (F2_sigma * int)) :=
  filter (fun '(c, x) => x != 0) count.

Lemma remove_zeroes_cat l l': counts_remove_zeroes (l ++ l') = (counts_remove_zeroes l) ++ (counts_remove_zeroes l').
Proof. by rewrite /counts_remove_zeroes filter_cat. Qed.

Definition append_letters_to_count (a: F2_sigma) (occ: int) (count: seq (F2_sigma * int)) :=
  counts_remove_zeroes (append_letters_to_count_prefilter a occ count).

Fixpoint F2_count_letters (w: F2): seq (F2_sigma * int) := match w with
  | nil => nil
  | c::l => append_letters_to_count c 1 (F2_count_letters l)
  end.
*)

Definition append_letters_to_count (a: F2_sigma) (occ: int) (count: seq (F2_sigma * int)) :=
  match count with
  | nil => if occ == 0 then nil else [::(a, occ)]
  | (c, k)::l =>
      if a == c then (
        if k + occ == 0 then l
        else (a, occ + k)::l
      )
      else (
        if occ == 0 then (c, k)::l
        else (a, occ)::(c, k)::l
      )
  end.

Fixpoint compress_count (l: seq (F2_sigma * int)): seq (F2_sigma * int) := match l with
  | nil => nil
  | (c, k)::l => append_letters_to_count c k (compress_count l)
  end.

Definition F2_count_letters (w: F2): seq (F2_sigma * int) := compress_count (map normalize_F2_letter w).

Definition F2_dec_eq (w w': F2): bool :=
  (F2_count_letters w) == (F2_count_letters w').

Lemma F2_dec_eq_reflect (w w': F2): reflect (w == w') (F2_dec_eq w w').
Admitted.

Definition counts_inv l: seq (F2_sigma * int) := map (fun '(c, n) => (c, -n)) (rev l).

Lemma count_letters_e: F2_count_letters e = nil.
Proof. by rewrite /F2_count_letters. Qed.

Lemma append_letters_same c k k' l:
  append_letters_to_count c k (append_letters_to_count c k' l) = append_letters_to_count c (k + k') l.
Proof.
Admitted.

Lemma append_letters_cancel c k l:
  append_letters_to_count c (-k) (append_letters_to_count c k l) = l.
Proof.
Admitted.

Lemma compress_countK c: compress_count (compress_count c) = compress_count c.
Proof.
elim: c => // [[p k] c] IH.
move: IH => /=.
set l' := compress_count c.
case: l' => [_ |[c' k'] l] /=.
  have /orP [/eqP -> //=|/negbTE /[dup] H -> /=] := orbN (k == 0).
  by rewrite H.
have /orP [/eqP ->|/negbTE /[dup] H -> /=] := orbN (p == c'); last first.
  have /orP [/eqP -> //=|/negbTE /[dup] H' -> /= -> /=] := orbN (k == 0).
  by rewrite H H'.
rewrite eq_refl.  
have /orP [/eqP -> /=|/negbTE /[dup] H -> /=] := orbN (k' + k == 0); last first.
  rewrite -append_letters_same => -> /=.
  by rewrite eq_refl H.
rewrite -{2}(@append_letters_cancel c' k' (compress_count l)) => -> /=.
by rewrite subr_eq0 !eq_refl.
Qed.

Lemma append_letters_compress_cat c k l1 l2:
  append_letters_to_count c k (compress_count (l1 ++ l2)) =
  compress_count (append_letters_to_count c k l1 ++ l2).
Proof.
Admitted.

Lemma compress_count_cat l1 l2:
  compress_count (l1 ++ l2) = compress_count ((compress_count l1) ++ (compress_count l2)).
Proof.
elim: l1 => [/=|[c k] l /= ->].
  by rewrite compress_countK.
exact: append_letters_compress_cat.
Qed.

Lemma count_letters_cons c l:
  F2_count_letters (c :: l) =
  compress_count ((normalize_F2_letter c) :: (F2_count_letters l)).
Proof.
rewrite /F2_count_letters map_cons /=.
by rewrite compress_countK.
Qed.

Lemma count_letters_cat l1 l2:
  F2_count_letters (l1 ++ l2) = compress_count ((F2_count_letters l1) ++ (F2_count_letters l2)).
Proof. by rewrite /F2_count_letters map_cat compress_count_cat. Qed.

Lemma count_letters1 c:
  F2_count_letters [:: c] = [:: normalize_F2_letter c].
Proof. by case: c. Qed.

Lemma rev_compress l:
  rev (compress_count l) =
  compress_count (rev l).
Proof.
Admitted.

Lemma negate_append_letters_comm c k l:
  append_letters_to_count c (- k) [seq (c0, - n0) | '(c0, n0) <- l] =
  [seq (c0, - n0) | '(c0, n0) <- append_letters_to_count c k l].
Proof.
(*
case: l => [/=|[c' k'] l].
  rewrite oppr_eq0.
  by have /orP [/eqP ->|/negbTE ->] := orbN (k == 0).
rewrite map_cons /=.
have /orP [/eqP ->|/negbTE ->] := orbN (c == c'); last done.
have ->: - k' - k = -(k' + k) by lia.
rewrite eq_refl oppr_eq0.
have /orP [-> //|/negbTE -> /=] := orbN (k' + k == 0).
by have <-: - k - k' = -(k + k') by lia.
*)
Admitted.

Lemma append_letters_zero c l:
  append_letters_to_count c 0 l = l.
Proof.
elim: l => // [[c' k] l] /=.
rewrite addr0 add0r.
have /orP [/eqP ->|/negbTE ->] := orbN (c == c').

Admitted.

Lemma compress_negate_counts_comm l:
  compress_count (map (fun '(c, n) => (c, -n)) l) =
  map (fun '(c, n) => (c, -n)) (compress_count l).
Proof.
Admitted.
(*
elim: l => // [[c k]] l.
rewrite map_cons -cat1s.
rewrite compress_count_cat => /=.
rewrite oppr_eq0.
have /orP [/eqP ->|/negbTE -> ->] := orbN (k == 0).
  rewrite eq_refl cat0s compress_countK => ->.
  by rewrite append_letters_zero.
rewrite cat1s /=.
rewrite compress_countK => ->.
exact: negate_append_letters_comm.
Qed.
*)

Lemma counts_inv_compress l:
  counts_inv (compress_count l) =
  compress_count (counts_inv l).
Proof. by rewrite /counts_inv rev_compress compress_negate_counts_comm. Qed.

Lemma counts_inv_cat l1 l2: counts_inv (l1 ++ l2) = (counts_inv l2) ++ (counts_inv l1).
Proof. by rewrite /counts_inv rev_cat map_cat. Qed.

Lemma count_letters_inv (w: F2):
  F2_count_letters (inv w) = counts_inv (F2_count_letters w).
Proof.
rewrite /inv/=/inv_word/=.
elim: w => [|c l].
  by rewrite count_letters_e.
rewrite count_letters_cons -cat1s rev_cat map_cat count_letters_cat => ->.
rewrite count_letters1 -[(normalize_F2_letter c) :: _]cat1s counts_inv_compress.
rewrite counts_inv_cat.
by case: c.
Qed.

Lemma count_letters_preserve_eq (w w': F2):
  w == w' -> F2_count_letters w = F2_count_letters w'.
Proof.
move=> /F2_dec_eq_reflect.
rewrite /F2_dec_eq.
by move=> /eqP.
Qed.

Lemma count_letters_power_a: forall k, F2_count_letters (power (`[a] : F2) k) =
  if k != 0 then [:: (a, k)] else nil.
Proof.
elim => // [k IH|k IH].
- rewrite powerS count_letters_cat {}IH /=.
  have /orP [/eqP -> //|-> /=] := orbN (k == 0).
  by have ->: k%:Z + 1 = k.+1 by lia.
- rewrite (count_letters_preserve_eq (powerP (`[a]: F2) _)) oppr_eq0.
  rewrite count_letters_cons /=.
  rewrite {}IH oppr_eq0 /=.
  have /orP [/eqP -> //|/[dup] H -> /=] := orbN (k == 0).
  have /negbTE -> /=: - Posz k != 0 by lia.
  have ->: -k%:Z - 1 = - (k.+1)%:Z by lia.
  rewrite oppr_eq0 /=.
  by have ->: - 1 - k%:Z = - k.+1%:Z by lia.
Qed.  

Lemma count_letters_power_b: forall k, F2_count_letters (power (`[b] : F2) k) =
  if k != 0 then [:: (b, k)] else nil.
Proof.
elim => // [k IH|k IH].
- rewrite powerS count_letters_cat {}IH /=.
  have /orP [/eqP -> //|-> /=] := orbN (k == 0).
  by have ->: k%:Z + 1 = k.+1 by lia.
- rewrite (count_letters_preserve_eq (powerP (`[b]: F2) _)) oppr_eq0.
  rewrite count_letters_cons /=.
  rewrite {}IH oppr_eq0 /=.
  have /orP [/eqP -> //|/[dup] H -> /=] := orbN (k == 0).
  have /negbTE -> /=: - Posz k != 0 by lia.
  have ->: -k%:Z - 1 = - (k.+1)%:Z by lia.
  by have ->: - 1 - k%:Z = - k.+1%:Z by lia.
Qed.  

Lemma count_letters_encoding z':
  F2_count_letters (encoding z') = (
    if z' == 0
    then [::(a, 1)]
    else [::(b, z'); (a, 1); (b, -z')]
  ).
Proof.
rewrite /encoding !count_letters_cat !count_letters_power_b.
have /orP [/eqP -> //|/[dup] H /negbTE -> /=] := orbN (z' == 0).
rewrite oppr_eq0 H /=.
(*
by have /negbTE ->: oppz z' != 0 by lia.
*)
Admitted.
*)
Definition F2_dec_eq: F2 -> F2 -> bool.
Admitted.

Definition iso_of_transition_gens (t: Transition) (w: F2) :=
       if F2_dec_eq w (encoding t.1.1)       then encoding t.2.1
  else if F2_dec_eq w (inv (encoding t.1.1)) then inv (encoding t.2.1)
  else if F2_dec_eq w (power (`[b]: F2) t.1.2) then power (`[b]: F2) t.2.2
  else if F2_dec_eq w (inv (power (`[b]: F2) t.1.2)) then inv (power (`[b]: F2) t.2.2)
  else w (* whatever but using w allows more general lemma to be stated below *).

(*
Lemma affine_state_encoding_gens_transition (s1 s2: State):
    (affine_state_encoding_gens s2) = map (iso_of_transition_gens (s1, s2)) (affine_state_encoding_gens s1).
Proof.
rewrite /iso_of_transition_gens /=.
have ->: F2_dec_eq (encoding s1.1) (encoding s1.1) = true.
  by rewrite /F2_dec_eq eq_refl.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (encoding s1.1) = false.
  case: s1 => [p q] /=.
  rewrite /F2_dec_eq.
  rewrite count_letters_power_b count_letters_encoding.
  rewrite (nzint_non_nul q).
  have /orP [-> //|/negbTE ->] := orbN (p == 0).
  apply /negbTE.
  by rewrite seq_diff_sizes.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (inv (encoding s1.1)) = false.
  case: s1 => [p q] /=.
  rewrite /F2_dec_eq.
  rewrite count_letters_power_b count_letters_inv count_letters_encoding.
  rewrite (nzint_non_nul q).
  have /orP [-> //|/negbTE -> /=] := orbN (p == 0).
  apply /negbTE.
  by rewrite seq_diff_sizes.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (power (`[b]: F2) s1.2) = true.
  by rewrite /F2_dec_eq eq_refl.
done.
Qed.
*)

Lemma iso_of_transition_gens_preserve_gen t: forall w,
  List.In w (affine_state_encoding_gens t.1) -> List.In (iso_of_transition_gens t w) (affine_state_encoding_gens t.2).
Admitted.

Lemma iso_of_transition_gens_preserve_eq t: forall x y,
  x == y -> iso_of_transition_gens t x == iso_of_transition_gens t y.
Admitted.

Lemma iso_of_transition_gens_preserve_e t:
  iso_of_transition_gens t e == e.
Admitted.

Definition iso_of_transition (t: Transition): morphism (affine_state_encoding t.1) (affine_state_encoding t.2) :=
  (* ugly but using "map_extended (@iso_of_transition_gens_preserve_gen t)" has unresolved implicit arguments *)
  Main_map_extended__canonical__EquivalenceAlgebra_Morphism (iso_of_transition_gens_preserve_gen (t:=t))
  (iso_of_transition_gens_preserve_eq t) (iso_of_transition_gens_preserve_e t).
Arguments iso_of_transition: clear implicits.

Definition iso_of_transition_lm (t: Transition): local_morphism F2 :=
  {| lm_morphism := iso_of_transition t |}.

Let transitions_isos := map iso_of_transition_lm A.

Let F := HNN transitions_isos.
Let ts := HNN_ts transitions_isos.

(* H = <a_m, t_1, ..., t_n> *)
Let H := finGeneratedSubgroup (
  [:: (subgroup_inj (encoding m : HNN_extension_base F2)) ] ++ ts
).

Definition K_defining_property (w: F2) :=
  exists (z': int),
    (w == encoding z')
      /\
    (equivalence_problem A z' m).

Let K := generatedSubgroup K_defining_property.

Lemma inH_if_equiv_m:
    equivalence_problem A z m
      ->
    (encoding z) \insubgroup K.
Proof.
move=> E.
unshelve eexists.
  exists (encoding z).
  apply: igs_gen.
  by exists z; split.
done.
Qed.

(*
Lemma count_letters0: F2_count_letters e = nil.
Proof. done. Qed.
*)

(*
Lemma encoding_non_null z': ~ (encoding z' == e).
Proof.
rewrite /encoding power_inv => /F2_dec_eq_reflect.
rewrite /F2_dec_eq /= !count_letters_cat.
rewrite count_letters_inv count_letters_power_b /=.
have /orP [/[dup] H' -> /=|/[dup] /negbTE H' ->] := orbN (z' == 0).
  by rewrite count_letters0.
(*
by rewrite count_letters1 count_letters0 /= oppr_eq0 H' /=.
*)
Admitted.
Arguments encoding_non_null: clear implicits.

Fixpoint count_a zs: int := match zs with
  | nil => 0
  | (topc, topn)::zs =>
      if topc == a then topn + (count_a zs)
      else if topc == a_inv then - topn + (count_a zs)
      else count_a zs
  end.

Lemma count_a_remove_zeroes l:
  count_a (counts_remove_zeroes l) = count_a l.
Proof.
elim: l => // [[c k] l] IH.
rewrite /counts_remove_zeroes.
have /orP [/eqP -> /=|/= ->] := orbN (k == 0);
by case: c => /=; rewrite ?add0r IH.
Qed.

Lemma count_a_merge l l':
  count_a (merge_counts l l') = (count_a l) + (count_a l').
Proof.
elim: l => [/=|[topc topn] l IH /=].
  by rewrite add0r.
rewrite /append_letters_to_count count_a_remove_zeroes.
move: IH.
set lm := merge_counts l l'.
move=> IH.
case: lm IH => [IH /=|c lm IH /=].
  by case: topc => /=; rewrite -?addrA -IH /=; lia.
case: topc => /=;
rewrite -?addrA -{}IH;
case: c => cc cn /=;
by case: cc => /=; rewrite ?mul1r /mulN1r; lia.
Qed.

Lemma count_a_encodings zs:
  count_a (F2_count_letters (prod (map encoding zs))) = size zs.
Proof.
elim: zs => // z' zs IH /=.
rewrite count_letters_cat count_a_merge IH.
rewrite count_letters_encoding.
have /orP [-> //|/negbTE -> /=] := orbN (z' == 0).
lia.
Qed.

Lemma encoding_free zs:
  prod [seq encoding z | z <- zs] == e -> zs = nil.
Proof.
move=> /F2_dec_eq_reflect; rewrite /F2_dec_eq /= => /eqP H'.
apply: size0nil.
have: (size zs)%:Z = 0; last lia.
by rewrite -count_a_encodings H'.
Qed.

Definition starting_b_of_word (w: F2): int := match F2_count_letters w with
  | (b, k)::_ => k
  | _ => 0
  end.
(*
Fixpoint starting_b_of_word (w: F2): int := match w with
  | b :: l => 1 + starting_b_of_word l
  | b_inv :: l => -1 + starting_b_of_word l
  | _ => 0
  end.
*)
(*
Lemma starting_b_of_a_sandwich w w': starting_b_of_word (w @ (`[a]: F2) @ w') = starting_b_of_word w.
Proof.
elim: w => [|c l]; first by rewrite /law/=.
by case: c => //= ->.
Qed.
*)
Lemma powerS_front k: power (`[b]: F2) k.+1 = (`[b]: F2) ++ power (`[b]: F2) k.
Proof.
elim: k => [/=|k IH].
  by rewrite /law/e/=.
by rewrite powerS {1}IH powerS.
Qed.

Lemma powerP_front k: power (`[b]: F2) (Negz k.+1) = (`[b_inv]: F2) ++ power (`[b]: F2) (Negz k).
Proof.
case: k => [/=|k /=].
  by rewrite /law/e/=.
by rewrite /inv/=/inv_word/= /law/= rev_cat.
Qed.

Lemma append_letters_b_count l:
  match append_letters_to_count b 1 l with
  | (b, k) :: _ => k
  | _ => 0
  end
    =
  match l with
  | (b, k) :: _ => k
  | _ => 0
  end + 1.
Proof.
elim: l => // [[c k] l IH].
case: c.
- rewrite /= mulr1; lia.
- rewrite /= mulr1; lia.
- move: IH.
  elim: l => [/= _|].
    rewrite /append_letters_to_count /=.
    rewrite mulr1.
    have /orP [/eqP -> //=|-> //=] := orbN (k + 1 == 0).


  rewrite /append_letters_to_count /=.
  rewrite mulr1.
  have /orP [/eqP|] := orbN (k + 1 == 0).

  move=> /[dup] ? -> /=.

Admitted.

Lemma append_letters_b_inv_count l:
  match append_letters_to_count b_inv 1 l with
  | (b, k) :: _ => k
  | _ => 0
  end
    =
  match l with
  | (b, k) :: _ => k
  | _ => 0
  end - 1.
Proof.
Admitted.

Lemma starting_b_of_power k: starting_b_of_word (power (`[b]: F2) k) = k.
Proof.
elim: k => // [k|k].
  rewrite powerS_front cat1s /starting_b_of_word.
  rewrite [F2_count_letters (_::_)]/=.
  set l := F2_count_letters (power (`[b]: F2) k).
  rewrite append_letters_b_count /= => ->.
  lia.
case: k => // k.
rewrite powerP_front cat1s /starting_b_of_word.
rewrite [F2_count_letters (_::_)]/=.
set l := F2_count_letters (power (`[b]: F2) (- k.+1%:Z)).
rewrite append_letters_b_inv_count /= => ->.
lia.
Qed.

(*
  by rewrite powerS_front cat1s /= => ->.
case: k => [/=|k]; first by lia.
rewrite powerP_front cat1s /= => ->.
lia.
Qed.
*)

Lemma starting_b_of_encoding_start z' zs' :
  starting_b_of_word ((power (`[b]: F2) z' ++ (`[a]: F2)) ++ zs') = z'.
Proof. by rewrite starting_b_of_a_sandwich starting_b_of_power. Qed.

Lemma starting_b_of_encoding_prod z' zs' :
  starting_b_of_word (encoding z' @ prod [seq encoding i | i <- zs']) = z'.
Proof. by rewrite {1}/encoding /law/= -catA starting_b_of_encoding_start. Qed.

Lemma cancel_encoding_in_prod z1 z2 zs zs':
  (encoding z1) @ prod (map encoding zs) == (encoding z2) @ prod (map encoding zs')
    ->
  z1 = z2 /\ zs = zs'.
Proof.
elim: zs zs'.
  move=> zs' /=.
  rewrite neutral_right.
  elim: zs' z1 z2 => [/= z1 z2|z' zs' IH z1 z2 /=].
    rewrite neutral_right.
    admit.
  simpl.
rewrite {1 3}/encoding -![((_ @ _) @ _) @ _]associativity.

Admitted.

Lemma starting_b_preserves_eq w w':
  w == w' ->
  power (`[b]: F2) w.

Lemma encoding_free_jenrgkjberkjgbkjebkrjgb zs zs':
  prod [seq encoding z | z <- zs] == prod [seq encoding z | z <- zs']
  -> zs = zs'.
Proof.
elim: zs' zs => /= [|z' zs' IH zs].
  exact: encoding_free.
elim: zs zs' IH => /= [zs' _|z'' zs IH zs' IH'].
  by rewrite -prod1s -map_cons => /symm /encoding_free ->.
move=> /[dup] /cancel_encoding_in_prod -> /cancel_left H'.
by have -> := IH' _ H'.
Qed.
*)

Lemma encoding_non_null z': ~ (encoding z' == e).
Admitted.

Lemma encoding_inj x y: encoding x == encoding y -> x = y.
Admitted.

Lemma encoding_free z' x:
  in_generated_subgroup K_defining_property x ->
  encoding z' == x ->
  x = encoding z'.
Admitted.

Lemma equiv_m_if_inH:
    (encoding z) \insubgroup K
      ->
    equivalence_problem A z m.
Proof.
case; case=> [x x_in_K] /= /symm Hx.
have := encoding_free x_in_K Hx.
Admitted.

Definition dummy_transition: Transition.
Proof. by refine (_, _); refine (0, _); exists 1; lia. Qed.

Lemma H'_invariance: forall i: 'I_(size transitions_isos),
    is_subgroup_stable (HNN_nth_iso _ transitions_isos i) K.
Proof.
(* TODO: propriété "<a_p, b^q> inter [ZZ] = [p + qZ]" *)
Admitted.

(* G \subset <a_m, t1, ..., tn> *)
Check HNN_stable_inter_G_is_G _ _ H'_invariance.

Check H: subgroup F.
Check K: subgroup F2.
(*
Check HNN_extension_base F2: subgroup F.
Variable x: H.
Check subgroup_inj (s:=H) x.
Check (subgroup_inj (s:=H) x: F).
Variable x': K.
Check subgroup_inj (s:=K) x'.
Check (subgroup_inj (s:=K) x': F2).
Check subgroup_inj (subgroup_inj (s:=K) x': HNN_extension_base F2).
*)
(*
Lemma inH_if_inK:
  forall (x: H), (subgroup_inj (s:=H) x) \insubgroup K.

Lemma inK_if_inH:
  forall (x: K), (subgroup_inj x) \insubgroup H.
Admitted.
*)

Check identity_morphism.

Definition identity_lm_H: local_morphism H :=
  {| lm_morphism := identity_morphism H |}.

Let E := HNN [:: identity_lm_H].
Let t := tnth (HNN_ts [:: identity_lm_H]) 0.

Fail Check HNN_extension_base F: subgroup E.
Check HNN_extension_base H: subgroup E.

Variable x: H.
Check subgroup_inj (s:=H) x.
Check (subgroup_inj (s:=H) x : HNN_extension_base F).
Check (t: E).

Check subgroup_inj (s:=F) (subgroup_inj (s:=H) x : HNN_extension_base F).

Goal True.
have := iso_representation H [:: identity_lm_H] 0.
rewrite -/t.
rewrite /HNN_nth_iso/=.
rewrite /identity_morphism.
Abort.

Variable x: H.
Check subgroup_inj (s:=H) x.
Check (subgroup_inj (s:=H) x : HNN_extension_base F).
Check subgroup_inj (s:=F) (subgroup_inj (s:=H) x : HNN_extension_base F).

Check (HNN_extension_base F: subgroup F).
Check (subgroup_inj (s:=H) x : HNN_extension_base F).

Lemma H_when_equiv: forall (x: H),
  (subgroup_inj (s:=H) x) == (t @ subgroup_inj (s:=H) x) @ inv t.

(* H = <a_m, t_1, ..., t_n> *)
Let H := finGeneratedSubgroup (
  [:: (subgroup_inj (encoding m : HNN_extension_base F2)) ] ++ ts
).


Definition reduction_output : GWPArguments := {|
  P := admit A;
  u := admit z;
  v := admit m;
|}.

End Reduction.

Lemma novikov_bool_reduction : equivalence_problem_uncurried ⪯ GWP_uncurried.
Proof.
exists (fun '(A, z, m) => reduction_output A z m).
move=> [] [A z] m.
rewrite /equivalence_problem_uncurried /GWP_uncurried; split.
- move=> /inH_if_equiv_m.

Admitted.

Theorem novikov_boone : undecidable GWP_uncurried.
Proof.
apply: (undecidability_from_reducibility equivalence_problem_undecidable).
exact: novikov_bool_reduction.
Qed.
