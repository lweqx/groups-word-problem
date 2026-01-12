From HB Require Import structures.
From Undecidability Require Import Synthetic.Definitions Synthetic.Undecidability.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra tuple.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.

From GWP Require Import Presentation AffineMachines F2 EquivalenceAlgebra Equivalence HNN.

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
Definition affine_state_encoding (s: State) := generatedSubgroup (affine_state_encoding_gens s).

Lemma catE {T: Type} (x y: seq T): x ++ y = (x ++ y)%list.
Proof. by elim: x => [//|a l /= ->]. Qed.

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

Lemma encoding_state_k_value: forall s k,
  subgroup_inj (s:=(affine_state_encoding s)) (encoding_state_k s k) == encoding (s.1 + k*s.2).
Proof.
move=> s k /=.
rewrite -!powermul /encoding.
have ->: s.2 * -k = -s.2 * k by lia.
rewrite 2!associativity.
rewrite -poweradd addrC.
have ->: oppz s.1 = -s.1 by lia.
rewrite -2!associativity.
rewrite -poweradd.
have ->: (- s.1 + - s.2 * k) = oppz (s.1 + k * s.2) by lia.
by rewrite associativity mulrC.
Qed.

(* TODO: move to EquivalenceAlgebra.v *)
Lemma prod_map: forall {M N: monoid} (s: seq M) (f: monoidMorphism M N), prod (map f s) == f (prod s).
Proof.
move=> M N s f; elim: s => /= [|a l eq].
  by rewrite morphism_preserve_e.
by rewrite morphism_preserve_law eq.
Qed.

(*
Section MorphismFromGeneratorMap.
Variable G H: group.
Variable genG: seq G.
Variable f: morphism G H.

Let K := generatedSubgroup genG.
Let L := generatedSubgroup [seq f g | g <- genG].

Definition canonical_generated_morphism: K -> L.
Proof.
move=> x.
case: (sb_point_characterization x) => decomp [decomp_of_gens ?].
exists (prod [seq f el | el <- decomp]).
exists [seq f el | el <- decomp]; split=> //.
apply /List.Forall_map.
move: decomp_of_gens; apply /List.Forall_impl => el.
rewrite List.Exists_map; apply /List.Exists_impl => gen [] eq.
  left; exact /morphism_preserve_equiv.
right; rewrite morphism_preserve_inv; exact /morphism_preserve_equiv.
Defined.

Lemma cgm_preserve_equiv: forall x y, x == y -> canonical_generated_morphism x == canonical_generated_morphism y.
Proof.
move=> x y.
rewrite /canonical_generated_morphism.
elim: (sb_point_characterization x) => decomp_x [decomp_x_of_gens decomp_for_x].
elim: (sb_point_characterization y) => decomp_y [decomp_y_of_gens decomp_for_y].
rewrite /eq/=/subgroupby_eq/= => /injectivity_property.
rewrite !prod_map -{}decomp_for_y -{}decomp_for_x.
by rewrite {1}/eq/=/subgroupby_eq/=/subgroupby_inj/= => ->.
Qed.

Lemma cgm_preserve_e: canonical_generated_morphism e == e.
Proof.
rewrite /canonical_generated_morphism.
elim: (sb_point_characterization e) => decomp [decomp_of_gens decomp_for_e].
rewrite /eq/=/subgroupby_eq/=.
rewrite prod_map -(morphism_preserve_e (s:=f)).
by apply: morphism_preserve_equiv; rewrite -decomp_for_e.
Qed.

Lemma cgm_preserve_law: forall x y, canonical_generated_morphism (x @ y) == (canonical_generated_morphism x) @ (canonical_generated_morphism y).
Proof.
move=> x y.
rewrite /canonical_generated_morphism.
elim: (sb_point_characterization x) => decomp_x [decomp_x_of_gens decomp_for_x].
elim: (sb_point_characterization y) => decomp_y [decomp_y_of_gens decomp_for_y].
rewrite /eq/=/subgroupby_eq/=.
elim: (P_law (sb_point x) (sb_point y) (sb_point_characterization x) (sb_point_characterization y)) => decomp_xy [decomp_xy_of_gens decomp_for_xy] /=.
by rewrite !prod_map -decomp_for_xy -decomp_for_x -decomp_for_y morphism_preserve_law.
Qed.

HB.instance Definition _ := isMonoidMorphism.Build K L canonical_generated_morphism cgm_preserve_equiv cgm_preserve_e cgm_preserve_law.

Lemma cgm_preserve_inv: forall x, inv (canonical_generated_morphism x) == canonical_generated_morphism (inv x).
Proof.
move=> x.
rewrite /canonical_generated_morphism.
elim: (sb_point_characterization x) => decomp_x [decomp_x_of_gens decomp_for_x].
rewrite /eq/=/subgroupby_eq/=.
elim: (P_inv (sb_point x) (sb_point_characterization x)) => decomp_y [decomp_y_of_gens decomp_for_y] /=.
by rewrite !prod_map -decomp_for_y -decomp_for_x morphism_preserve_inv.
Qed.

HB.instance Definition _ := isInvMorphism.Build K L canonical_generated_morphism cgm_preserve_inv.

End MorphismFromGeneratorMap.
Arguments canonical_generated_morphism {_ _}.
*)

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
case: l => [/=|[c' k'] l].
  rewrite oppr_eq0.
  by have /orP [/eqP ->|/negbTE ->] := orbN (k == 0).
rewrite map_cons /=.
have /orP [/eqP ->|/negbTE ->] := orbN (c == c'); last done.
have ->: - k' - k = -(k' + k) by lia.
rewrite eq_refl oppr_eq0.
have /orP [-> //|/negbTE -> /=] := orbN (k' + k == 0).
by have <-: - k - k' = -(k + k') by lia.
Qed.

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
by have /negbTE ->: oppz z' != 0 by lia.
Qed.

Lemma seq_diff_sizes {T: eqType} (l l': seq T):
  size l != size l' -> l != l'.
Proof. by apply /contra => /eqP ->. Qed.

Definition iso_of_transition_gens (t: Transition) (w: F2) :=
       if F2_dec_eq w (encoding t.1.1)       then encoding t.2.1
  else if F2_dec_eq w (inv (encoding t.1.1)) then inv (encoding t.2.1)
  else if F2_dec_eq w (power (`[b]: F2) t.1.2) then power (`[b]: F2) t.2.2
  else if F2_dec_eq w (inv (power (`[b]: F2) t.1.2)) then inv (power (`[b]: F2) t.2.2)
  else w (* whatever but using w allows more general lemma to be stated below *).

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
  (* TODO: we don't define transitions's second component to be non-null *)
  have ->: q != 0 by admit.
  have /orP [-> //|/negbTE ->] := orbN (p == 0).
  apply /negbTE.
  by rewrite seq_diff_sizes.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (inv (encoding s1.1)) = false.
  case: s1 => [p q] /=.
  rewrite /F2_dec_eq.
  rewrite count_letters_power_b count_letters_inv count_letters_encoding.
  (* TODO: we don't define transitions's second component to be non-null *)
  have ->: q != 0 by admit.
  have /orP [-> //|/negbTE -> /=] := orbN (p == 0).
  apply /negbTE.
  by rewrite seq_diff_sizes.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (power (`[b]: F2) s1.2) = true.
  by rewrite /F2_dec_eq eq_refl.
done.
Admitted.

Lemma iso_of_transition_gens_preserve_eq (t: Transition): forall w w',
  w == w' -> iso_of_transition_gens t w == iso_of_transition_gens t w'.
Proof.
Admitted.

Lemma iso_of_transition_gens_involutive (s1 s2: State): forall w,
  iso_of_transition_gens (s1, s2) (iso_of_transition_gens (s2, s1) w) == w.
Proof.
Admitted.

Lemma iso_of_transition_gens_preserve_inv (s1 s2: State): forall w,
  inv (iso_of_transition_gens (s1, s2) w) == iso_of_transition_gens (s1, s2) (inv w).
Proof.
Admitted.

Definition iso_of_transition (t: Transition): (affine_state_encoding t.1) -> (affine_state_encoding t.2).
Proof.
move=> [x [decomp [decomp_of x_decomp]]].
exists (prod [seq
  iso_of_transition_gens t el
  | el <- decomp
]).
exists [seq
  iso_of_transition_gens t el
  | el <- decomp
]; split=> //.
rewrite List.Forall_map.
move: decomp_of; apply List.Forall_impl => a.
case: t => [s1 s2] /=.
rewrite (affine_state_encoding_gens_transition s2 s1).
have -> := List.Exists_map (iso_of_transition_gens (s2, s1)) _ (affine_state_encoding_gens s2).
apply /List.Exists_impl => gens; case => H.
  left.
  rewrite -[gens]iso_of_transition_gens_involutive.
  exact /iso_of_transition_gens_preserve_eq.
right.
move: H.
rewrite iso_of_transition_gens_preserve_inv.
move=> /(iso_of_transition_gens_preserve_eq (s1, s2)).
by rewrite iso_of_transition_gens_involutive.
Defined.
Arguments iso_of_transition: clear implicits.

(* TODO: move to EquivalenceAlgebra.v *)
Lemma prod_inv {G: group} (decomp: seq G) :
  inv (prod decomp) == prod (rev (map inv decomp)).
Proof.
elim: decomp => [/=|a decomp IH /=]; first by rewrite inv_e.
by rewrite inverse_law IH -cat1s rev_cat prod_cat /= neutral_right.
Qed.

Lemma encoding_as_affine_state_encoding p q: affine_state_encoding (p, q).
Proof.
exists (encoding p).
exists [::(encoding p)]; split.
  apply /List.Forall_cons => //.
  by apply /List.Exists_cons; left; left.
by rewrite prod1s prod0 neutral_right.
Defined.

Lemma power_as_affine_state_encoding p q: affine_state_encoding (p, q).
Proof.
exists (power (`[b]: F2) q).
exists [::(power (`[b]: F2) q)]; split.
  apply /List.Forall_cons => //.
  by apply /List.Exists_cons; right; left; left.
by rewrite prod1s prod0 neutral_right.
Defined.

Section IsoOfTransMorphism.
Variable t: Transition.

Lemma counts_inv_involutive l:
  counts_inv (counts_inv l) = l.
Proof.
rewrite /counts_inv !map_rev revK.
elim: l => [//|[? ?] l /= ->].
by rewrite opprK.
Qed.

Lemma iot_preserve_e: iso_of_transition t e == e.
Proof. by rewrite /iso_of_transition/=/eq/=/subgroupby_eq/=. Qed.

Lemma F2_dec_eq_transitivity' w w' w'':
  ~~ F2_dec_eq w' w'' ->
     F2_dec_eq w  w'  ->
  ~~ F2_dec_eq w  w''.
Proof. by rewrite /F2_dec_eq; move=> ? /eqP ->. Qed.

Lemma F2_dec_eq_sym x y: F2_dec_eq x y = F2_dec_eq y x.
Proof. by rewrite /F2_dec_eq eq_sym. Qed.

Lemma eqb_iff (b1 b2: bool): b1 <-> b2 -> b1 = b2.
Proof.
case: b1; case: b2 => //=; case=> Hl Hr.
  by have := Hl isT.
by have := Hr isT.
Qed.

Lemma F2_dec_eq_inv x y: F2_dec_eq x (inv y) = F2_dec_eq (inv x) y.
Proof.
rewrite /F2_dec_eq eq_sym !count_letters_inv.
apply /eqb_iff; split=> [/eqP|/eqP <-].
  by rewrite -{2}[F2_count_letters y]counts_inv_involutive => ->.
by rewrite counts_inv_involutive.
Qed.

Lemma inv_encoding_neq: ~~ F2_dec_eq (inv (encoding t.1.1)) (encoding t.1.1).
Proof.
rewrite /encoding.
have:
  inv ((power (`[b]: F2) t.1.1 @ (`[a]: F2)) @ power (`[b]: F2) (oppz t.1.1))
    ==
  (power (`[b]: F2)) t.1.1 @ (`[a_inv]: F2) @ (power (`[b]: F2) (-t.1.1)).
  by rewrite !inverse_law !power_inv !inv_involutive associativity.
move=> /F2_dec_eq_reflect.
rewrite /F2_dec_eq => /eqP ->.
rewrite !count_letters_cat !count_letters_power_b.
rewrite oppr_eq0.
have /orP [/eqP -> //|/[dup] H -> /=] := orbN (t.1.1 == 0).
Admitted.

Lemma iotg_inv x:
  iso_of_transition_gens t (inv x) == inv (iso_of_transition_gens t x).
Proof.
rewrite /iso_of_transition_gens.
have /orP [/[dup] H ->|/[dup] H /negbTE ->] := orbN (F2_dec_eq x (encoding t.1.1)).
  rewrite -F2_dec_eq_inv.
  have := @F2_dec_eq_transitivity' x (encoding t.1.1) (inv (encoding t.1.1)) _ H.
  rewrite F2_dec_eq_inv => /(_ inv_encoding_neq) /negbTE ->.
  rewrite F2_dec_eq_inv.
  have /F2_dec_eq_reflect := inv_involutive x.
  rewrite /F2_dec_eq => /eqP ->.
  move: H => /eqP ->.
  by rewrite eq_refl.
have /orP [|/[dup] H' /negbTE ->] := orbN (F2_dec_eq x (inv (encoding t.1.1))).
  rewrite F2_dec_eq_inv => ->.
  by rewrite inv_involutive.
rewrite -F2_dec_eq_inv.
move: (H') => /negbTE ->.
rewrite -F2_dec_eq_inv.
have /F2_dec_eq_reflect Hinv := inv_involutive (encoding t.1.1).
have {Hinv} /negbTE ->: ~~ F2_dec_eq x (inv (inv (encoding t.1.1))).
  move: Hinv H.
  by rewrite /F2_dec_eq => /eqP ->.
have /orP [|] := orbN (F2_dec_eq (inv x) (power (`[b]: F2) t.1.2)).
  move=> /[dup] H'' ->.
  admit.
Admitted.

Lemma prod_iotg_e (x: affine_state_encoding t.1) (decomp_x: seq F2):
  x == e
    ->
  sb_point x == prod decomp_x
    ->
  ListDef.Forall
    (fun el : presented F2_sigma =>
      List.Exists (fun gen : presented F2_sigma => gen == el \/ inv gen == el)
        (affine_state_encoding_gens t.1))
    decomp_x
    ->
  prod [seq iso_of_transition_gens t el | el <- decomp_x] == e.
Proof.
Admitted.

Lemma iot_preserve_equiv: forall (x y: affine_state_encoding t.1),
  x == y -> iso_of_transition t x == iso_of_transition t y.
Proof.
move=> x y H.
rewrite /iso_of_transition.
elim: (sb_point_characterization x) => decomp_x [decomp_x_gens decomp_x_eq].
elim: (sb_point_characterization y) => decomp_y [decomp_y_gens decomp_y_eq].
rewrite /eq/=/subgroupby_eq/=/subgroupby_inj/=.
elim: decomp_y x y decomp_x decomp_x_gens decomp_y_gens decomp_x_eq decomp_y_eq H.
  move=> x y decomp_x /= decomp_x_gens _ decomp_x_eq decomp_y_eq H.
  have {decomp_y_eq} {}H: x == e by move: H; rewrite /eq/=/subgroupby_eq/=/subgroupby_inj decomp_y_eq.
  apply /prod_iotg_e; first exact: H; done.
move=> c decomp_y IH y x decomp_x decomp_x_gens decomp_y_gens decomp_x_eq decomp_y_eq H.
rewrite map_cons prod1s.
have <-:
  inv (iso_of_transition_gens t c) @ prod [seq iso_of_transition_gens t el | el <- decomp_x] ==
  prod [seq iso_of_transition_gens t el | el <- decomp_y];
last by rewrite associativity inverse_left neutral_left.
rewrite -iotg_inv -prod1s -map_cons.

have [c' c'_is_c]: exists c': affine_state_encoding t.1, ((subgroup_inj (s:=affine_state_encoding t.1) (G:=F2) c') : F2) == c.
  have /= := List.Forall_inv decomp_y_gens.
  rewrite {1}/affine_state_encoding_gens.
  move=> /List.Exists_cons [|/List.Exists_cons [|/List.Exists_nil //]]; case=> ?.
  - by exists (encoding_as_affine_state_encoding t.1.1 t.1.2).
  - by exists (inv (encoding_as_affine_state_encoding t.1.1 t.1.2)).
  - by exists (power_as_affine_state_encoding t.1.1 t.1.2).
  - by exists (inv (power_as_affine_state_encoding t.1.1 t.1.2)).

have := IH ((inv c') @ y) ((inv c') @ x) ((inv c)::decomp_x).
rewrite /F2_dec_eq => {}IH.
rewrite -(IH _ _ _ _ _) {IH}.
- reflexivity.
- apply /List.Forall_cons => //.
  have /= := List.Forall_inv decomp_y_gens.
  apply /List.Exists_impl => a; case => [->|]; first by right.
  by rewrite -{2}[a]inv_involutive => ->; left.
- exact: (List.Forall_inv_tail decomp_y_gens).
- by rewrite /= -c'_is_c morphism_preserve_inv decomp_x_eq.
- rewrite /= decomp_y_eq prod1s -c'_is_c associativity.
  by rewrite inverse_right neutral_left.
- by rewrite H.
Qed.

Lemma iot_preserve_law: forall (x y: affine_state_encoding t.1),
  iso_of_transition t (x @ y) == (iso_of_transition t x) @ (iso_of_transition t y).
Proof.
move=> x y.
rewrite /iso_of_transition/=/P_law/=/igs_P_law/=.
elim: (sb_point_characterization x) => decomp_x [decomp_x_gens decomp_x_e].
elim: (sb_point_characterization y) => decomp_y [decomp_y_gens decomp_y_e].
by rewrite /eq/=/subgroupby_eq/= map_cat prod_cat.
Qed.

HB.instance Definition _ := isMonoidMorphism.Build (affine_state_encoding t.1) (affine_state_encoding t.2) (iso_of_transition t) iot_preserve_equiv iot_preserve_e iot_preserve_law.

Lemma iot_preserve_inv: forall (x: affine_state_encoding t.1),
  inv (iso_of_transition t x) == iso_of_transition t (inv x).
Proof.
move=> x.
rewrite /iso_of_transition/=/P_inv/=.
case: x => x [decomp_x [decomp_x_gens decomp_x_eq]].
rewrite /eq/=/subgroupby_eq/=/subgroupby_inj/=.
rewrite prod_inv map_rev.
clear decomp_x_eq decomp_x_gens.
elim: decomp_x => // c decomp_x.
by rewrite -cat1s !map_cat !rev_cat !prod_cat /= iotg_inv => ->.
Qed.

HB.instance Definition _ := isInvMorphism.Build (affine_state_encoding t.1) (affine_state_encoding t.2) (iso_of_transition t) iot_preserve_inv.

End IsoOfTransMorphism.

Definition iso_of_transition_lm (t: Transition): local_morphism F2 :=
  {| lm_morphism := (iso_of_transition t: morphism (affine_state_encoding t.1) (affine_state_encoding t.2)) |}.

Let transitions_isos := map iso_of_transition_lm A.

Let F := HNN transitions_isos.
Let ts := HNN_ts transitions_isos.

(* H = <a_m, t_1, ..., t_n> *)
Let H := generatedSubgroup (
  [:: (subgroup_inj (encoding m : HNN_extension_base F2)) ] ++ ts
).

Definition K_defining_property (w: F2) :=
  exists (z': int),
    (w == encoding z')
      /\
    (equivalence_problem A z' m).

Lemma Kdp_preserves_eq: forall w w', w == w' -> K_defining_property w -> K_defining_property w'.
Proof.
move=> w w' eq; case=> [z' [? ?]].
exists z'; split=> //.
by rewrite -eq.
Qed.

Let K := generatedSubgroupByProp K_defining_property Kdp_preserves_eq.

Lemma inH_if_equiv_m:
    equivalence_problem A z m
      ->
    (encoding z) \insubgroup K.
Proof.
move=> E.
unshelve eexists.
  exists (encoding z).
  exists [::(encoding z)]; split; last by rewrite prod1s prod0 neutral_right.
  apply /List.Forall_cons; last by apply /List.Forall_nil.
  by left; exists z.
done.
Qed.

Lemma count_letters0: F2_count_letters e = nil.
Proof. done. Qed.

Lemma encoding_non_null z': ~ (encoding z' == e).
Proof.
rewrite /encoding power_inv => /F2_dec_eq_reflect.
rewrite /F2_dec_eq /= !count_letters_cat.
rewrite count_letters_inv count_letters_power_b /=.
have /orP [/[dup] H' -> /=|/[dup] /negbTE H' ->] := orbN (z' == 0).
  by rewrite count_letters0.
by rewrite count_letters1 count_letters0 /= oppr_eq0 H' /=.
Qed.
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

Lemma equiv_m_if_inH:
    (encoding z) \insubgroup K
      ->
    equivalence_problem A z m.
Proof.
case=> x.
rewrite /subgroup_inj/=/subgroupby_inj/=.
case: (sb_point_characterization x) => decomp_x [/[swap] ->].
rewrite /K_defining_property => H'.
(*
elim: decomp_x.
  move=> /= _.
  rewrite /encoding.
  rewrite power_inv -(inverse_left (power (`[b]: F2) z)) => R.
  have := cancel_right _ _ _ R.
  rewrite -{1}[power (`[b]: F2) z]neutral_right => {}R.
  have := cancel_left _ _ _ R.
  by move=> /F2_dec_eq_reflect.
move=> c l.
*)
Admitted.

Lemma H'_invariance: forall i: 'I_(size transitions_isos),
    is_subgroup_stable (HNN_nth_iso _ transitions_isos i) K.
Proof.
move=> i; rewrite /HNN_nth_iso /transitions_isos (nth_map 0) => [x [x' x_is_x']|]; last first.
  move: i; rewrite /transitions_isos size_map; exact: ltn_ord.


(* TODO: propriété "<a_p, b^q> inter [ZZ] = [p + qZ]" *)
Admitted.

(* G \subset <a_m, t1, ..., tn> *)
Check HNN_stable_inter_G_is_G _ _ H'_invariance.

Check H: subgroup F.
Check K: subgroup F2.

Check HNN_extension_base F2: subgroup F.
Variable x: H.
Check subgroup_inj (s:=H) x.
Check (subgroup_inj (s:=H) x: F).
Variable x': K.
Check subgroup_inj (s:=K) x'.
Check (subgroup_inj (s:=K) x': F2).
Check subgroup_inj (subgroup_inj (s:=K) x': HNN_extension_base F2).

Lemma inH_if_inK:
  forall (x: H), (subgroup_inj x) \insubgroup K.

Lemma inK_if_inH:
  forall (x: K), (subgroup_inj x) \insubgroup H.

Admitted.

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
