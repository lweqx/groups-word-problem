From HB Require Import structures.
From Undecidability Require Import Synthetic.Definitions Synthetic.Undecidability.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra tuple.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.

From GWP Require Import Presentation AffineMachines F2 EquivalenceAlgebra Equivalence HNN.

(* A way to view a subgroup of a subgroup of a group as a subgroup of the super-group.
   ie. if:
     G: group
     H: subgroup G
     K: subgroup H
   then:
     transitiveSubgroup H K: subgroup G
  *)
(*
Section TransitiveSubgroup.
Variable G: group.
Variable H: subgroup G.
Variable K: subgroup H.

Definition transitiveSubgroup := K.

Definition ts_injection (x: transitiveSubgroup): G := subgroup_inj (subgroup_inj x).

Lemma tsi_injectivity_property x y: ts_injection x == ts_injection y -> x == y.
Proof.
move=> P.
do 2 ! apply: injectivity_property.
exact: P.
Qed.
HB.instance Definition _ := isInjective.Build _ _ ts_injection tsi_injectivity_property.

Lemma tsi_preserve_equiv x y: x == y -> ts_injection x == ts_injection y.
Proof. by move=> P; do 2 ! apply: morphism_preserve_equiv. Qed.

Lemma tsi_preserve_e: ts_injection e == e.
Proof. by rewrite /ts_injection; do 2 ! rewrite morphism_preserve_e. Qed.

Lemma tsi_preserve_law x y: ts_injection (x @ y) == (ts_injection x) @ (ts_injection y).
Proof. by rewrite /ts_injection; do 2 ! rewrite morphism_preserve_law. Qed.

HB.instance Definition _ := isMonoidMorphism.Build transitiveSubgroup G ts_injection tsi_preserve_equiv tsi_preserve_e tsi_preserve_law.

Lemma tsi_preserve_inv x: inv (ts_injection x) == ts_injection (inv x).
Proof. by rewrite /ts_injection; do 2 ! rewrite morphism_preserve_inv. Qed.

HB.instance Definition _ := isInvMorphism.Build transitiveSubgroup G ts_injection tsi_preserve_inv.

(* non-forgetful inheritance :< *)
Fail HB.instance Definition _ := isSubgroup.Build G transitiveSubgroup ts_injection.

End TransitiveSubgroup.
*)

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

Definition F2_dec_eq (w w': F2): bool :=
  (F2_count_letters w) == (F2_count_letters w').

Lemma F2_dec_eq_reflect (w w': F2): reflect (w == w') (F2_dec_eq w w').
Admitted.

Fixpoint merge_counts l l' := match l with
  | nil => l'
  | (an, ac)::l => append_letters_to_count an ac (merge_counts l l')
  end.

Lemma append_letters_inv c k l:
  append_letters_to_count c k l = append_letters_to_count (F2_invl c) (-k) l.
Proof. rewrite /append_letters_to_count; by elim: l => [/=|[topc topn] l /=]; case: c => /=; rewrite ?mulrNN ?mul1r ?mulN1r. Qed.

Lemma merge_counts_cat' l1 l2 l3:
  merge_counts (l1 ++ l2) l3 = merge_counts l1 (merge_counts l2 l3).
Proof. by elim: l1 l2 l3 => // c l1 IH /= l2 l3; rewrite IH. Qed.

Lemma merge_counts_cons topc topn l2 l3:
  merge_counts ((topc, topn)::l2) l3 = append_letters_to_count topc topn (merge_counts l2 l3).
Proof. done. Qed.

Lemma append_letters_cons top c k l':
  append_letters_to_count c k (top::l') = (append_letters_to_count c k [::top]) ++ (counts_remove_zeroes l').
Proof. by rewrite /append_letters_to_count /= cats0 remove_zeroes_cat. Qed.

Lemma append_letters_cat c k l l':
  (counts_remove_zeroes l) != nil ->
  append_letters_to_count c k (l ++ l') = (append_letters_to_count c k l) ++ (counts_remove_zeroes l').
Proof. 
elim: l => // [a l] IH _.
rewrite cat_cons [append_letters_to_count c k (a::(l ++ l'))]append_letters_cons.
rewrite [append_letters_to_count c k (a::l)]append_letters_cons.
by rewrite remove_zeroes_cat catA.
Qed.

Lemma append_letters_0 c k:
  append_letters_to_count c k nil = if k != 0
    then let '(topc, topn) := normalize_F2_letter c in [:: (topc, topn * k)]
    else [::].
Proof.
rewrite /append_letters_to_count/=.
by case: c => /=; rewrite ?mul1r ?mulN1r ?addr0 ?oppr_eq0.
Qed.

Lemma counts_remove_zeroes_projective l:
  counts_remove_zeroes (counts_remove_zeroes l) = counts_remove_zeroes l.
Proof. by rewrite /counts_remove_zeroes filter_id. Qed.

Lemma append_letters_1s c k topc topn l:
  append_letters_to_count c k ((topc, topn) :: l) = counts_remove_zeroes ((c, k)::(append_letters_to_count topc topn l)).
Proof.
rewrite /append_letters_to_count /append_letters_to_count_prefilter.


rewrite remove_zeroes_cat.

Lemma append_same_cancel c k l:
  append_letters_to_count c k (append_letters_to_count c (-k) l)
    =
  counts_remove_zeroes l.
Proof.
elim: l => [|[topc topn] l].
  rewrite append_letters_0 /=.
  case: c => /=;
  rewrite ?mul1r ?mulrN ?mulN1r ?opprK oppr_eq0;
  by have /orP [->|/negPn /[dup] H -> /=] := orbN (k != 0); do [
    rewrite /append_letters_to_count/append_letters_to_count_prefilter /=;
    rewrite ?mul1r ?mulN1r ?[-k + k]addrC;
    (* this has to be an already existing lemma *)
    have ->: k - k = 0 by lia;
    by rewrite eq_refl /=
    |
    by rewrite append_letters_0 /= ?mul1r ?mulN1r H
  ].
move=> IH /=.


rewrite /append_letters_to_count /append_letters_to_count_prefilter /=.
case: c => /=; case: topc => /=.
rewrite !mul1r.
have /orP [/[dup] H ->|/negPn /[dup] H ->] := orbN (topn - k != 0).
+ have /orP [/[dup] H' ->|/negPn /[dup] H' -> /=] := orbN (topn != 0).
  - rewrite remove_zeroes_cat.
    rewrite /append_letters_to_count_head /=.
    rewrite mul1r subrK H' cat1s.
    by rewrite counts_remove_zeroes_projective.
  - by rewrite mul1r subrK H' /= counts_remove_zeroes_projective.
+ have /= ->: topn = k by lia.
  admit.

have /orP [/[dup] H ->|/negPn /[dup] H ->] := orbN (topn - k != 0).
+ have /orP [/[dup] H' ->|/negPn /[dup] H' -> /=] := orbN (topn != 0).
  - rewrite remove_zeroes_cat.
    rewrite /append_letters_to_count_head /=.
    rewrite mul1r subrK H' cat1s.
    by rewrite counts_remove_zeroes_projective.
  - by rewrite mul1r subrK H' /= counts_remove_zeroes_projective.
+ have /= ->: topn = k by lia.
  admit.

  set l' := counts_remove_zeroes l.
  elim: l' a => // a' l' IH a.
  rewrite remove_zeroes_cat.
  transitivity ((if k != 0 then [:: (a, k)] else [::]) ++ []).

, a' & l'] else a' :: l').

  elim: (counts_remove_zeroes l) => [|c l'].
    admit.





simpl.
rewrite {2}/append_letters_to_count/append_letters_to_count_prefilter /=.
case: c => /=; case: topc => /=.
rewrite !mul1r.


have /orP [-> /=|/negPn /[dup] ? ->] := orbN (topn - k != 0).
  by rewrite !mul1r subrK counts_remove_zeroes_projective.
have ->: topn = k by lia.
simpl.

by rewrite !mul1r subrK counts_remove_zeroes_projective.

?[-k + k]addrC.
(* this has to be an already existing lemma *)
have ->: k - k = 0 by lia;

Admitted.

Lemma append_letters_0 c l: append_letters_to_count c 0 l = counts_remove_zeroes l.
Proof.
elim: l => [|[topn topc] l /=].
  rewrite /append_letters_to_count /=.
  by case: c.
have /orP [/[dup] H ->|/[dup] H ->] := orbN (topc == 0)%B;
rewrite /append_letters_to_count /= remove_zeroes_cat;
by case: c => /=; case: topn => /=; rewrite ?mul1r ?addr0 H /=.
Qed.

Lemma append_same_add c k k' l:
    k + k' != 0 ->
   append_letters_to_count c k (append_letters_to_count c k' l) = append_letters_to_count c (k + k') l.
Proof.
case: l => [|[topc topn] l].
  admit.
(*
  case: c => /=.
  by rewrite 3!mul1r addrC=> /negbTE ->.
  rewrite 3!mulN1r addrC => ?; have /negbTE ->: (- k' - k != 0) by lia.
  by rewrite cats0 opprD.
  by rewrite 3!mul1r addrC=> /negbTE ->.
  rewrite 3!mulN1r addrC => ?; have /negbTE ->: (- k' - k != 0) by lia.
  by rewrite cats0 opprD.
rewrite append_letters_cons -[(topc, topn)::l]cat1s.
rewrite [append_letters_to_count _ (k + k') _]append_letters_cons.
simpl.
case: c => /=.
rewrite !cats0.
case: topc => /=.
rewrite !mul1r.
have /orP [/[dup] ? ->|] := orbN (topn + k' == 0)%B.
rewrite cat0s.
have /orP [/[dup] ? ->|] := orbN (topn + (k + k') == 0)%B.
rewrite cat0s.
have ->: k = 0 by lia.
move=> _.




*)

Admitted.

Lemma merge_counts_remove_append: forall l l' c k,
  merge_counts (append_letters_to_count c k l) l' = merge_counts ((c, k)::l) l'.
Proof.
elim => [l' c k /=|top l IH l' c' k'].
  admit.
(*  by case: c => /=; rewrite ?mul1r // mulN1r append_letters_inv /= opprK. *)
rewrite [merge_counts [:: _, _ & _] _]/=.
case: top => c k.
rewrite append_letters_cons merge_counts_cat'.
case: c'; case: c.
- rewrite /= mul1r cats0.
  have /orP [/[dup] ? ->|/[dup] ? /negbTE ->] := orbN (k + k' == 0).
  + have ->: k = -k' by lia.
    by rewrite append_same_cancel.
  + by rewrite append_same_add /= addrC.
- by rewrite /= mul1r.
- by rewrite /= mul1r.
- by rewrite /= mul1r.
- rewrite /= mulN1r cats0.
  rewrite append_letters_inv /= -{3}[k]opprK.
  have /orP [/[dup] ? ->|/[dup] ? /negbTE ->] := orbN (k - k' == 0).
  + have <-: k = k' by lia.
    by rewrite append_same_cancel.
  + by rewrite append_same_add addrC opprK.
- by rewrite /= mulN1r append_letters_inv /= opprK.
- by rewrite /= mulN1r append_letters_inv /= opprK.
- by rewrite /= mulN1r append_letters_inv /= opprK.
- by rewrite /= mul1r.
- by rewrite /= mul1r.
- rewrite /= mul1r cats0.
  have /orP [/[dup] ? ->|/[dup] ? /negbTE ->] := orbN (k + k' == 0).
  + have ->: k = -k' by lia.
    by rewrite append_same_cancel.
  + by rewrite append_same_add /= addrC.
- by rewrite /= mul1r.
- by rewrite /= mulN1r append_letters_inv /= opprK.
- by rewrite /= mulN1r append_letters_inv /= opprK.
- rewrite /= mulN1r cats0.
  rewrite append_letters_inv /= -{3}[k]opprK.
  have /orP [/[dup] ? ->|/[dup] ? /negbTE ->] := orbN (k - k' == 0).
  + have <-: k = k' by lia.
    by rewrite append_same_cancel.
  + by rewrite append_same_add addrC opprK.
- by rewrite /= mulN1r append_letters_inv /= opprK.
Qed.

Lemma merge_counts_append_letters_C l l' c k:
  append_letters_to_count c k (merge_counts l l') = merge_counts (append_letters_to_count c k l) l'.
Proof.
elim: l c k => [/= c k|[topn topc] l IH c k].
  by case: c => /=; rewrite ?mul1r // append_letters_inv mulN1r /=.
rewrite [merge_counts ((topn, topc) :: l) l']/= {}IH.
by rewrite !merge_counts_remove_append.
Qed.

Lemma count_letters_cat (w w': F2):
  F2_count_letters (w @ w') = merge_counts (F2_count_letters w) (F2_count_letters w').
Proof.
elim: w => [/=|a l /= ->]; first by rewrite /law/=.
by rewrite merge_counts_append_letters_C.
Qed.

(*
Lemma count_letters_inv (w: F2):
  F2_count_letters (inv w) = map (fun '(c, n) => (c, -n)) (F2_count_letters w).
Proof.
Admitted.

Lemma count_letters_power_a: forall k, F2_count_letters (power (`[a] : F2) k) =
  if k != 0 then [:: (a, k)] else nil.
Proof.
elim => // [k IH|k IH].
- rewrite powerS count_letters_cat {}IH.
  have /orP [->|] := orbN (k != 0); first by rewrite /= mulr1 mul1r.
  by rewrite negbK => /eqP -> /=; rewrite mulr1.
- have /orP [-> {IH}|] := orbN (- k.+1%:Z != 0); last first.
    by rewrite negbK => /eqP -> /=.
  elim: k => //= k.
  rewrite !count_letters_inv count_letters_cat /=.
  elim: k => //= k IH IH'.
Admitted.
*)

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
  admit.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (inv (encoding s1.1)) = false by admit.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (power (`[b]: F2) s1.2) = true by admit.
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

Section IsoOfTransMorphism.
Variable t: Transition.

Lemma iot_preserve_e: iso_of_transition t e == e.
Proof.
rewrite /iso_of_transition/=.
move: P_neutral; case=> decomp [decomp_gens decomp_e] /=.
rewrite /eq/=/subgroupby_eq/=.
(*
move: decomp_gens.
elim: decomp => [//|c l IH /= H].
have H_head := List.Forall_inv H.
have {H} H_tail := List.Forall_inv_tail H.
rewrite IH //.
rewrite List.Exists_exists; case=> s [?].

have: forall l1 l2,
  ListDef.Forall (fun el =>
    List.Exists (fun gen => 
      gen == el \/ inv gen == el
    ) (affine_state_encoding_gens t.1)
  ) l2
    ->
  ListDef.Forall (fun el =>
    List.Exists (fun gen => 
      gen == el \/ inv gen == el
    ) (affine_state_encoding_gens t.1)
  ) l1
    ->
  prod l1 == prod l2
    ->
  prod [seq iso_of_transition_gens t el | el <- l1] == prod [seq iso_of_transition_gens t el | el <- l2].

*)
Admitted.

Lemma iotg_invK: forall c,
  iso_of_transition_gens t c @ iso_of_transition_gens t (inv c) == e.
Admitted.

Lemma iot_preserve_equiv: forall (x y: affine_state_encoding t.1),
  x == y -> iso_of_transition t x == iso_of_transition t y.
Proof.
move=> x y H.
rewrite /iso_of_transition/=.
elim: (sb_point_characterization x) => decomp_x [decomp_x_gens decomp_x_e].
elim: (sb_point_characterization y) => decomp_y [decomp_y_gens decomp_y_e].
rewrite /eq/=/subgroupby_eq/=.
move: H; rewrite {1}/eq/=/subgroupby_eq/=/subgroupby_inj/= {}decomp_x_e {}decomp_y_e.

move: decomp_x decomp_y decomp_y_gens decomp_x_gens.
elim=> [decomp_y decomp_y_gens _ /=|/= c l IH decomp_y decomp_y_gens H].





  elim: decomp_y decomp_y_gens => [//|c' l' IH /= H].
  have H_head := List.Forall_inv H.
  have {H} H_tail := List.Forall_inv_tail H.

  admit.

have H_head := List.Forall_inv H.
have {H} H_tail := List.Forall_inv_tail H.

move: decomp_y decomp_y_gens; elim=> [/= _ H'|].
  have {}H': prod l == prod [:: inv c].
    rewrite /= neutral_right.
    have: (inv c) @ c @ prod l == inv c.
      by rewrite -associativity H' neutral_right.
    by rewrite inverse_right neutral_left.
  rewrite {IH} (IH [:: inv c]) //= ?neutral_right ?iotg_invK //.
  apply /List.Forall_cons /List.Forall_nil.
  move: H_head; apply /List.Exists_impl => c' [->|<-]; first by right.
  by left; rewrite inv_involutive.
move=> c' l' IH' H' /= H''.
have H'_head := List.Forall_inv H'.
have {H'} H'_tail := List.Forall_inv_tail H'.
rewrite {IH} (IH ((inv c)::c'::l')) //=; first last.
- have: (inv c) @ (c @ prod l) == inv c @ (c' @ prod l') by rewrite H''.
  by rewrite !associativity inverse_right neutral_left => ->.
- apply /List.Forall_cons; last by apply /List.Forall_cons => //.
  move: H_head; apply /List.Exists_impl => ? [->|<-]; first by right.
  by rewrite inv_involutive; left.
- by rewrite associativity iotg_invK neutral_left.
Admitted.

(*
Lemma iot_prod_map_vertical: forall l1 l2,
  ListDef.Forall (fun el =>
    List.Exists (fun gen => 
      gen == el \/ inv gen == el
    ) (affine_state_encoding_gens t.1)
  ) l1
    ->
  ListDef.Forall (fun el =>
    List.Exists (fun gen => 
      gen == el \/ inv gen == el
    ) (affine_state_encoding_gens t.1)
  ) l2
    ->
  prod l1 == prod l2
    ->
  prod (map (iso_of_transition_gens t) l1) == prod (map (iso_of_transition_gens t) l2).
Proof.
move=> l1 l2.
Admitted.
*)

Lemma iot_preserve_law: forall (x y: affine_state_encoding t.1),
  iso_of_transition t (x @ y) == (iso_of_transition t x) @ (iso_of_transition t y).
Proof.
move=> x y.
rewrite /iso_of_transition/=.
set H := P_law (sb_point x) (sb_point y) (sb_point_characterization x) (sb_point_characterization y).
case: H => decomp_xy [decomp_xy_gens decomp_xy_e] /=.
elim: (sb_point_characterization x) => decomp_x [decomp_x_gens decomp_x_e].
elim: (sb_point_characterization y) => decomp_y [decomp_y_gens decomp_y_e].
rewrite /eq/=/subgroupby_eq/=.
rewrite -prod_cat -map_cat.
Admitted.

HB.instance Definition _ := isMonoidMorphism.Build (affine_state_encoding t.1) (affine_state_encoding t.2) (iso_of_transition t) iot_preserve_equiv iot_preserve_e iot_preserve_law.

Lemma iot_preserve_inv: forall (x: affine_state_encoding t.1),
  inv (iso_of_transition t x) == iso_of_transition t (inv x).
Proof.
move=> x.
rewrite /iso_of_transition/=.
set H := P_inv (sb_point x) (sb_point_characterization x).
case: H => decomp_ix [decomp_ix_gens decomp_ix_e] /=.
elim: (sb_point_characterization x) => decomp_x [decomp_x_gens decomp_x_e].
rewrite /eq/=/subgroupby_eq/=.
Admitted.

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

Lemma encoding_free zs z':
  prod [seq encoding z | z <- zs] == encoding z' -> z' \in zs.
Proof.
move=> /F2_dec_eq_reflect; rewrite /F2_dec_eq.
elim: zs z' => [/= z'|z' zs IH y /=].
  rewrite /encoding power_inv -(inverse_left (power (`[b]: F2) z')) => R.
  have := cancel_right _ _ _ R.
  rewrite -{1}[power (`[b]: F2) z']neutral_right => {}R.
  have := cancel_left _ _ _ R.
  by move=> /F2_dec_eq_reflect.

have /orP [] := orbN (z' == y).

Lemma equiv_m_if_inH:
    (encoding z) \insubgroup K
      ->
    equivalence_problem A z m.
Proof.
case=> x.
rewrite /subgroup_inj/=/subgroupby_inj/=.
case: (sb_point_characterization x) => decomp_x [/[swap] ->].
rewrite /K_defining_property.




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
