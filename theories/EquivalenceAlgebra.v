From elpi.apps Require Import coercion.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.
Require Import Setoid Morphisms.
From Stdlib Require List.

From GWP Require Import Equivalence.

Open Scope int_scope.
Open Scope ring_scope.

HB.mixin Record isMonoid M of hasEq M := {
  law : M -> M -> M;
  e : M;
  associativity : forall x y z, law x (law y z) == law (law x y) z;
  neutral_left : forall x, law e x == x;
  neutral_right : forall x, law x e == x;
  congruent_left : forall x y z, y == z -> law x y == law x z;
  congruent_right : forall x y z, y == z -> law y x == law z x;
}.
#[short(type="monoid")]
HB.structure Definition Monoid := { G of isMonoid G & hasEq G }.
Infix "@" := law (at level 50).

Section ProperMonoid.
HB.declare Context G of hasEq G & isMonoid G.

Global Instance : Proper (eq ==> eq ==> eq) (law : G -> G -> G).
Proof.
move=> a b eq_ab u v eq_uv.
transitivity (a @ v); do [exact: congruent_left|exact: congruent_right].
Qed.

End ProperMonoid.

(* If `l = [a; b; c; ...; z]`, `prod l = a @ b @ ... @ z` *)
Definition prod {M: monoid} (l: seq M) : M := foldr (fun y acc => y @ acc) e l.

Lemma prod0 {M: monoid} : @prod M nil = e.
Proof. done. Qed.

Lemma prod1s {M: monoid} (a: M) (l: seq M) : prod (a :: l) == a @ prod l.
Proof. rewrite /prod/=; reflexivity. Qed.

Lemma prod_cat {M: monoid} (l1 l2: seq M): prod (l1 ++ l2) == (prod l1) @ (prod l2).
Proof.
elim: l1 => [|a l1 /= ->]; first by rewrite /= neutral_left.
by rewrite associativity.
Qed.

HB.mixin Record isMonoidMorphism (G H: monoid) (f: G -> H) := {
  morphism_preserve_equiv: forall x y, x == y -> f x == f y;
  morphism_preserve_e: f e == e;
  morphism_preserve_law: forall x y, f (x @ y) == (f x) @ (f y);
}.
#[short(type="monoidMorphism")]
HB.structure Definition MonoidMorphism (G H: monoid) := { f of isMonoidMorphism G H f }.

Section ProperMorphism.
Variable G H: monoid.
Variable f: monoidMorphism G H.

Global Instance : Proper (eq ==> eq) f.
Proof. exact: morphism_preserve_equiv. Qed.

End ProperMorphism.

HB.mixin Record isInjective (A B: equivType) (f: A -> B) := {
  injectivity_property: forall x y, f x == f y -> x == y;
}.

#[short(type="injectiveFunType")]
HB.structure Definition Injective (A B: equivType) := { f of isInjective A B f }.

#[short(type="injectiveMonoidMorphism")]
HB.structure Definition InjectiveMonoidMorphism (G H: monoid) := { f of isInjective G H f & isMonoidMorphism G H f }.

HB.mixin Record isGroup G of hasEq G & isMonoid G := {
  inv : G -> G;
  inverse_law : forall x y, inv (x @ y) == (inv y) @ (inv x);
  inverse_left : forall x, x @ (inv x) == e;
  inverse_right : forall x, (inv x) @ x == e;
}.
#[short(type="group")]
HB.structure Definition Group := { G of isGroup G & hasEq G & isMonoid G }.

Lemma inv_involutive {G: group}: forall (g: G), inv (inv g) == g.
Proof.
move=> g.
have: (inv g) @ (inv (inv g)) == (inv g) @ g.
  by rewrite inverse_left inverse_right.
move=> /(congruent_left g).
by rewrite !associativity inverse_left !neutral_left.
Qed.

Section ProperGroup.
HB.declare Context G of hasEq G & isMonoid G & isGroup G.

Global Instance : Proper (eq ==> eq) (inv : G -> G).
Proof.
move=> a b eq_ab.
have H: (inv a) @ b == e; first by rewrite -eq_ab inverse_right.
have: (inv a) @ b @ (inv b) == (inv b); first by rewrite H neutral_left.
by rewrite -associativity inverse_left neutral_right.
Qed.

End ProperGroup.

Lemma inv_e {G: group}: inv (s:=G) e == e.
Proof. by rewrite -{1}[inv e]neutral_right inverse_right. Qed.

HB.mixin Record isInvMorphism (G H: group) (f: G -> H) := {
  morphism_preserve_inv: forall x, inv (f x) == f (inv x);
}.
#[short(type="morphism")]
HB.structure Definition Morphism (G H: group) := { f of isMonoidMorphism G H f & isInvMorphism G H f }.

#[short(type="injectiveMorphism")]
HB.structure Definition InjectiveMorphism (G H: group) := { f of isInjective G H f & isInvMorphism G H f & isMonoidMorphism G H f }.

Definition power {G: group} (w: G) (k: int) : G :=
  match k with
  | Posz k => iter k (fun acc => acc @ w) e
  | Negz k => inv (iter k (fun acc => acc @ w) w) (* Negx 0 is -1 *)
  end.

Lemma power0 {G: group} (w: G) : power w 0 = e.
Proof. done. Qed.

Lemma power_e {G: group} (k: int) : power (e (s:=G)) k == (e (s:=G)).
Proof.
case: k => [k|k].
- elim: k => [//|k /=].
  by rewrite neutral_right.
- elim: k => [/=|k /=]; first by rewrite inv_e.
  by rewrite inverse_law inv_e neutral_left.
Qed.

Lemma powerS {G: group} (w: G) (x: nat) : power w x.+1 = (power w x) @ w.
Proof. done. Qed.

Lemma power_inv {G: group} (w: G) (x:int) : power w (- x) == inv (power w x).
Proof.
elim: x => [|k|k /=].
- by rewrite /= inv_e.
- case: k => [_|k].
    by rewrite /= inverse_law inv_e neutral_right.
  by rewrite /= !inverse_law => ->.
- case: k => [_|k].
    by rewrite /= inv_involutive neutral_left.
  by rewrite /= !inv_involutive => ->.
Qed.

Lemma powerP {G: group} (w: G) (x: nat) : power w (- x.+1%:Z) == (inv w) @ (power w (-x%:Z)).
Proof. by rewrite power_inv powerS inverse_law power_inv. Qed.

Lemma powerC' {G: group} (w: G) (x: int) : (power w x) @ w == w @ (power w x).
Proof.
elim: x => [|x /= eq|x].
- by rewrite power0 neutral_left neutral_right.
- by rewrite associativity -eq.
- rewrite !power_inv /= inverse_law => eq.
  rewrite -associativity eq.
  by rewrite !associativity inverse_right inverse_left.
Qed.

Lemma powerC'' {G: group} (w: G) (x: int) : (power w x) @ (inv w) == (inv w) @ (power w x).
Proof.
elim: x => [|x eq|x].
- by rewrite power0 neutral_left neutral_right.
- rewrite powerS -associativity inverse_left neutral_right.
  by rewrite powerC' associativity inverse_right neutral_left.
- rewrite !power_inv => eq.
  by rewrite powerS inverse_law -associativity eq.
Qed.

Lemma powerC {G: group} (w: G) (x y: int) : (power w x) @ (power w y) == (power w y) @ (power w x).
Proof.
elim: x.
- by rewrite power0 neutral_left neutral_right.
- move=> x /= eq.
  rewrite associativity -eq.
  rewrite -!associativity.
  by rewrite powerC'.
- move=> x.
  rewrite !power_inv powerS inverse_law => eq.
  rewrite -associativity eq.
  by rewrite !associativity powerC''.
Qed.

Lemma powerS' {G: group} (w: G) (x: int) : power w (x + 1) == (power w x) @ w.
Proof.
elim: x => [//|x eq|x _].
  by rewrite /= addn1.
rewrite !power_inv powerS inverse_law -associativity.
have ->: (- x.+1%:Z + 1) = (- x%:Z) by lia.
rewrite associativity -inverse_law powerC' inverse_law.
rewrite -associativity inverse_right neutral_right.
by rewrite power_inv.
Qed.

Lemma powerP' {G: group} (w: G) (x: int) : power w (x - 1) == (inv w) @ (power w x).
Proof.
elim: x => [|x eq|x eq].
- by rewrite neutral_right.
- have ->: x.+1%:Z - 1 = x by lia.
  by rewrite powerS powerC' associativity inverse_right neutral_left.
- have ->: - x.+1%:Z - 1 = - x.+2%:Z by lia.
  by rewrite /= inverse_law.
Qed.

Lemma poweradd {G: group} (w: G) (x y: int) : power w (x + y) == (power w x) @ (power w y).
Proof.
elim: x.
- by rewrite add0r power0 neutral_left.
- move=> x eq.
  rewrite powerS powerC' -associativity -eq -powerC'.
  have ->: x.+1%:Z + y = (x%:Z + y) + 1 by lia.
  by rewrite powerS'.
- move=> x eq.
  rewrite power_inv powerS inverse_law.
  have ->: - x.+1%:Z + y = (- x%:Z + y) - 1 by lia.
  by rewrite powerP' eq associativity power_inv.
Qed.

Lemma power_switch_sign {G: group} (w: G) (x y: int): power (power w x) (- y) == power (power w (-x)) y.
Proof.
elim: y => [|y|y].
- by rewrite oppr0 !power0.
- rewrite powerP powerS => ->.
  by rewrite -power_inv powerC'.
- rewrite !opprK powerS powerP => ->.
  by rewrite -powerC'' -power_inv opprK.
Qed.

Lemma powerC'_tower {G: group} (w: G) (x y: int): power (power w x) y @ w == w @ power (power w x) y.
Proof.
elim: y => [|y|y].
- by rewrite power0 neutral_left neutral_right.
- rewrite powerS -associativity powerC' associativity => ->.
  by rewrite associativity.
- rewrite powerP -associativity => ->.
  by rewrite associativity -power_inv powerC' associativity.
Qed.

Lemma powerC''_tower {G: group} (w: G) (x y: int): power (power w x) y @ (inv w) == (inv w) @ power (power w x) y.
Proof.
elim: y => [|y|y].
- by rewrite power0 neutral_left neutral_right.
- rewrite powerS -associativity powerC'' associativity => ->.
  by rewrite associativity.
- rewrite powerP -associativity => ->.
  by rewrite associativity -power_inv powerC'' associativity.
Qed.

Lemma powermul {G: group} (w: G) (x y: int) : power w (x * y) == power (power w x) y.
Proof.
elim: x => [|x|x].
- by rewrite mul0r !power0 power_e.
- rewrite powerS.
  have ->: x.+1%:Z * y = x%:Z * y + y by lia.
  rewrite poweradd => ->.
  elim: y => [|y|y].
  - by rewrite !power0 neutral_left.
  - rewrite !powerS => <-.
    rewrite associativity -[(_ @ (power w x)) @ (power w y)]associativity.
    by rewrite powerC associativity -associativity.
  - rewrite !power_switch_sign !powerP => <-.
    rewrite powerS inverse_law.
    rewrite associativity -[(_ @ _) @ inv w]associativity.
    rewrite powerC'' associativity powerC''_tower.
    rewrite associativity.
    rewrite -[(_ @ (inv (power w x))) @ _]associativity.
    rewrite -power_switch_sign -powerC'' associativity.
    by rewrite !power_inv.
- have ->: - x.+1%:Z * y = - x%:Z*y + (-y) by lia.
  rewrite poweradd => ->.
  elim: y => [|y|y].
  - by rewrite !power0 neutral_left.
  - rewrite !powerS => <-.
    rewrite -[(_ @ (power w (- y%:Z))) @ _]associativity powerC.
    rewrite !powerP.
    rewrite associativity -[(_ @ _) @ (inv w)]associativity.
    by rewrite powerC'' -associativity.
  - have ->: (- - y%:Z) = y%:Z by lia.
    have ->: (- - y.+1%:Z) = y.+1%:Z by lia.
    rewrite powerS [power _ (- y.+1%:Z)]powerP.
    rewrite associativity -[(_ @ _) @ power w y]associativity => ->.
    rewrite -associativity.
    rewrite powerC'_tower [power (power _ _) (- _.+1%:Z)]powerP.
    rewrite !power_inv inv_involutive -!power_inv opprK.
    by rewrite powerS associativity.
Qed.

#[short(type="deceqGroupType")]
HB.structure Definition DecEqGroup := { G of isGroup G & hasEq G & isMonoid G & hasDecEq G }.

HB.mixin Record isSubgroup (G: group) (H: group) := {
  subgroup_inj: injectiveMorphism H G;
}.

#[short(type="subgroup")]
HB.structure Definition Subgroup (G: group) := { H of isSubgroup G (* super group *) H (* sub group *)}.

Elpi Accumulate coercion.db lp:{{

% See https://rocq-prover.zulipchat.com/#narrow/channel/237868-Hierarchy-Builder-devs-.26-users/topic/Missing.20instance.20in.20a.20hierarchy.20for.20subtypes/with/561428680
coercion _ T {{ Type }} ExpectedType Solution :-
  ExpectedType = {{ subgroup _ }},
  coq.elaborate-skeleton {{ ( lp:T : group) }} ExpectedType Solution Diagnostics,
  ok = Diagnostics.

}}.

(* TODO: it would be cool to "register" subgroup_inj as a coercion.
   I don't think it can be done via the vanilla Rocq coercions, and doing so via a coercion hook
   seems difficult without triggering an infinite coercion chain. *)

Definition in_subgroup {G: group} (K: subgroup G) (x: G) := { x': K | subgroup_inj x' == x }.
Notation "x '\insubgroup' K" := (in_subgroup K x) (at level 10).

Definition is_subgroup_stable {G: group} {H1 H2: subgroup G} (f: morphism H1 H2) (K: subgroup G) :=
  forall (x: H1), ((subgroup_inj x) \insubgroup K) -> subgroup_inj (f x) \insubgroup K.

Record local_morphism (G: group) := {
  lm_source_subgroup : subgroup G;
  lm_target_subgroup : subgroup G;
  lm_morphism :> morphism lm_source_subgroup lm_target_subgroup;
}.
Arguments lm_source_subgroup {_}.
Arguments lm_target_subgroup {_}.
Coercion morphism_to_local_morphism {G} {H1 H2: subgroup G}: morphism H1 H2 -> local_morphism G :=
  fun f => {| lm_morphism := f |}.

Section SelfSubgroup.
Variable K: group.

(* instanciating everything on K directly would not work well because
   the key for the isSubgroup mixin is the super-group, meaning
   that we couldn't have both K: subgroup K and K: subgroup H. *)
Definition selfsubgroup := K.

Definition identity_morphism: selfsubgroup -> selfsubgroup := id.

Lemma im_preserve_equiv: forall x y, x == y -> identity_morphism x == identity_morphism y.
Proof. done. Qed.
Lemma im_preserve_e: identity_morphism e == e.
Proof. done. Qed.
Lemma im_preserve_law: forall x y, identity_morphism (x @ y) == (identity_morphism x) @ (identity_morphism y).
Proof. done. Qed.
Lemma im_preserve_inv: forall x, identity_morphism (inv x) == inv (identity_morphism x).
Proof. done. Qed.

HB.instance Definition _ := isMonoidMorphism.Build K selfsubgroup identity_morphism im_preserve_equiv im_preserve_e im_preserve_law.
HB.instance Definition _ := isInvMorphism.Build K selfsubgroup identity_morphism im_preserve_inv.

Lemma im_injective_property: forall x y, identity_morphism x == identity_morphism y -> x == y.
Proof. done. Qed.

HB.instance Definition _ := isInjective.Build K selfsubgroup identity_morphism im_injective_property.

HB.instance Definition _ := isSubgroup.Build K selfsubgroup identity_morphism.

End SelfSubgroup.

Definition transport {A} {P: A -> Type} {x y: A} (e: x = y): P y -> P x.
Proof. by elim: e. Qed.

HB.mixin Record isSubgroupCharacterizer (G: group) (P: G -> Type) := {
  P_law: forall x y, P x -> P y -> P (x @ y);
  P_neutral: P e;
  P_inv: forall x, P x -> P (inv x);
}.
#[short(type = "subgroup_characterizer")]
HB.structure Definition SubgroupCharacterizer (G: group) := { P of isSubgroupCharacterizer G P }.

Section SubgroupByCharacterization.
Variable G: group.
Variable P: subgroup_characterizer G.

#[projections(primitive)]
Record subgroup_by := {
  sb_point: G;
  sb_point_characterization: P sb_point;
}.

Definition subgroupby_inj (x: subgroup_by): G := x.(sb_point).

Definition subgroupby_eq (x y: subgroup_by) := (subgroupby_inj x) == (subgroupby_inj y).
Lemma subgroupby_eq_refl: forall x, subgroupby_eq x x.
Proof. move=> x; rewrite /subgroupby_eq; reflexivity. Qed.
Lemma subgroupby_eq_sym: forall x y, subgroupby_eq x y -> subgroupby_eq y x.
Proof. move=> x y; rewrite /subgroupby_eq; by symmetry. Qed.
Lemma subgroupby_eq_trans: forall x y z, subgroupby_eq x y -> subgroupby_eq y z -> subgroupby_eq x z.
Proof. move=> x y z; rewrite /subgroupby_eq => ? ?; by transitivity (subgroupby_inj y). Qed.

HB.instance Definition _ := hasEq.Build subgroup_by subgroupby_eq subgroupby_eq_refl subgroupby_eq_sym subgroupby_eq_trans.

Definition subgroupby_law (x y : subgroup_by): subgroup_by.
Proof.
exists (x.(sb_point) @ y.(sb_point)).
apply /P_law; exact /sb_point_characterization.
Defined.

Definition subgroupby_neutral: subgroup_by.
Proof. exists e; exact: P_neutral. Defined.

Lemma subgroupby_associativity: forall (x y z: subgroup_by), subgroupby_law x (subgroupby_law y z) == subgroupby_law (subgroupby_law x y) z.
Proof. move=> x y z; by rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/= associativity. Qed.

Lemma subgroupby_neutral_left: forall (x: subgroup_by), subgroupby_law subgroupby_neutral x == x.
Proof. move=> x; by rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/= neutral_left. Qed.

Lemma subgroupby_neutral_right: forall (x: subgroup_by), subgroupby_law x subgroupby_neutral == x.
Proof. move=> x; by rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/= neutral_right. Qed.

Lemma subgroupby_congruent_left: forall (x y z: subgroup_by), y == z -> subgroupby_law x y == subgroupby_law x z.
Proof.
move=> x y z ?.
rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/=.
exact: congruent_left.
Qed.

Lemma subgroupby_congruent_right: forall (x y z: subgroup_by), y == z -> subgroupby_law y x == subgroupby_law z x.
Proof.
move=> x y z ?.
rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/=.
exact: congruent_right.
Qed.

HB.instance Definition _ := isMonoid.Build subgroup_by subgroupby_law subgroupby_neutral subgroupby_associativity subgroupby_neutral_left subgroupby_neutral_right subgroupby_congruent_left subgroupby_congruent_right.

Definition subgroupby_inv: subgroup_by -> subgroup_by.
Proof. move=> x; exists (inv x.(sb_point)); exact /P_inv /sb_point_characterization. Defined.

Lemma subgroupby_inverse_law: forall x y, subgroupby_inv (x @ y) == (subgroupby_inv y) @ (subgroupby_inv x).
Proof. move=> x y; by rewrite /subgroupby_inv/=/eq/=/subgroupby_eq/subgroupby_inj/= inverse_law. Qed.

Lemma subgroupby_inverse_left : forall x, x @ (subgroupby_inv x) == e.
Proof. move=> x; by rewrite /subgroupby_inv/=/law/=/subgroupby_law/=/eq/=/subgroupby_eq/=/subgroupby_inj/= inverse_left. Qed.

Lemma subgroupby_inverse_right : forall x, (subgroupby_inv x) @ x == e.
Proof. move=> x; by rewrite /subgroupby_inv/=/law/=/subgroupby_law/=/eq/=/subgroupby_eq/=/subgroupby_inj/= inverse_right. Qed.

HB.instance Definition _ := isGroup.Build subgroup_by subgroupby_inv subgroupby_inverse_law subgroupby_inverse_left subgroupby_inverse_right.

Lemma subgroupby_inj_injectivity: forall x y, x == y -> subgroupby_inj x == subgroupby_inj y.
Proof. done. Qed.

HB.instance Definition _ := isInjective.Build _ _ subgroupby_inj subgroupby_inj_injectivity.

Lemma subgroupby_inj_preserve_equiv: forall x y, x == y -> subgroupby_inj x == subgroupby_inj y.
Proof. done. Qed.
Lemma subgroupby_inj_preserve_e: subgroupby_inj e == e.
Proof. done. Qed.
Lemma subgroupby_inj_preserve_law: forall x y, subgroupby_inj (law x y) == law (subgroupby_inj x) (subgroupby_inj y).
Proof. done. Qed.
Lemma subgroupby_inj_preserve_inv: forall x, inv (subgroupby_inj x) == subgroupby_inj (inv x).
Proof. done. Qed.

HB.instance Definition _ := isMonoidMorphism.Build _ _ subgroupby_inj subgroupby_inj_preserve_equiv subgroupby_inj_preserve_e subgroupby_inj_preserve_law.
HB.instance Definition _ := isInvMorphism.Build _ _ subgroupby_inj subgroupby_inj_preserve_inv.

HB.instance Definition _ := isSubgroup.Build G subgroup_by subgroupby_inj.

End SubgroupByCharacterization.
Arguments subgroup_by {_}.
Arguments sb_point_characterization {_ _}.
Arguments sb_point {_ _}.

(* Subgroup generated by a finite set of group elements *)
Section GeneratedSubgroup.

Variable G: group.
Variable generators: seq G.

Definition in_generated_subgroup (x: G): Type :=
  { decomp: seq G |
    (List.Forall (fun el =>
      List.Exists (fun gen => gen == el \/ inv gen == el) generators
    ) decomp)
      /\
    (x == prod decomp) }.

Lemma igs_P_law: forall (x y: G), in_generated_subgroup x -> in_generated_subgroup y -> in_generated_subgroup (x @ y).
Proof.
move=> x y [decomp_x [decomp_x_gens x_eq]] [decomp_y [decomp_y_gens y_eq]].
exists (decomp_x ++ decomp_y); split; first by rewrite List.Forall_app; split.
by rewrite prod_cat x_eq y_eq.
Qed.

Lemma igs_P_neutral: in_generated_subgroup e.
Proof. exists nil; split=> //. Qed.

Lemma revE: forall {A} (l: seq A), rev l = List.rev l.
Proof. by move=> A; elim=> [//|a l /=]; rewrite -cat1s rev_cat => ->. Qed.

Lemma igs_P_inv: forall (x: G), in_generated_subgroup x -> in_generated_subgroup (inv x).
Proof.
move=> x [decomp_x [decomp_x_gens x_eq]].
exists (rev (map inv decomp_x)); split; first last.
  rewrite {}x_eq => {decomp_x_gens}.
  elim: decomp_x => [|a l]; first by rewrite prod0 inv_e.
  rewrite prod1s inverse_law => ->.
  by rewrite map_cons -cat1s rev_cat prod_cat /= neutral_right.
rewrite revE; apply /List.Forall_rev.
move: decomp_x_gens; rewrite List.Forall_map.
apply /List.Forall_impl => g.
apply /List.Exists_impl => g' [] eq; first by right; rewrite eq.
by left; rewrite -[g']inv_involutive eq.
Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build G in_generated_subgroup igs_P_law igs_P_neutral igs_P_inv.

Definition generatedSubgroup := subgroup_by in_generated_subgroup.

End GeneratedSubgroup.
Arguments generatedSubgroup {_}.
Arguments in_generated_subgroup {_}.

(* Subgroup generated by a property characterizing its generators. *)
Section SubgroupByGensCharacterizer.

Variable G: group.
Variable gen_characterizer: G -> Prop.

Hypothesis gen_characterizer_preserve_eq: forall x x', x == x' ->
  gen_characterizer x -> gen_characterizer x'.

Definition in_generated_subgroup2 (x: G): Type :=
  { decomp: seq G |
    (List.Forall (fun el => gen_characterizer el \/ gen_characterizer (inv el)) decomp)
      /\
    (x == prod decomp) }.

Lemma igs2_P_law: forall (x y: G), in_generated_subgroup2 x -> in_generated_subgroup2 y -> in_generated_subgroup2 (x @ y).
Proof.
move=> x y [decomp_x [decomp_x_gens x_eq]] [decomp_y [decomp_y_gens y_eq]].
exists (decomp_x ++ decomp_y); split; first by rewrite List.Forall_app; split.
by rewrite prod_cat x_eq y_eq.
Qed.

Lemma igs2_P_neutral: in_generated_subgroup2 e.
Proof. exists nil; split=> //. Qed.

Lemma igs2_P_inv: forall (x: G), in_generated_subgroup2 x -> in_generated_subgroup2 (inv x).
Proof.
move=> x [decomp_x [decomp_x_gens x_eq]].
exists (rev (map inv decomp_x)); split; first last.
  rewrite {}x_eq => {decomp_x_gens}.
  elim: decomp_x => [|a l]; first by rewrite prod0 inv_e.
  rewrite prod1s inverse_law => ->.
  by rewrite map_cons -cat1s rev_cat prod_cat /= neutral_right.
rewrite revE; apply /List.Forall_rev.
move: decomp_x_gens; rewrite List.Forall_map.
apply /List.Forall_impl => g.
case=> H ; last by left.
right; move: H.
apply /gen_characterizer_preserve_eq.
by rewrite inv_involutive.
Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build G in_generated_subgroup2 igs2_P_law igs2_P_neutral igs2_P_inv.

Definition generatedSubgroupByProp := subgroup_by in_generated_subgroup2.

End SubgroupByGensCharacterizer.
Arguments generatedSubgroupByProp {_}.
Arguments in_generated_subgroup2 {_}.

(* Intersection of subgroups *)
Section SubgroupIntersection.
Variable G: group.
Variable (H1 H2: subgroup G).

Record is_in_intersection (x: G) : Type := {
  intersection_in_left: x \insubgroup H1;
  intersection_in_right: x \insubgroup H2;
}.

Definition iii_P_law : forall (x y: G), is_in_intersection x -> is_in_intersection y -> is_in_intersection (x @ y).
Proof.
move=> x y [[x1 x1_eq] [x2 x2_eq]] [[y1 y1_eq] [y2 y2_eq]]; eexists.
- by exists (x1 @ y1); rewrite morphism_preserve_law -x1_eq -y1_eq.
- by exists (x2 @ y2); rewrite morphism_preserve_law -x2_eq -y2_eq.
Qed.

Definition iii_P_neutral : is_in_intersection e.
Proof. by eexists; exists e; rewrite morphism_preserve_e. Qed.

Definition iii_P_inv : forall (x: G), is_in_intersection x -> is_in_intersection (inv x).
Proof.
move=> x [[x1 x1_eq] [x2 x2_eq]]; eexists.
- by exists (inv x1); rewrite -morphism_preserve_inv -x1_eq.
- by exists (inv x2); rewrite -morphism_preserve_inv -x2_eq.
Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build G is_in_intersection iii_P_law iii_P_neutral iii_P_inv.

(* we could also prove that H1 /\ H2 is a subgroup of H1 and H2 *)

Definition intersection := subgroup_by is_in_intersection.

End SubgroupIntersection.
