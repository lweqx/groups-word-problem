From Undecidability Require Import Synthetic.Definitions Synthetic.Undecidability.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint.

From GWP Require Import Presentation AffineMachines F2 EquivalenceAlgebra.

Record GWPArguments := {
  P : invertiblePresentationType;
  u : presented P;
  v : presented P;
}.
Definition GWP_uncurried args := word_problem (P args) (u args) (v args).

Section Reduction.

Variable A: Machine.
Variable z m: int.

Import PresentationNotations.

Import intZmod.

(* `encoding k` is `a_k = b^k a b^-k` *)
Definition encoding (k: int) : F2 := (power (`[b]: F2) k) @ `[a] @ (power (`[b]: F2) (oppz k)).

Definition admit {T: Type} : T.
Admitted.

Definition reduction_output : GWPArguments := {|
  P := admit;
  u := admit;
  v := admit;
|}.

End Reduction.

Lemma novikov_bool_reduction : equivalence_problem_uncurried ⪯ GWP_uncurried.
Proof.
exists (fun '(A, z, m) => reduction_output A z m).
move=> [[A z] m].
rewrite /equivalence_problem_uncurried /GWP_uncurried.
Admitted.

Theorem novikov_boone : undecidable GWP_uncurried.
Proof.
apply: (undecidability_from_reducibility equivalence_problem_undecidable).
exact: novikov_bool_reduction.
Qed.
