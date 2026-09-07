(**************************************

In this file we prove some of the coherence laws of the monoidal structure, namely:

- leftunitor/rightunitor:
  - naturality
  - isolaw

**************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Require Import preliminaries.
Require Import double_pullbacks.
Require Import natural_contraction.

Require Import double_gluing.double_gluing.

Require Import double_gluing.monoidal.tensor_unit.
Require Import double_gluing.monoidal.left_unitor.
Require Import double_gluing.monoidal.right_unitor.
Require Import double_gluing.monoidal.associator.
Require Import double_gluing.monoidal.monoidal_data.

Lemma double_glued_luiso {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : disp_leftunitor_iso (disp_monoidal_leftunitor (double_glued_monoidal_data dpbs k))
                                        (disp_monoidal_leftunitorinv (double_glued_monoidal_data dpbs k)).
Proof.
  intros R.
  intros ((U, l), (X, l')).
  apply (is_inv_iff_components_are_inv _ _).
  split.
  exact (monoidal_leftunitorisolaw E U).
  split.
  simpl.
  unfold double_glued_leftunitor_data_comp2, double_glued_leftunitorinv_data_comp2.
  set (dpb := tensor_doublePullback dpbs k ((I_{ E},, fmonoidal_preservesunit L),, K I_{ C},, identity (K I_{ C})) ((U,, l),, X,, l')).
  refine (doublePullbackArrowUnique' dpb (pr11 dpb) (doublePullbackPrL _) (doublePullbackPrM _) (doublePullbackPrR _) (doublePullbackSqrLCommutes _) (doublePullbackSqrRCommutes _) _ _ _ _ @ ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  unfold internal_lam.
  refine (_ @ rightunitors_eval_expand1 X).
  exact (assoc _ _ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f) · _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E I_{E} ))) _ _ _) @ _).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f · _) (monoidal_rightunitorinvnat E _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes dpb) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ id_right _).
  apply maponpaths.
  generalize (pr1 (pr222 k) R); simpl; intros keq.
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, f · _ · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! internal_postcomp_comp _ _ _) @ _).
  rewrite (maponpaths (internal_postcomp (I_{E})) (assoc _ _ _)).
  refine (! maponpaths (λ f, _ · internal_postcomp (I_{E}) (f · _) · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite (maponpaths (internal_postcomp (I_{E})) (assoc' _ _ _)).
  rewrite internal_postcomp_comp.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E I_{ E}))) _ _ _) @ _).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, _ · f) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_rightunitorinvnat E _ _ _) @ _).
  refine (maponpaths (λ f, _ · f) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp (I_{E}) (f · _) · _) (id_left (fmonoidal_preservesunit L ⊗^{ E}_{r} pr1 K (I_{ C} ⊗_{ C} R))) @ _).
  rewrite <- (bifunctor_leftid E).
  refine (! maponpaths (λ f, _ · internal_postcomp (I_{E}) (I_{ E} ⊗^{ E}_{l} f · _ · _) · _) (functor_id K _) @ _).
  rewrite <- (pr1 (monoidal_leftunitorisolaw C R)).
  rewrite (functor_comp K).
  refine (maponpaths (λ f, _ · internal_postcomp (I_{E}) ( f · _ · _) · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  do 2 refine (maponpaths (λ f, _ · internal_postcomp (I_{E}) f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp (I_{E}) (_ · f) · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp (I_{E}) (_ · (f · _)) · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp (I_{E}) (_ · f) · _) keq @ _).  
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (internal_postcomp_comp _ _ _) @ _).
  rewrite (maponpaths (internal_postcomp (I_{E})) (assoc' _ _ _)).
  refine (! maponpaths (λ f, _ · internal_postcomp I_{E} (_ · f) · _) (monoidal_leftunitornat E (K R) _ _) @ _).
  rewrite (maponpaths (internal_postcomp (I_{E})) (assoc _ _ _)).
  refine (! maponpaths (λ f, _ · internal_postcomp I_{E} (f · _) · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp I_{E} (_ ⊗^{E}_{l} f · _) · _) (functor_comp K _ _) @ _).
  rewrite (pr1 (monoidal_leftunitorisolaw C R)).
  rewrite (functor_id K).
  rewrite (bifunctor_leftid E).
  rewrite id_left.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- internal_postcomp_comp.
  refine (maponpaths (λ f, _ · internal_postcomp _ f · _) (sym_mon_braiding_lunitor E _) @ _).
  rewrite assoc.
  exact (! rightunitors_eval_expand2 (K (I_{ C} ⊗_{ C} R))).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (internal_eval_natural _ _ @ _) @ _).
  unfold monoidal_cat_tensor_mor; now rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (monoidal_rightunitorinvnat E _ _ _) @ _).
  apply assoc'.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes dpb)).
  refine (_ @ id_right _).
  rewrite <- internal_postcomp_id.
  refine (_ @ doublePullbackSqrRCommutes dpb).
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite 2 internal_lam_precomp.
  rewrite assoc.
  rewrite 2 internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  do 2 refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  repeat apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) _ @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_rightunitorinvnat E _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (natural_contraction_unit k R @ _) @ _).
  apply (monoidal_leftunitornat E).
  apply assoc.
  apply assoc.
  refine (assoc' _ _ _ @ _ @ id_left _).
  apply map_on_two_paths.
  refine (maponpaths (compose _) (sym_mon_braiding_lunitor E _) @ _).
  refine (_ @ ! rightunitors_eval_expand2 _).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_rightunitorinvnat E _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (internal_eval_nat _ _ _ _ @ _).
  now rewrite hom_onmorphisms_is_postcomp.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (! sym_mon_braiding_lunitor C _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  apply (monoidal_leftunitorisolaw C R).
  exact (id_left _).
  exact (id_left _).
  exact (id_left _).
  refine (assoc (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite assoc.
  exact (! rightunitors_eval_expand2 X). 
Qed.


Lemma double_glued_disp_leftunitor_law {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  disp_leftunitor_law (disp_monoidal_leftunitor (double_glued_monoidal_data dpbs k))
    (disp_monoidal_leftunitorinv (double_glued_monoidal_data dpbs k)).
Proof.
  split.
  intros R1 R2 f12.
  intros ((U1, l1), (X1, l1')).
  intros ((U2, l2), (X2, l2')).
  intros ((ϕ12, eqphi), (ψ12, eqpsi)).
  revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  apply double_glued_mor_eq.
  split.
  unfold transportb, transportf.
  induction (! pr1 (monoidal_leftunitorlaw C) R1 R2 f12).
  exact (monoidal_leftunitornat E _ _ _).
  unfold transportb, transportf.
  induction (! pr1 (monoidal_leftunitorlaw C) R1 R2 f12).
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  10 : {
    apply internal_lam.
    apply (compose (ru^{E}_{X2}) ψ12).
  }
  10 : {
    apply (compose (C:=E) ψ12).
    apply (compose (C:=E) l1').
    apply (# K).
    exact (lu^{C}_{R1}).
  }
  10 : {
    apply internal_lam.
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (l1 ⊗^{E} _) _).
    apply (compose (C:=E) ψ12).
    apply (compose (C:=E) l1').
    apply (# K (ru^{C}_{R1})).
    exact (pr1 k R1 _).
  }
  rewrite internal_lam_precomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  simpl.
  refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E).
  rewrite 2 assoc'.
  rewrite <- (monoidal_rightunitornat E).
  apply maponpaths.
  rewrite 2 assoc.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (pr1 (pr222 k) R1)).
  apply pathsinv0.
  apply (sym_mon_braiding_lunitor E). (* completes subgoal *)
  rewrite internal_lam_precomp.
  do 2 refine (assoc _ _ _ @ _).
  refine ( maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  simpl.
  refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
  apply maponpaths.
  rewrite id_right.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E _ _ _ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite (bifunctor_equalwhiskers E).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply (sym_mon_braiding_lunitor C). (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  simpl.
  exact (! functor_comp _ _ _ ).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) eqpsi).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  apply (monoidal_leftunitornat C). (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine ( maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (bifunctor_leftcomp E).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (bifunctor_rightcomp E).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc'.
  apply maponpaths.
  rewrite eqphi.
  rewrite (bifunctor_rightcomp E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  generalize (pr122 k I_{C} _ _ f12); simpl; rewrite 2 id_right; intros keq.
  refine (! maponpaths (compose _) keq @ _); clear keq.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite assoc'.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  rewrite assoc.
  refine (_ @ maponpaths (λ f, f · _) eqpsi).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  apply (monoidal_rightunitornat C). (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply monoidal_rightunitornat. (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  apply maponpaths.
  exact (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  simpl.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc.
  refine (_ @ assoc' _ _ _).
  rewrite (bifunctor_leftcomp E).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  do 2 rewrite assoc'.
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E). (* completes subgoal *)
  exact (double_glued_luiso _ k).
Qed.


Lemma double_glued_disp_rightunitor_law {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  disp_rightunitor_law (disp_monoidal_rightunitor (double_glued_monoidal_data dpbs k))
    (disp_monoidal_rightunitorinv (double_glued_monoidal_data dpbs k)).
Proof.
  split.
  intros R1 R2 f12.
  intros ((U1, l1), (X1, l1')).
  intros ((U2, l2), (X2, l2')).
  intros ((ϕ12, eqphi), (ψ12, eqpsi)).
  revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  use dirprod_paths;
    use subtypePath.
  intros x.
  apply (homset_property E).
  unfold transportb, transportf.
  induction (! pr1 (monoidal_rightunitorlaw C) R1 R2 f12).
  exact (monoidal_rightunitornat E _ _ _).
  intros x.
  apply (homset_property E).
  unfold transportb, transportf.
  induction (! pr1 (monoidal_rightunitorlaw C) R1 R2 f12).
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  10 : {
    apply internal_lam.
    apply (compose ((compose (C:=E) l2' (# K ru^{C}_{_})) ⊗^{E} (l1 · # L f12))).
    apply (compose (sym_mon_braiding E _ _)).
    apply (pr1 k).
  }
  10 : {
    apply (compose (C:=E) l2').
    apply (# K).
    apply (compose (ru^{C}_{R1})).
    exact f12.
  }
  10 : {
    apply internal_lam.
    apply (compose (ru^{E}_{_})).
    exact ψ12.
  }
  refine (maponpaths (compose _) (internal_postcomp_id U1 _) @ _).
  rewrite id_right.
  rewrite internal_lam_precomp.
  rewrite internal_lam_natural.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply maponpaths.
  repeat rewrite assoc.
  refine (maponpaths (λ f, f · _) (tensor_sym_mon_braiding E _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (tensor_sym_mon_braiding E _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite <- (monoidal_rightunitornat C).
  rewrite (functor_comp K).
  refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  generalize (pr122 k I_{C} _ _ f12); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (compose _) keq); clear keq.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  apply (bifunctor_equalwhiskers E). (* completes subgoal *)
  simpl.
  rewrite internal_lam_precomp.
  rewrite assoc.
  rewrite internal_lam_natural.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (_ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  refine (_ @ functor_comp (pr1 (pr2 E I_{ E})) _ _).
  apply maponpaths.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (functor_comp K _ _) @ _).
  rewrite (assoc (C:=C)).
  rewrite (sym_mon_braiding_runitor C).
  rewrite (functor_comp K).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (tensor_sym_mon_braiding E _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose _) (pr1 (pr222 k) R1) @ _).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) eqpsi).
  rewrite assoc'.
  rewrite (sym_mon_braiding_lunitor E).
  apply (monoidal_rightunitornat E). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite internal_lam_precomp.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  rewrite internal_lam_precomp.
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite <- eqphi.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (! bifunctor_leftcomp E _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply (monoidal_rightunitornat C). (* completes subgoal *)  
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  exact (! functor_comp (pr1 (pr2 E I_{ E})) _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite internal_lam_precomp.
  rewrite 3 assoc.
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  simpl.
  refine (_ @ assoc _ _ _).
  rewrite (bifunctor_leftcomp E (K (R2 ⊗_{ C} I_{ C}))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k I_{C} _ _ f12); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (compose _) keq).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_rightcomp E U1 _ _ _ _ _).
  apply maponpaths.
  refine (! maponpaths (λ f, f · _) eqpsi @ _).
  refine (assoc' (C:=E) _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_rightunitornat C). (*completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) eqpsi @ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  apply maponpaths.
  exact (! functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply (monoidal_rightunitornat E). (*completes subgoal *)
  intros R1 ((U1, l1), (X1, l1')).
  split; apply double_glued_mor_eq; split;
    unfold transportb, transportf;
    induction (! (pr2 (pr2 (monoidal_rightunitorlaw C) R1))); simpl.
  exact (pr2 (monoidal_rightunitorisolaw E U1)).
  refine (assoc (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR (C:=E) _ _ _ _ _ _ _) @ _).
  repeat rewrite assoc.
  apply pathsinv0.
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  exact (rightunitors_eval_expand2 X1).
  induction (! pr1 (pr2 (monoidal_rightunitorlaw C) R1)).
  exact (pr1 (monoidal_rightunitorisolaw E U1)).
  induction (! pr1 (pr2 (monoidal_rightunitorlaw C) R1)).
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _); try exact (id_left _).
  exact (doublePullbackSqrLCommutes _).
  exact (doublePullbackSqrRCommutes _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f) · _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, _ · (f · _) · _) (monoidal_rightunitorinvnat _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (λ f, f · _) (doublePullbackSqrRCommutes _) @ _).
  refine (_ @ id_right _).
  refine (_ @ maponpaths (compose _) (internal_postcomp_id _ _)).
  refine (_ @ ! doublePullbackSqrLCommutes _).
  rewrite assoc'.
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  rewrite 2 assoc'.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (internal_lam_precomp _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_lam (f · _) · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_lam (_ · f · _) · _) (id_right _) @ _).
  rewrite <- (bifunctor_leftid E).
  refine (! maponpaths (λ f, _ · internal_lam (_ · (_ · _ ⊗^{E}_{l} f) · _) · _) (functor_id K _) @ _).
  rewrite <- (pr1 (monoidal_leftunitorisolaw C _)).
  rewrite (functor_comp K).
  refine (maponpaths (λ f, _ · internal_lam (_ · (_ · f) · _) · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (_ · f · _) · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (_ · (f · _) · _) · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (_ · f · _) · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (f · _) · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_lam (_ · f) · _) (pr1 (pr222 k) R1) @ _).
  refine (maponpaths (λ f, _ · internal_lam (f · _) · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (_ · f) · _) (sym_mon_braiding_lunitor E _) @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (! maponpaths (λ f, _ · f · _) (internal_lam_natural _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  repeat refine (maponpaths (compose _) (assoc _ _ _) @ _).
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! maponpaths (λ f, _ · (f · _)) (rightunitors_eval_expand2 (K R1)) @ _).
  rewrite id_left.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  refine (_ @ functor_id K _).
  apply maponpaths.
  rewrite (sym_mon_braiding_linvunitor C).
  exact (pr1 (monoidal_rightunitorisolaw C R1)).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f) · _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) · _) (monoidal_rightunitorinvnat E _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (λ f, f · _) (doublePullbackSqrRCommutes _) @ _).
  rewrite assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  simpl.
  refine (maponpaths (λ f, _ · f · _) (internal_lam_precomp _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_lam (f · _) · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_lam (_ · f · _) · _) (id_right _) @ _).
  rewrite <- (bifunctor_leftid E).
  refine (! maponpaths (λ f, _ · internal_lam (_ · (_ · _ ⊗^{E}_{l} f) · _) · _) (functor_id K _) @ _).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr1 (monoidal_leftunitorisolaw C _)).
  rewrite (functor_comp K).
  refine (maponpaths (λ f, _ · internal_lam (_ · (_ · f) · _) · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (_ · f · _) · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (_ · (f · _) · _) · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (_ · f · _) · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (f · _) · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_lam (_ · f) · _) (pr1 (pr222 k) R1) @ _).
  refine (maponpaths (λ f, _ · internal_lam (f · _) · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (_ · f) · _) (sym_mon_braiding_lunitor E _) @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (! maponpaths (λ f, _ · f · _) (internal_lam_natural _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc'.
  repeat refine (maponpaths (compose _) (assoc _ _ _) @ _).
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! maponpaths (λ f, _ · (f · _)) (rightunitors_eval_expand2 (K R1)) @ _).
  rewrite id_left.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  refine (_ @ functor_id K _).
  apply maponpaths.
  rewrite (sym_mon_braiding_linvunitor C).
  exact (pr1 (monoidal_rightunitorisolaw C R1)).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ id_right _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  exact (rightunitors_eval_expand1 X1).
Qed.
