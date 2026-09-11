(************************************

In this file the remaining monoidal laws are proven, namely:

- pentagon identity

Then all laws are bundled as a disp_monoidal_laws structure. 

for proofs of the other laws, see file monoidal_laws1.v

************************************)
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
Require Import double_gluing.monoidal.unitor_laws.
Require Import double_gluing.monoidal.monoidal_laws1.


Definition double_glued_disp_pentagon_identity_compArrowL {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP := tensor_doublePullback dpbs k
              (((pr11 dr1 ⊗_{ E} pr11 dr2) ⊗_{ E} pr11 dr3,,
                (pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2) ⊗^{ E} pr21 dr3
                · (pr112 (pr1 L)) (R1 ⊗_{ C} R2) R3),,
               pr11 (tensor_doublePullback dpbs k
                       ((pr11 dr1 ⊗_{ E} pr11 dr2,,
                         pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                        pr11 (tensor_doublePullback dpbs k dr1 dr2),,
                        doublePullbackPrM
                          (tensor_doublePullback dpbs k dr1 dr2)) dr3),,
               doublePullbackPrM
                 (tensor_doublePullback dpbs k
                    ((pr11 dr1 ⊗_{ E} pr11 dr2,,
                      pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 (tensor_doublePullback dpbs k dr1 dr2),,
                     doublePullbackPrM
                       (tensor_doublePullback dpbs k dr1 dr2)) dr3)) dr4)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4)))) :
  doublePullback_CompetitorArrowL dP X.
Proof.
    apply (compose (doublePullbackPrL _)).
    refine (compose _ (internal_precomp (α^{E}_{_,_,_}) _)).
    refine (compose _ (internal_uncurry _ _ _)).
    apply internal_postcomp.
    apply (compose (doublePullbackPrL _)).
    refine (compose _ (internal_uncurry _ _ _)).
    apply internal_postcomp.
    apply (doublePullbackPrL _).
Defined.

Definition double_glued_disp_pentagon_identity_compArrowM  {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP := tensor_doublePullback dpbs k
              (((pr11 dr1 ⊗_{ E} pr11 dr2) ⊗_{ E} pr11 dr3,,
                (pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2) ⊗^{ E} pr21 dr3
                · (pr112 (pr1 L)) (R1 ⊗_{ C} R2) R3),,
               pr11 (tensor_doublePullback dpbs k
                       ((pr11 dr1 ⊗_{ E} pr11 dr2,,
                         pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                        pr11 (tensor_doublePullback dpbs k dr1 dr2),,
                        doublePullbackPrM
                          (tensor_doublePullback dpbs k dr1 dr2)) dr3),,
               doublePullbackPrM
                 (tensor_doublePullback dpbs k
                    ((pr11 dr1 ⊗_{ E} pr11 dr2,,
                      pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 (tensor_doublePullback dpbs k dr1 dr2),,
                     doublePullbackPrM
                       (tensor_doublePullback dpbs k dr1 dr2)) dr3)) dr4)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4)))) :
  doublePullback_CompetitorArrowM dP X.
Proof.
    apply (compose (doublePullbackPrM _)).
    apply (# K).
    apply (α^{C}_{_,_,_} · α^{C}_{_,_,_}).
Defined.

Definition double_glued_disp_pentagon_identity_compArrowRL  {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4)))) :
  doublePullback_CompetitorArrowL dP123 (X ⊗_{E} pr11 dr4).
Proof.
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (doublePullbackPrL _ )).
    refine (compose (internal_postcomp _  _) _).
    apply (compose (doublePullbackPrL _ )).
    apply (compose (internal_postcomp _ (doublePullbackPrR _))).
    apply internal_swap_arg.
    apply internal_swap_arg.
    apply (compose (internal_eval _ _)).
    apply internal_uncurry.
Defined.

Definition double_glued_disp_pentagon_identity_compArrowRM  {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4)))) :
  doublePullback_CompetitorArrowM dP123 (X ⊗_{E} pr11 dr4).
Proof.
    refine (compose (_ ⊗^{E} (pr21 dr4)) _).
    apply (compose (doublePullbackPrM _ )).
    refine (# K _).
    refine (compose _ (α^{C}_{_,_,_} · α^{C}_{_,_,_})).
    apply (sym_mon_braiding C _ _).
    apply (compose (sym_mon_braiding E _ _)).
    apply (pr1 k).
Defined.

Definition double_glued_disp_pentagon_identity_compArrowRRL  {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4)))) :
  doublePullback_CompetitorArrowL dP12 ((X ⊗_{E} pr11 dr4) ⊗_{E} pr11 dr3).
Proof.
    refine (compose (_ ⊗^{E}_{r} _) _).
    refine (compose (_ ⊗^{E}_{r} _) _).
    refine (compose (doublePullbackPrL _ ) _).
    apply (compose (internal_postcomp _ (doublePullbackPrR _ · internal_precomp (sym_mon_braiding E _ _) _ · internal_curry _ _ _))).
    apply (internal_swap_arg _ _ _ ).
    apply (internal_eval _ _ · internal_swap_arg _ _ _).
    apply (internal_eval _ _).
Defined.

Definition double_glued_disp_pentagon_identity_compArrowRRM  {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4)))) :
  doublePullback_CompetitorArrowM dP12 ((X ⊗_{E} pr11 dr4) ⊗_{E} pr11 dr3).
Proof.
    apply (compose (((doublePullbackPrM _) ⊗^{E}_{r} _ ) ⊗^{E}_{r} _ )).
    apply (compose (α^{E}_{_,_,_} · _ ⊗^{E}_{l} (sym_mon_braiding E _ _) · sym_mon_braiding E _ _)).
    apply (compose ((((pr21 dr3) ⊗^{E} (pr21 dr4)) · fmonoidal_preservestensordata L _ _) ⊗^{E} (# K (sym_mon_braiding C _ _ · α^{C}_{_,_,_})))).
    apply (pr1 k).
Defined.

Definition double_glued_disp_pentagon_identity_compArrowRRR  {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4)))) :
  doublePullback_CompetitorArrowR dP12 ((X ⊗_{E} pr11 dr4) ⊗_{E} pr11 dr3).
Proof.
    refine (compose (_ ⊗^{E}_{r} _) _).
    refine (compose (_ ⊗^{E}_{r} _) _).
    refine (compose (doublePullbackPrR _ ) _).
    apply (compose (internal_precomp (sym_mon_braiding E _ _ · α^{E}_{_,_,_}) _)).
    apply internal_curry.
    apply (compose (internal_eval _ _)).
    apply (compose (internal_precomp (sym_mon_braiding E _ _) _)).
    apply internal_curry.
    apply (internal_eval _ _).
Defined.

Lemma double_glued_disp_pentagon_identity_compArrowRRSqrL  {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2) :
  doublePullback_CompetitorSqrL dP12 ((_ ⊗_{E} pr11 dr4) ⊗_{E} pr11 dr3)
    (double_glued_disp_pentagon_identity_compArrowRRL dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowRRM dpbs k dr1 dr2 dr3 dr4).
Proof.
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply (bifunctor_rightcomp E _).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  apply assoc'.
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (internal_eval_nat _ _ _ _ @ _).
  now rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (internal_eval_nat _ _ _ _ @ _).
  now rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! internal_postcomp_comp _ _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (! curry_nat3 _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  apply assoc'.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! internal_postcomp_comp _ _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (doublePullbackSqrRCommutes _).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply (doublePullbackSqrLCommutes _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.  
  simpl.
  refine (assoc _ _ _ @ assoc _ _ _ @ _ @ internal_lam_tensor_eval _ @ _).
  apply cancel_postcomposition.
  refine (_ @ maponpaths _ _).
  refine (_ @ ! bifunctor_rightcomp E _ _ _ _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_rightcomp E).
  refine (assoc _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (internal_eval_nat _ _ _ _ @ _).
  now rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ internal_lam_tensor_eval _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths compose _ _ @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (_ @ internal_lam_postcomp _ _).
  apply cancel_postcomposition.
  apply internal_lam_precomp.
  apply pathsinv0.
  apply (bifunctor_rightcomp E).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ internal_lam_postcomp _ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ ).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply internal_lam_postcomp.
  apply internal_lam_natural.
  unfold monoidal_cat_tensor_mor;
    rewrite 2 (when_bifunctor_becomes_rightwhiskering E);
    rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply internal_lam_natural.
  apply internal_lam_natural.
  unfold monoidal_cat_tensor_mor;
    rewrite 3 (when_bifunctor_becomes_rightwhiskering E);
    rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor;
    rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  2 : {
    apply maponpaths.
    apply pathsinv0.
    apply internal_lam_precomp.
  }
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_associatornatright E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply (monoidal_associatorinvnatright E).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply internal_lam_tensor_eval.
  refine (maponpaths (compose _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_associatornatright E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply (monoidal_associatorinvnatright E).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply internal_lam_tensor_eval.
  refine (maponpaths (compose _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ internal_lam_curry _).
  apply cancel_postcomposition.
  refine (_ @ internal_lam_precomp _ _).
  apply cancel_postcomposition.
  do 2 refine (assoc _ _ _ @ _).
  apply internal_lam_natural.
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply internal_lam_tensor_eval.
  apply internal_lam_natural.
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply internal_lam_tensor_eval.
  unfold monoidal_cat_tensor_pt.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  do 3 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).
  refine (maponpaths (compose _) _ @ _).
  refine (_ @ internal_lam_tensor_eval _).
  apply cancel_postcomposition.
  apply maponpaths.
  refine (internal_lam_natural _ _ @ _).
  unfold monoidal_cat_tensor_mor;
    now rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (pr12 k).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_leftcomp E).
  apply maponpaths.
  apply (natural_contraction_composed k).
  refine (assoc _ _ _ @ _ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
  }
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (bifunctor_equalwhiskers E).
    }
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply (monoidal_braiding_naturality_right E).
    }
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _).
    2 : {
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (bifunctor_leftcomp E).
    }
    apply maponpaths.
    apply pathsinv0.
    apply (natural_contraction_composed k).
  }
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _).
    2 : {
      apply cancel_postcomposition.
      refine (_ @ assoc _ _ _ @ _).
      2 : {
        apply cancel_postcomposition.
        refine (assoc' _ _ _ @ _ @ assoc _ _ _).
        apply maponpaths.
        apply pathsinv0.
        apply (bifunctor_equalwhiskers E).
      }
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
      apply maponpaths.
      apply pathsinv0.
      apply (fsym_respects_braiding L).
    }
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply (natural_contraction_extranatural k).
  }
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_rightcomp E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply (monoidal_associatorinvnatleftright E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply (monoidal_associatorinvnatright E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply (monoidal_associatorinvnatleft E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (_ @ bifunctor_equalwhiskers E _ _ _ _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  apply cancel_postcomposition.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (functor_comp K).
  refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (_ @ assoc' _ _ _ @ _).
    2 : {
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (bifunctor_rightcomp E).
    }
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    do 2 refine (_ @ assoc' _ _ _).
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths.
      apply (monoidal_braiding_naturality_left E).
    }
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply (monoidal_braiding_naturality_right E).
  }
  refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _ @ assoc _ _ _).
  2 : {
    apply maponpaths.
    refine (_ @ assoc' _ _ _ @ _).
    2 : {
      apply maponpaths.
      refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
      2 : {
        apply maponpaths.
        apply pathsinv0.
        apply (bifunctor_equalwhiskers E).
      }
      refine (assoc _ _ _ @ _).
      apply cancel_postcomposition.
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
      apply maponpaths.
      apply (functor_comp K).
    }
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (_ @ assoc _ _ _ @ _).
    2 : {
      apply cancel_postcomposition.
      refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
      2 : {
        apply maponpaths.
        apply pathsinv0.
        apply (monoidal_associatorinvnatleftright E).
      }
      refine (assoc _ _ _ @ _).
      apply cancel_postcomposition.
      refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
      2 : {
        apply maponpaths.
        apply pathsinv0.
        apply (monoidal_associatorinvnatright E).
      }
      refine (assoc _ _ _ @ _).
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (monoidal_associatorinvnatleft E).
    }
    apply maponpaths.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths.
      apply pathsinv0.
      apply (bifunctor_equalwhiskers E).
    }
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths.
      apply pathsinv0.
      apply (bifunctor_equalwhiskers E).
    }
    apply cancel_postcomposition.
    refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
    apply maponpaths.
    apply (functor_comp K).
  }
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  2 : {
    apply maponpaths.
    apply (bifunctor_rightcomp E).
  }
  apply map_on_two_paths.
  2 : {
    do 2 apply maponpaths.
    refine (_ @ assoc' _ _ _).
    apply sym_mon_tensor_lassociator1.
  }
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (_ @ monoidal_braiding_naturality_right E _ _ _ _).
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0.
    apply (bifunctor_leftcomp E).    
  }
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply assoc.
  refine (_ @ maponpaths (λ f, f · _) _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply sym_mon_hexagon_rassociator1.
  do 4 refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (compose _) _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  apply pathsinv0.
  apply sym_mon_hexagon_rassociator1.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  refine (! id_left _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply pathsinv0.
  apply (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply pathsinv0.
  apply sym_mon_tensor_lassociator'.
  unfold monoidal_cat_tensor_mor; 
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ ! bifunctor_leftcomp E _ _ _ _ _ _).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply (bifunctor_rightcomp E).
  refine (! id_left _ @ _).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  rewrite <- (bifunctor_leftid E).
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply (pr1 (monoidal_associatorisolaw E _ _ _)).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  apply monoidal_pentagon_identity_inv.
  refine (_ @ id_left _).
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! monoidal_associatornatleft E _ _ _ _ _).
  do 2 refine (assoc _ _ _ @ _).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ id_left _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightid E _ _).
  refine (_ @ ! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  2 : {
    apply maponpaths.
    apply (sym_mon_braiding_inv E).
  }
  apply cancel_postcomposition.
  refine (_ @ id_left _).
  refine (_ @ maponpaths (λ f, f · _) _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatornatright E).
  apply (monoidal_associatorisolaw E).
Qed.

Lemma double_glued_disp_pentagon_identity_compArrowRRSqrR  {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2) :
  doublePullback_CompetitorSqrR dP12 ((_ ⊗_{E} pr11 dr4) ⊗_{E} pr11 dr3)
    (double_glued_disp_pentagon_identity_compArrowRRM dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowRRR dpbs k dr1 dr2 dr3 dr4).
Proof.
  
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _) @ assoc _ _ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (internal_pre_post_comp_as_pre_post_comp _ _)).
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (! internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, ((f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, ((_ · f) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _)).
  refine (_ @ maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, ((f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, ((_ · f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (internal_pre_post_comp_as_pre_post_comp _ _)).
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (_ @ maponpaths (λ f, ((f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, ((f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (doublePullbackSqrRCommutes _)).
  refine (_ @ maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite 2 internal_lam_precomp.
  rewrite 3 internal_lam_natural.
  refine (_ @ maponpaths (λ f, (f ⊗^{ E}_{r} _ · _) ⊗^{ E}_{r} _  · _) (assoc' _ _ _)).
  rewrite internal_lam_precomp.
  rewrite internal_lam_curry.
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (maponpaths (λ f, f · _) (! internal_lam_tensor_eval _) @ assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  rewrite internal_lam_precomp.
  rewrite internal_lam_curry.
  refine (_ @ ! internal_lam_tensor_eval _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt; rewrite 3 (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (! pr12 k _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_rightid E _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (! pr1 (monoidal_braiding_inverses E _ _)) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  do 2 refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (! pr2 (pr222 k) (R3 ⊗_{C} R4) R2 R1) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_leftid E _ _) @ _).
  refine (maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (! functor_id K _) @ _).
  refine (maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (! bifunctor_rightid C _ _) @ _).
  refine (maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K (f ⊗^{C}_{r} _) · _)) (! pr2 (monoidal_braiding_inverses C _ _)) @ _).
  refine (maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (bifunctor_rightcomp C _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  generalize (pr122 k R1 _ _ (sym_mon_braiding C (R3 ⊗_{ C} R4) R2)); simpl; rewrite 2 id_right; intros keq.
  refine (maponpaths (compose _) keq @ _); clear keq.
  do 6 refine (_ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  do 5 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · (f · _)) ⊗^{E}_{r} _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc _ _ _ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _) (assoc' _ _ _) @ _).
  rewrite <- (fsym_respects_braiding L).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) ⊗^{E}_{r} _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _) @ assoc _ _ _ @ _).
  refine (_ @ maponpaths (λ f, _ · f ⊗^{E}_{r} _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  apply (maponpaths (postcompose _)).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  do 5 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f) ⊗^{E}_{r} _ · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply map_on_two_paths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _)) (pr1 (monoidal_braiding_inverses E _ _)) @ _).
  refine (maponpaths (compose _) (bifunctor_rightid E _ _) @ _).
  refine (id_right _ @ _).
  refine (maponpaths (λ f, f · _ · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _ @ maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _))).
  refine (_ @ assoc _ _ _).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (assoc' _ _ _)).
  set (U1 := pr11 dr1); set (U2 := pr11 dr2); set (U3 := pr11 dr3); set (U4 := pr11 dr4).
  assert (α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))), U4, U2 ⊗_{ E} U3}
     · K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗^{ E}_{l} sym_mon_braiding E U4 (U2 ⊗_{ E} U3)
     · sym_mon_braiding E (K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4)))) ((U2 ⊗_{ E} U3) ⊗_{E} U4) =
       sym_mon_braiding E _ _ · _ ⊗^{E}_{l} sym_mon_braiding E _ _ · αinv^{E}_{_,_,_}) as hexeq.
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _ @ ! sym_mon_hexagon_rassociator E _ _ _)) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ id_right _ @ _).
  refine (assoc _ _ _ @ _ @ id_left _).
  apply (maponpaths (postcompose _)).
  apply (monoidal_associatorisolaw E).
  refine (_ @ maponpaths (λ f, _ · f · _) (! hexeq)); clear hexeq.
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _) @ assoc _ _ _).
  assert (αinv^{ E }_{ U2 ⊗_{ E} U3, U4, K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4)))} ·
                 α^{ E }_{ U2, U3, U4} ⊗^{ E}_{r} K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) =
            α^{E}_{_,_,_} · _ ⊗^{E}_{l} αinv^{E}_{_,_,_} · αinv^{E}_{_,_,_}) as penteq.
  refine (_ @ id_right _).
  refine (_ @ maponpaths (compose _) (bifunctor_rightid E _ _)).
  refine (_ @ maponpaths (λ f, _ · f ⊗^{E}_{r} _) (pr2 (monoidal_associatorisolaw E _ _ _))).
  refine (_ @ maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (! monoidal_pentagon_identity_inv E _ _ _ _)).
  refine (! id_left _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (monoidal_associatorisolaw E).
  refine (_ @ maponpaths (compose _) (! penteq)); clear penteq.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  assert (α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗_{ E} U4, U3, U2}
              · (K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗_{ E} U4) ⊗^{ E}_{l} sym_mon_braiding E U3 U2
              · sym_mon_braiding E ((K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4)))) ⊗_{E} U4) (U2 ⊗_{ E} U3)
          = sym_mon_braiding E _ _ ⊗^{E}_{r} _ · sym_mon_braiding E _ _ · αinv^{E}_{_,_,_}) as hexeq.
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator E _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (assoc _ _ _ @ _ @ monoidal_braiding_naturality_right E _ _ _ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  refine (maponpaths (λ f, _ · f · _) (! sym_mon_hexagon_rassociator E _ _ _) @ _).
  refine (assoc' _ _ _ @ maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ id_right _ @ _).
  refine (assoc _ _ _ @ _ @ id_left _).
  apply cancel_postcomposition.
  apply (monoidal_associatorisolaw E).
  refine (_ @ maponpaths (λ f, f · _) (! hexeq)); clear hexeq.
  assert ((α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))), U4, U3} · _ ⊗^{ E}_{l} sym_mon_braiding E U4 _ · sym_mon_braiding E _ (U3 ⊗_{E} U4)) =
            sym_mon_braiding E _ _ · _ ⊗^{E}_{l} sym_mon_braiding E _ _ · αinv^{E}_{_,_,_}) as hexeq.
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  refine (maponpaths (λ f, _ · f · _) (! sym_mon_hexagon_rassociator E _ _ _) @ _).
  refine (assoc' _ _ _ @ maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ id_right _ @ _).
  refine (assoc _ _ _ @ _ @ id_left _).
  apply cancel_postcomposition.
  apply (monoidal_associatorisolaw E).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} U2 · _) hexeq @ _); clear hexeq.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _ · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  do 2 refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (compose _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  do 3 refine (_ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_associatornatleft E _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (! pr2 (monoidal_associatorisolaw E _ _ _))).
  rewrite id_left.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E). (* completes subgoal *)
  apply maponpaths.
  refine (maponpaths (λ f, compose (C:=E) f _ · _) (! functor_comp K _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  do 2 refine (assoc _ _ _ @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering C).
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (sym_mon_tensor_lassociator' C _ _ _ @ _) @ _).
  unfold monoidal_cat_tensor_mor;
    now rewrite (when_bifunctor_becomes_leftwhiskering C).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (pr2 (monoidal_associatorisolaw C _ _ _)) @ _).
  apply id_left.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp C _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{C}_{l} f) (pr2 (monoidal_braiding_inverses C _ _)) @ _).
  apply (bifunctor_leftid C).
  apply id_left.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  apply sym_mon_braiding_tensor_associator.
  refine (assoc _ _ _ @ _ @ id_left _).
  apply (maponpaths (postcompose _)).
  refine (_ @ pr1 (monoidal_associatorisolaw C _ _ _)).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  apply (monoidal_braiding_inverses C).
Qed.

Definition double_glued_disp_pentagon_identity_compArrowRR {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4)))) :
  doublePullback_CompetitorArrowR dP123 (X ⊗_{E} pr11 dr4).
Proof.
    apply internal_lam.
    use doublePullbackArrow.
    apply double_glued_disp_pentagon_identity_compArrowRRL.
    apply double_glued_disp_pentagon_identity_compArrowRRM.
    apply double_glued_disp_pentagon_identity_compArrowRRR.
    apply double_glued_disp_pentagon_identity_compArrowRRSqrL.
    apply double_glued_disp_pentagon_identity_compArrowRRSqrR.
Defined.

Lemma double_glued_disp_pentagon_identity_compArrowRSqrL {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3) :
  doublePullback_CompetitorSqrL dP123 (_ ⊗_{E} pr11 dr4)
    (double_glued_disp_pentagon_identity_compArrowRL dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowRM dpbs k dr1 dr2 dr3 dr4).
Proof.
  
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (uncurry_nat3 _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ assoc' _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (! internal_postcomp_comp _ _ _ @ _).
  refine (maponpaths (internal_postcomp _) _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (! internal_postcomp_comp _ _ _ @ _).
  refine (maponpaths (internal_postcomp _) _).
  exact (! doublePullbackSqrRCommutes _).
  refine (maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _) @ _).
  apply assoc'.
  apply assoc'.
  apply (internal_postcomp_comp _ _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _) @ _).
  apply assoc'.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ assoc' _ _ _ @ _).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  simpl. (*necessary*)
  rewrite 4 internal_lam_precomp.
  rewrite 2 internal_lam_postcomp.
  repeat rewrite internal_lam_natural.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) _ @ _).
  refine (maponpaths (λ f, internal_lam (_ · f) · _) (internal_lam_lam_swap _) @ _).
  repeat rewrite internal_lam_natural.
  exact (internal_lam_lam_swap _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_tensor_eval _) @ _).
  rewrite internal_lam_natural.
  refine (internal_lam_uncurry _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt; repeat rewrite (when_bifunctor_becomes_rightwhiskering E).
  do 2 refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (id_left _)).
  refine (_ @ maponpaths (λ f,  _ · (f · _)) (pr2 (monoidal_associatorisolaw E _ _ _))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  refine (_ @ maponpaths (λ f,  _ · (f · _)) (bifunctor_rightid E _ _)).
  refine (_ @ maponpaths (λ f,  _ · (f ⊗^{E}_{r} _ · _)) (pr1 (monoidal_braiding_inverses E _ _))).
  refine (_ @ maponpaths (λ f,  _ · (f · _)) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  do 2 refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (pr2 (pr222 k) R4 (R1 ⊗_{ C} R2) R3)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · ((f ⊗^{ E}_{r} _) ⊗^{ E}_{r} _ · _)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{ E}_{r} _ · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · (_ · (f · _))) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply assoc'.
  apply assoc.
  apply (bifunctor_rightcomp E _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! pr12 k _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{ E}_{l} f) (! pr12 k _ _ _ _) @ _).
  apply (bifunctor_leftcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_rightid E _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (! pr1 (monoidal_braiding_inverses E _ _)) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  do 2 refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (! pr2 (pr222 k) _ _ _) @ _).
  apply assoc.
  apply (bifunctor_rightcomp E _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_rightid E _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (! pr1 (monoidal_braiding_inverses E _ _)) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  do 2 refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (! pr2 (pr222 k) _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftid E _ _ @ _) @ _).
  refine (maponpaths (λ f, _⊗^{ E}_{l} f) (! functor_id K _ @ _) @ _).
  refine (maponpaths (# K) (! bifunctor_rightid C _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ C}_{r} _) (! pr2 (monoidal_braiding_inverses C _ _)) @ _).
  apply (bifunctor_rightcomp C).
  apply (functor_comp K).
  apply (bifunctor_leftcomp E).
  refine (assoc' _ _ _ @ _).
  generalize (pr122 k R3 _ _ (sym_mon_braiding C (R1 ⊗_{ C} R2) R4)); simpl; rewrite 2 id_right; intros keq.
  refine (maponpaths (compose _) keq @ _).
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  unfold monoidal_cat_tensor_pt; simpl.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{ E}_{r} _ · _)) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  refine (assoc _ _ _).
  apply assoc.
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply assoc'.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  refine (assoc _ _ _ @ _).
  do 5 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
    2: {
      refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (monoidal_braiding_naturality_right E _ _ _ _)).
      apply pathsinv0.
      apply (bifunctor_rightcomp E).
    }
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
      2: {
        refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
        refine (_ @ assoc _ _ _).
        refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatorinvnatleft E _ _ _ _ _)).
          refine (_ @ assoc _ _ _).
          refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
          2 : {
            refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
            refine (_ @ assoc _ _ _).
            refine (maponpaths (compose _) (_ @ assoc' _ _ _)).
            refine (_ @ maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
            apply (bifunctor_equalwhiskers E).             
          }
          apply assoc'.
        }
        apply assoc'.
      }
      apply assoc'.
    }
    apply assoc'.
  }
  do 2 refine (_ @ assoc' _ _ _).
  apply map_on_two_paths.
  do 5 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  rewrite <- (fsym_respects_braiding L).
  apply (bifunctor_rightcomp E).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  do 4 refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (! monoidal_associatorinvnatright E _ _ _ _ _)).
    apply assoc'.
  }
  refine (_ @ assoc' _ _ _).
  do 9 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) _ @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (assoc _ _ _ @ _)).
  apply tensor_sym_mon_braiding.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  apply assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, _ ⊗^{ E}_{l} f) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  do 5 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  apply assoc.
  apply assoc.
  refine (assoc _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (monoidal_braiding_naturality_left E _ _ _ _)).
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ assoc _ _ _ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
    refine (_ @ maponpaths (compose _) (! monoidal_associatorinvnatleftright E _ _ _ _ _)).
    apply assoc'.
  }
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  apply sym_mon_hexagon_rassociator1.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  do 4 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (! sym_mon_hexagon_rassociator0 E _ _ _) @ _).
  refine (_ @ id_right _).
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr1 (monoidal_braiding_inverses E _ _)).
  refine (_ @ ! bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ id_left _).
  apply cancel_postcomposition.
  apply (monoidal_associatorisolaw E).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  rewrite 2 (bifunctor_rightcomp E _).
  now rewrite 2 assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f · _ ) (! sym_mon_hexagon_rassociator1 E _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightid E _ _).
  apply maponpaths.
  apply (monoidal_braiding_inverses E).
  reflexivity.
  refine (_ @ ! sym_mon_tensor_lassociator E _ _ _).
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering E), (when_bifunctor_becomes_leftwhiskering E).
  repeat rewrite assoc'.
  do 2 apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (sym_mon_hexagon_rassociator0 E _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! id_right _ @ _).
  2 : {
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_associatorisolaw E).
  }
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (monoidal_pentagon_identity_inv E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  apply (monoidal_associatorisolaw E). (* completes subgoal *)
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths compose (! functor_comp K _ _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (maponpaths (compose _) (monoidal_associatornatleft C _ _ _ _ _) @ _).
  repeat rewrite assoc.
  apply cancel_postcomposition.
  rewrite <- (when_bifunctor_becomes_rightwhiskering C), <- (when_bifunctor_becomes_leftwhiskering C).
  apply pathsinv0.
  apply (sym_mon_hexagon_lassociator C).
Qed.

Lemma double_glued_disp_pentagon_identity_compArrowRSqrR {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3) :
  doublePullback_CompetitorSqrR dP123 (_ ⊗_{E} pr11 dr4)
    (double_glued_disp_pentagon_identity_compArrowRM dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowRR dpbs k dr1 dr2 dr3 dr4).
Proof.

  refine (_ @ ! internal_lam_postcomp _ _).
  refine (_ @ maponpaths internal_lam (! doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) (assoc' _ _ _ @ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! pr12 k _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply assoc'.
  apply assoc.
  refine (assoc _ _ _ @ _).
  unfold monoidal_cat_tensor_pt.
  refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
      exact (assoc _ _ _).
    }
    apply assoc'.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ maponpaths (compose _) (_ @ id_left _)).
    2 : {
      rewrite <- (bifunctor_leftid E).
      refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f · _) (_ @ functor_id K _)).
      2 : {
        refine (_ @ maponpaths (# K) (_ @ bifunctor_rightid C _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, f ⊗^{C}_{r} _) (pr2 (monoidal_braiding_inverses C _ _ ))).
          apply pathsinv0.
          apply (bifunctor_rightcomp C).
        }
        apply pathsinv0.
        apply (functor_comp K).
      }
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      generalize (pr122 k (R1 ⊗_{ C} R2) _ _ (sym_mon_braiding C R3 R4)); simpl; rewrite 2 id_right; intros keq.
      refine (_ @ maponpaths (compose _) (! keq)).
      apply assoc'.
    }
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
      2 : {
        rewrite <- (fsym_respects_braiding L).
        apply pathsinv0.
        apply (bifunctor_rightcomp E).
      }
      apply assoc'.
    }
    apply assoc.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ id_left _)).
  2 : {
    rewrite <- (bifunctor_leftid E).
    refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f · _) (_ @ functor_id K _)).
    2 : {
      refine (_ @ maponpaths (# K) (pr1 (monoidal_associatorisolaw C _ _ _))).
      apply pathsinv0.
      apply (functor_comp K).
    }
    refine (_ @ maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
    apply assoc.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    apply pathsinv0.
    refine ((pr2 (pr222 k) R4 R3 (R1 ⊗_{ C} R2)) @ _).
    unfold postcompose.
    apply idpath.
  }
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
    2 : {
      refine (_ @ maponpaths (compose _) (! monoidal_braiding_naturality_left E _ _ _ _)).
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
      2 : {
        refine (_ @ maponpaths (compose _) (_ @ bifunctor_leftcomp E _ _ _ _ _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, _ ⊗^{ E}_{l} f) (tensor_sym_mon_braiding E _ _)).
          apply pathsinv0.
          apply (bifunctor_leftcomp E).
        }
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) _).
        2 : {
          refine (_ @ ! maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
          refine (_ @ assoc' _ _ _).
          refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatornatleftright E _ _ _ _ _)).
          refine (_ @ assoc _ _ _).
          refine (_ @ maponpaths (compose _) (! monoidal_associatornatleft E _ _ _ _ _)).
          apply assoc'.
        }
        apply assoc.
      }
      apply assoc.
    }
    apply assoc.
  }
  refine (_ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  apply maponpaths.
  do 2 refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
  2 : {
    refine (_ @ maponpaths (compose _) (assoc _ _ _)).
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
    2 : {
      refine (_ @ maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (! monoidal_braiding_naturality_right E _ _ _ _)).
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
      2 : {
        refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatornatright E _ _ _ _ _)).
        apply assoc.
      }
      apply assoc.
    }
    apply assoc.
  }
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply map_on_two_paths.
  do 2 apply maponpaths.
  refine (_ @ maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  do 2 refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right C _ _ _ _)).
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator0 C _ _ _) @ _).
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt;
    rewrite (when_bifunctor_becomes_leftwhiskering C).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ maponpaths (compose _) (! sym_mon_tensor_rassociator C _ _ _)).
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt;
    rewrite (when_bifunctor_becomes_leftwhiskering C).
  refine (! id_left _ @ _).
  repeat rewrite assoc.
  repeat apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_associatorisolaw C). (* completes subgoal *)
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
  2 : {
    refine (_ @ maponpaths (compose _) (! monoidal_braiding_naturality_left E _ _ _ _)).
    refine (_ @ assoc' _ _ _).
    refine (maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
    refine (_ @ maponpaths (compose _) (_ @ bifunctor_leftcomp E _ _ _ _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, _ ⊗^{ E}_{l} f) (! pr1 (monoidal_braiding_inverses E _ _))).
      apply pathsinv0.
      apply (bifunctor_leftid E).
    }
    apply pathsinv0.
    apply id_right.
  }
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ maponpaths (compose _) (_ @ ! sym_mon_tensor_lassociator E _ _ _)).
    2 : {
      unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt;
      rewrite (when_bifunctor_becomes_rightwhiskering E).
      do 2 refine (_ @ assoc _ _ _).
      apply assoc.
    }
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (! pr1 (monoidal_associatorisolaw E _ _ _))).
    apply pathsinv0.
    apply id_left.
  }
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
  2 : {
    refine (_ @ maponpaths (compose _) (assoc _ _ _ @ sym_mon_hexagon_rassociator E _ _ _)).
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (! pr1 (monoidal_associatorisolaw E _ _ _))).
    apply pathsinv0.
    apply id_left.
  }
  refine (! id_right _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorisolaw E).
Qed.

Definition double_glued_disp_pentagon_identity_compArrowR {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3)
  (dP := tensor_doublePullback dpbs k
              (((pr11 dr1 ⊗_{ E} pr11 dr2) ⊗_{ E} pr11 dr3,,
                (pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2) ⊗^{ E} pr21 dr3
                · (pr112 (pr1 L)) (R1 ⊗_{ C} R2) R3),,
               pr11 dP123,,
               doublePullbackPrM dP123) dr4)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4)))) :
  doublePullback_CompetitorArrowR dP X.
Proof.
  apply internal_lam.
  use doublePullbackArrow.
  apply double_glued_disp_pentagon_identity_compArrowRL.
  apply double_glued_disp_pentagon_identity_compArrowRM.
  apply double_glued_disp_pentagon_identity_compArrowRR.
  apply double_glued_disp_pentagon_identity_compArrowRSqrL.
  apply double_glued_disp_pentagon_identity_compArrowRSqrR.
Defined.

Lemma double_glued_disp_pentagon_identity_compSqrL {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3)
  (dP := tensor_doublePullback dpbs k
              (((pr11 dr1 ⊗_{ E} pr11 dr2) ⊗_{ E} pr11 dr3,,
                (pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2) ⊗^{ E} pr21 dr3
                · (pr112 (pr1 L)) (R1 ⊗_{ C} R2) R3),,
               pr11 dP123,,
               doublePullbackPrM dP123) dr4) :
  doublePullback_CompetitorSqrL dP _ (double_glued_disp_pentagon_identity_compArrowL dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowM dpbs k dr1 dr2 dr3 dr4).
Proof.
  
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · ((_ · f) · _)) (uncurry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ f · _)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ (_ · f) · _)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ (_ · (_ · f)) · _)) (uncurry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ (_ · f) · _)) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (internal_postcomp _ (_ · (f · _)) · _)) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ (_ · (internal_postcomp _ f · _)) · _)) (doublePullbackSqrLCommutes _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ (_ · (f · _)) · _)) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ (_ · f) · _)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ f · _)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ (f · _) · _)) (doublePullbackSqrLCommutes _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ f · _)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  simpl. (*necessary*)
  rewrite 4 internal_lam_precomp.
  refine (_ @ ! internal_lam_natural _ _).
  refine (assoc _ _ _ @ _).
  rewrite internal_lam_postcomp.
  refine (maponpaths (λ f, internal_lam (_ · f) · _) (assoc _ _ _) @ _).
  rewrite internal_lam_postcomp.
  rewrite internal_lam_natural.
  refine (maponpaths (λ f, internal_lam (_ · f) · _) (internal_lam_uncurry _) @ _).
  rewrite internal_lam_natural.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_uncurry _) @ _).
  refine (internal_lam_precomp _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt; rewrite 3 (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{ E}_{l} f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} (f ⊗^{ E}_{r} _ · _) · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ ⊗^{E}_{l} (f · _) · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f · _) (monoidal_associatornatleftright E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, _ ⊗^{E}_{l} (f · _) · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 5 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f · _) (monoidal_associatornatleft E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, _ ⊗^{E}_{l} f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 3 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · _ ⊗^{ E}_{l} f · _) (! functor_comp K _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ · f) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f) (pr2 (pr222 k) (R1 ⊗_{C} R2) R3 R4)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  unfold postcompose.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_associatornatleftright E _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  do 3 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_associatornatleft E _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · _ ⊗^{E}_{l} f) (! (pr2 (pr222 k) R1 R2 (R3 ⊗_{C} R4)) @ assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f ⊗^{ E}_{r} _ · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (_ @ maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  unfold postcompose.
  apply pathsinv0.
  apply (pathscomp0 (b:= αinv^{E}_{_,_,_} · sym_mon_braiding E _ _ ·
                                _ ⊗^{E}_{l} (sym_mon_braiding E _ _ · sym_mon_braiding E _ _ ⊗^{E}_{r} _ · α^{E}_{_,_,_}))).
  refine (_ @ maponpaths (λ f, _ · _ ⊗^{E}_{l} f) (assoc _ _ _)).
  refine (_ @ ! maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (! sym_mon_tensor_rassociator E _ _ _)).
  do 3 refine (_ @ maponpaths (λ f, _ · f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (monoidal_associatorisolaw E _ _ _))).
  rewrite id_left.
  refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt; rewrite (when_bifunctor_becomes_leftwhiskering E).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (sym_mon_tensor_lassociator E _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_right.
  repeat rewrite assoc'.
  repeat apply maponpaths.
  apply (when_bifunctor_becomes_leftwhiskering E).
  unfold monoidal_cat_tensor_pt.
  repeat refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (! id_left _ @ _).
  rewrite <- (bifunctor_leftid E).
  rewrite <- (pr1 (monoidal_associatorisolaw E _ _ _)).
  rewrite (bifunctor_leftcomp E).
  rewrite assoc'.
  apply maponpaths.
  refine (! id_right _ @ _).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc.
  apply cancel_postcomposition.
  apply (monoidal_pentagon_identity_inv E).
  repeat rewrite assoc'.
  do 2 apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatorinvnatright E _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ monoidal_braiding_naturality_right E _ _ _ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator E _ _ _ @ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  now rewrite 3 assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  apply id_left.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! sym_mon_hexagon_rassociator E _ _ _ @ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _ @ id_left _).
  apply cancel_postcomposition.
  apply (monoidal_associatorisolaw E).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  apply (monoidal_associatorisolaw E).
Qed.

Lemma double_glued_disp_pentagon_identity_compSqrR {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3)
  (dP := tensor_doublePullback dpbs k
              (((pr11 dr1 ⊗_{ E} pr11 dr2) ⊗_{ E} pr11 dr3,,
                (pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2) ⊗^{ E} pr21 dr3
                · (pr112 (pr1 L)) (R1 ⊗_{ C} R2) R3),,
               pr11 dP123,,
               doublePullbackPrM dP123) dr4) :
  doublePullback_CompetitorSqrR dP _ (double_glued_disp_pentagon_identity_compArrowM dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowR dpbs k dr1 dr2 dr3 dr4).
Proof.
  refine (assoc _ _ _ @ _ @ ! internal_lam_postcomp _ _).
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply (maponpaths internal_lam).
  refine (_ @ ! doublePullbackArrow_PrM _ _ _ _ _ _ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  apply cancel_postcomposition.
  apply maponpaths.
  refine (! functor_comp K _ _).
Qed.

Lemma double_glued_disp_pentagon_identity_compTrianLL {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3)
  (dP := tensor_doublePullback dpbs k
              (((pr11 dr1 ⊗_{ E} pr11 dr2) ⊗_{ E} pr11 dr3,,
                (pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2) ⊗^{ E} pr21 dr3
                · (pr112 (pr1 L)) (R1 ⊗_{ C} R2) R3),,
               pr11 dP123,,
               doublePullbackPrM dP123) dr4)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4))))
  (arrL := double_glued_rightwhiskering_comp2 dpbs k
             (double_glued_tensor_product dpbs k
                (double_glued_tensor_product dpbs k dr1 dr2) dr3)
             (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2 dr3)) dr4
             (disp_monoidal_associator
                (double_glued_monoidal_data dpbs k) R1 R2 R3 dr1 dr2 dr3)
             · double_glued_assoc_data_comp2 dpbs k dr1
             (double_glued_tensor_product dpbs k dr2 dr3) dr4
             · double_glued_leftwhiskering_comp2 dpbs k dr1
             (double_glued_tensor_product dpbs k
                (double_glued_tensor_product dpbs k dr2 dr3) dr4)
             (double_glued_tensor_product dpbs k dr2
                (double_glued_tensor_product dpbs k dr3 dr4))
             (disp_monoidal_associator
                (double_glued_monoidal_data dpbs k) R2 R3 R4 dr2 dr3 dr4)):
  doublePullback_CompetitorTriangleL dP X arrL (double_glued_disp_pentagon_identity_compArrowL dpbs k dr1 dr2 dr3 dr4).
Proof.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  apply assoc'.  
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  unfold  double_glued_disp_pentagon_identity_compArrowL.
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _).
Qed.

Lemma double_glued_disp_pentagon_identity_compTrianLM {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3)
  (dP := tensor_doublePullback dpbs k
              (((pr11 dr1 ⊗_{ E} pr11 dr2) ⊗_{ E} pr11 dr3,,
                (pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2) ⊗^{ E} pr21 dr3
                · (pr112 (pr1 L)) (R1 ⊗_{ C} R2) R3),,
               pr11 dP123,,
               doublePullbackPrM dP123) dr4)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4))))
  (arrL := double_glued_rightwhiskering_comp2 dpbs k
             (double_glued_tensor_product dpbs k
                (double_glued_tensor_product dpbs k dr1 dr2) dr3)
             (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2 dr3)) dr4
             (disp_monoidal_associator
                (double_glued_monoidal_data dpbs k) R1 R2 R3 dr1 dr2 dr3)
             · double_glued_assoc_data_comp2 dpbs k dr1
             (double_glued_tensor_product dpbs k dr2 dr3) dr4
             · double_glued_leftwhiskering_comp2 dpbs k dr1
             (double_glued_tensor_product dpbs k
                (double_glued_tensor_product dpbs k dr2 dr3) dr4)
             (double_glued_tensor_product dpbs k dr2
                (double_glued_tensor_product dpbs k dr3 dr4))
             (disp_monoidal_associator
                (double_glued_monoidal_data dpbs k) R2 R3 R4 dr2 dr3 dr4)):
  doublePullback_CompetitorTriangleM dP X arrL
    (double_glued_disp_pentagon_identity_compArrowM dpbs k dr1 dr2 dr3 dr4).
Proof.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  apply assoc'.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  unfold double_glued_disp_pentagon_identity_compArrowM.
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ ! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  exact (monoidal_pentagonidentity C R1 R2 R3 R4).
Qed.

Lemma double_glued_disp_pentagon_identity_compTrianLR {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 R4 : C} (dr1 : double_glued_ob L K R1)
  (dr2 : double_glued_ob L K R2) (dr3 : double_glued_ob L K R3)
  (dr4 : double_glued_ob L K R4)
  (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP123 := tensor_doublePullback dpbs k
                  ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2),,
                     pr11 dP12,, doublePullbackPrM dP12) dr3)
  (dP := tensor_doublePullback dpbs k
              (((pr11 dr1 ⊗_{ E} pr11 dr2) ⊗_{ E} pr11 dr3,,
                (pr21 dr1 ⊗^{ E} pr21 dr2 · (pr112 (pr1 L)) R1 R2) ⊗^{ E} pr21 dr3
                · (pr112 (pr1 L)) (R1 ⊗_{ C} R2) R3),,
               pr11 dP123,,
               doublePullbackPrM dP123) dr4)
  (X := pr12 (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2
                   (double_glued_tensor_product dpbs k dr3 dr4))))
  (arrL := double_glued_rightwhiskering_comp2 dpbs k
             (double_glued_tensor_product dpbs k
                (double_glued_tensor_product dpbs k dr1 dr2) dr3)
             (double_glued_tensor_product dpbs k dr1
                (double_glued_tensor_product dpbs k dr2 dr3)) dr4
             (disp_monoidal_associator
                (double_glued_monoidal_data dpbs k) R1 R2 R3 dr1 dr2 dr3)
             · double_glued_assoc_data_comp2 dpbs k dr1
             (double_glued_tensor_product dpbs k dr2 dr3) dr4
             · double_glued_leftwhiskering_comp2 dpbs k dr1
             (double_glued_tensor_product dpbs k
                (double_glued_tensor_product dpbs k dr2 dr3) dr4)
             (double_glued_tensor_product dpbs k dr2
                (double_glued_tensor_product dpbs k dr3 dr4))
             (disp_monoidal_associator
                (double_glued_monoidal_data dpbs k) R2 R3 R4 dr2 dr3 dr4)):
  doublePullback_CompetitorTriangleR dP X arrL
    (double_glued_disp_pentagon_identity_compArrowR dpbs k dr1 dr2 dr3 dr4).
Proof.
  refine (assoc' _ _ _ @ _ @ internal_lam_natural _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_postcomp _ _).
  unfold double_glued_disp_pentagon_identity_compArrowR.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt, postcompose;
    refine (maponpaths (λ f, f · _) (when_bifunctor_becomes_rightwhiskering E _ _) @ _).

  (*
  simpl.
  set (pr12 (disp_bifunctor_on_objects (double_glued_tensor dpbs k) R2 R3 dr2 dr3)).
  set (dP23 := tensor_doublePullback dpbs k dr2 dr3).
  set (dP23_4 := tensor_doublePullback dpbs k ((pr11 dr2 ⊗_{ E} pr11 dr3,, pr21 dr2 ⊗^{ E} pr21 dr3 · (pr112 (pr1 L)) R2 R3),,
                                                 pr11 dP23,, doublePullbackPrM dP23) dr4).
  set (dP1__23_4 := (tensor_doublePullback dpbs k dr1
                       (((pr11 dr2 ⊗_{ E} pr11 dr3) ⊗_{ E} pr11 dr4,,
                           (pr21 dr2 ⊗^{ E} pr21 dr3 · (pr112 (pr1 L)) R2 R3) ⊗^{ E} pr21 dr4 · (pr112 (pr1 L)) (R2 ⊗_{ pr211 C} R3) R4),,
                          pr11 dP23_4,, doublePullbackPrM dP23_4))).
  set (dP1_23 := tensor_doublePullback dpbs k dr1 ((pr11 dr2 ⊗_{ E} pr11 dr3,, pr21 dr2 ⊗^{ E} pr21 dr3 · (pr112 (pr1 L)) R2 R3),,
                                                     pr11 dP23,, doublePullbackPrM dP23)).
  set (dP34 := tensor_doublePullback dpbs k dr3 dr4).
  set (dP2_34 := tensor_doublePullback dpbs k dr2 ((pr11 dr3 ⊗_{ E} pr11 dr4,, pr21 dr3 ⊗^{ E} pr21 dr4 · (pr112 (pr1 L)) R3 R4),,
                                                     pr11 dP34,, doublePullbackPrM dP34)).
  set (dP1__2_34 := tensor_doublePullback dpbs k dr1
             ((pr11 dr2 ⊗_{ E} (pr11 dr3 ⊗_{ E} pr11 dr4),,
               pr21 dr2 ⊗^{ E} (pr21 dr3 ⊗^{ E} pr21 dr4 · (pr112 (pr1 L)) R3 R4) · (pr112 (pr1 L)) R2 (R3 ⊗_{ C} R4)),,
              pr11 dP2_34,, doublePullbackPrM dP2_34)).
  set (comp := pr11 dP1__2_34  ⊗_{E} pr11 dr4).
  set (left := double_glued_leftwhiskering_comp2 dpbs k dr1
                 (double_glued_tensor_product dpbs k
                    (double_glued_tensor_product dpbs k dr2 dr3) dr4)
                 (double_glued_tensor_product dpbs k dr2
                    (double_glued_tensor_product dpbs k dr3 dr4))
                 (disp_monoidal_associator
                    (double_glued_monoidal_data dpbs k) R2 R3 R4 dr2 dr3 dr4)
                 ⊗^{ E}_{r} pr11 dr4
                     · (doublePullbackArrow dP1_23 ((pr11 dP1__23_4) ⊗_{E} (pr11 dr4))
                          ((doublePullbackPrL dP1__23_4
                              · (internal_postcomp (pr11 dr1) (doublePullbackPrR dP23_4) ·
                                   internal_swap_arg (pr11 dr1) (pr11 dP23) (pr11 dr4)))
                             ⊗^{ E}_{r} pr11 dr4
                                 · internal_eval (pr11 dr4) (internal_hom (pr11 dr1) (pr11 dP23)))
                          (pr11 dP1__23_4 ⊗^{ E}_{l} pr21 dr4
                                              · (doublePullbackPrM dP1__23_4
                                                   · (compose (C:=E) (# K α^{ C }_{ R1, R2 ⊗_{ pr211 C} R3, R4}) (# K (sym_mon_braiding C R4 (R1 ⊗_{ C} (R2 ⊗_{ pr211 C} R3)))))) ⊗^{ E}_{r} L R4 · (sym_mon_braiding E (K (R4 ⊗_{ C} (R1 ⊗_{ C} (R2 ⊗_{ pr211 C} R3)))) (L R4) · pr1 k R4 (R1 ⊗_{ C} (R2 ⊗_{ pr211 C} R3))))
       (doublePullbackPrR dP1__23_4
          ⊗^{ E}_{r} pr11 dr4
              · (internal_precomp (sym_mon_braiding E (pr11 dr4) (pr11 dr2 ⊗_{ E} pr11 dr3)) (pr12 dr1) ⊗^{ E}_{r} pr11 dr4
           · (internal_curry (pr11 dr4) (pr11 dr2 ⊗_{ E} pr11 dr3) (pr12 dr1) ⊗^{ E}_{r} pr11 dr4
              · internal_eval (pr11 dr4) (internal_hom (pr11 dr2 ⊗_{ E} pr11 dr3) (pr12 dr1)))))
       (associator.assocdata_lemma1 dpbs k (pr21 dr1) (pr22 dr1) (pr21 dr2 ⊗^{ E} pr21 dr3 · (pr112 (pr1 L)) R2 R3)
          (doublePullbackPrM dP23)
          (pr21 dr4) (pr22 dr4))
       (associator.assocdata_lemma2 dpbs k (pr21 dr1) (pr22 dr1) (pr21 dr2 ⊗^{ E} pr21 dr3 · (pr112 (pr1 L)) R2 R3)
          (doublePullbackPrM dP23)
          (pr21 dr4) (pr22 dr4)) · double_glued_assoc_data_comp2 dpbs k dr1 dr2 dr3)).
  change (left = doublePullbackArrow dP123 comp
    (double_glued_disp_pentagon_identity_compArrowRL dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowRM dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowRR dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowRSqrL dpbs k dr1 dr2 dr3 dr4)
    (double_glued_disp_pentagon_identity_compArrowRSqrR dpbs k dr1 dr2 dr3 dr4)).
  About doublePullbackArrowUnique'.
  show_id_type.
  set (dP' := tensor_doublePullback dpbs k (disp_bifunctor_on_objects (double_glued_tensor dpbs L K k) R1 R2 dr1 dr2) dr3).*)


  
  apply doublePullbackArrowUnique'.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  apply assoc'.
  unfold postcompose.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, _ · f) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply assoc.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (bifunctor_rightcomp E _ _ _ _ _ _).
  
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 3 refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! maponpaths (λ f, f · _) (internal_postcomp_comp _ _ _) @ _).
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_postcomp _ _ @ _).
  refine (maponpaths internal_lam (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold postcompose.
  refine (! maponpaths (λ f, internal_lam (f · _)) (when_bifunctor_becomes_rightwhiskering E _ _) @ _).
  refine (! internal_lam_natural _ _ @ _).
  refine (_ @ id_right _).
  apply maponpaths.
  exact (triangle_id_right_ad (pr2 (pr2 E _)) _).
  
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths _ (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc'.

  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  apply assoc'.
  refine (_ @ assoc _ _ _).  
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (! maponpaths (compose _) (pr12 k _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (_ @ ! functor_comp K _ _ @ _).
  apply (cancel_postcomposition (C:=E)).
  refine (maponpaths (λ f, compose (C:=E) _ f) (! functor_comp K _ _) @ _).
  apply pathsinv0.
  apply (functor_comp K).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  exact (monoidal_pentagonidentity C _ _ _ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (doublePullbackArrow_PrR _ _ _ _ _ _ _)).
  refine (internal_lam_natural _ _ @ _).
  unfold double_glued_disp_pentagon_identity_compArrowRR.
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (when_bifunctor_becomes_rightwhiskering E _ _) @ _).
  apply doublePullbackArrowUnique'.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (λ f, _ · f) (doublePullbackArrow_PrL _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (λ f, _ · f) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (! internal_postcomp_comp _ _ _) @ _).
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_postcomp _ _ @ _).
  refine (maponpaths internal_lam (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E _).
  refine (! internal_lam_natural _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths internal_lam (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E _).
  refine (! internal_lam_natural _ _ @ _).
  refine (_ @ id_right _).
  apply maponpaths.
  exact (triangle_id_right_ad (pr2 (pr2 E _)) _).
    refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply assoc.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine ( _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  apply (maponpaths (compose _)).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  do 2 refine (assoc _ _ _ @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  refine (pr12 k R4 _ _ _ @ _).
  apply maponpaths.
  apply (functor_comp K).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (assoc _ _ _ @ _ @ assoc _ _ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_braiding_naturality_left E).    
  }
  refine (_ @ assoc _ _ _ @ _ @ assoc _ _ _ @ _ @ assoc _ _ _ @ _).
  4 : {
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
    refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    apply (tensor_sym_mon_braiding E).
  }
  3 : {
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0.
    apply (bifunctor_leftcomp E).
  }
  2 : {
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (monoidal_associatornatleftright E).
  }
  do 2 refine (assoc' _ _ _ @ _).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
  2 : {
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (monoidal_associatornatleft E).
  }
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).  
  apply maponpaths.
  do 2 refine (_ @ assoc' _ _ _).
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
  }
  refine (_ @ assoc' _ _ _ @ _ @ assoc' _ _ _).
  2 : {
    apply maponpaths.
    refine (_ @ id_left _).
    rewrite <- (bifunctor_leftid E).
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (_ @ functor_id K _).
    unfold monoidal_cat_tensor_pt.
    rewrite <- (bifunctor_rightid C).
    rewrite <- (pr2 (monoidal_braiding_inverses C _ _)).
    rewrite (bifunctor_rightcomp C).
    apply pathsinv0.
    apply (functor_comp K).
  }
  refine (_ @ ! maponpaths (compose _) (natural_contraction_extranatural k _ _ _ _)).
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
  }
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
    rewrite <- (fsym_respects_braiding L).
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (_ @ id_left _).
    rewrite <- (bifunctor_leftid E).
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (_ @ functor_id K _).
    rewrite <- (pr1 (monoidal_associatorisolaw C _ _ _)).
    apply pathsinv0.
    apply (functor_comp K).
  }
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (! (pr2 (pr222 k) R4 R3 (R1 ⊗_{C} R2)) @ assoc' _ _ _).
  }
  unfold postcompose.
  repeat rewrite assoc.
  do 2 apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _ @ _ @ assoc _ _ _).
  2 : {
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
  }  
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (_ @ assoc _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths.
      apply (bifunctor_leftcomp E).
    }
    refine (_ @ assoc _ _ _ @ _).
    2 : {
      apply maponpaths.
      apply (bifunctor_leftcomp E).
    }
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_braiding_naturality_right E).
  }
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths.
      apply (bifunctor_equalwhiskers E).        
    }
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (monoidal_associatornatright E).
  }
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right E).
  apply map_on_two_paths.
  
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths compose (! functor_comp K _ _) (! functor_comp K _ _) @ _).
  refine (_ @ maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ id_left _).
    unfold monoidal_cat_tensor_pt.
    rewrite <- (pr2 (monoidal_associatorisolaw C _ _ _)).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    apply (monoidal_pentagonidentity C).
  }
  repeat rewrite assoc.
  repeat apply cancel_postcomposition.
  rewrite (bifunctor_leftcomp C).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_braiding_naturality_left C _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right C _ _ _ _)).
    apply assoc'.
  }
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator C _ _ _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering C).
  repeat rewrite assoc.
  do 2 apply cancel_postcomposition.
  rewrite <- (when_bifunctor_becomes_leftwhiskering C).
  refine (maponpaths (λ f, f · _) (! sym_mon_hexagon_rassociator C _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  apply (monoidal_associatorisolaw C). (* completes subgoal *)
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (pr1 (monoidal_braiding_inverses E _ _))).
  rewrite (bifunctor_rightid E).
  rewrite id_left.
  refine (! monoidal_braiding_naturality_right E _ _ _ _ @ _).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ ! sym_mon_tensor_lassociator E _ _ _)).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_associatorisolaw E).
    apply cancel_postcomposition.
    unfold monoidal_cat_tensor_mor; now rewrite (when_bifunctor_becomes_leftwhiskering E).
  }
  rewrite id_right.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  repeat rewrite assoc.
  apply (sym_mon_tensor_rassociator E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  (* simpl. *)
  unfold postcompose, monoidal_cat_tensor_pt.
  do 3 refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths compose (! bifunctor_rightcomp E _ _ _ _ _ _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  do 3 refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths compose (! bifunctor_rightcomp E _ _ _ _ _ _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ ! maponpaths (compose _) (internal_precomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  exact (doublePullbackArrow_PrR _ _ _ _ _ _ _).
Qed.

Lemma double_glued_disp_pentagon_identity {E C : sym_mon_closed_cat}
  (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : 
  disp_pentagon_identity (disp_monoidal_associator (double_glued_monoidal_data dpbs k)).
Proof.
  intros R1 R2 R3 R4.
  intros dr1 dr2 dr3 dr4.
  apply double_glued_mor_eq; split;
    unfold transportb, transportf;
    induction (! monoidal_pentagonidentity C R1 R2 R3 R4).
  apply (monoidal_pentagonidentity E).
  (*
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct dr3 as ((U3, l3), (X3, l3')).
  destruct dr4 as ((U4, l4), (X4, l4')). *)
  set (arrR := double_glued_assoc_data_comp2 dpbs k
                 (double_glued_tensor_product dpbs k dr1 dr2) dr3 dr4
                 · double_glued_assoc_data_comp2 dpbs k dr1 dr2
                 (double_glued_tensor_product dpbs k dr3 dr4)).
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply double_glued_disp_pentagon_identity_compArrowL.
  }
  9 : {
    apply double_glued_disp_pentagon_identity_compArrowM.
  }
  9 : {
    apply double_glued_disp_pentagon_identity_compArrowR.
  }
  exact (double_glued_disp_pentagon_identity_compSqrL dpbs k dr1 dr2 dr3 dr4).
  exact (double_glued_disp_pentagon_identity_compSqrR dpbs k dr1 dr2 dr3 dr4).
  exact (double_glued_disp_pentagon_identity_compTrianLL dpbs k dr1 dr2 dr3 dr4).
  exact (double_glued_disp_pentagon_identity_compTrianLM dpbs k dr1 dr2 dr3 dr4).
  exact (double_glued_disp_pentagon_identity_compTrianLR dpbs k dr1 dr2 dr3 dr4).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (internal_postcomp_comp _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (uncurry_nat3 _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) (! internal_postcomp_comp _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply pathsinv0.
  apply internal_uncurry_uncurry. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  exact (! functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply (maponpaths internal_lam).
  unfold postcompose, monoidal_cat_tensor_pt, monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply doublePullbackArrowUnique'.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! internal_postcomp_comp _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, f · _) (! internal_postcomp_comp _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (uncurry_nat3 _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply internal_uncurry_tensor_swap. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) _ (# K f)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  exact (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrR _ _ _ _ _ _ _)).
  unfold postcompose, monoidal_cat_tensor_pt.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (internal_lam_precomp _ _)).
  refine (assoc _ _ _ @ _).
  
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _)).
  refine (maponpaths (λ f, _ · f) _ @ _).
  refine (maponpaths (λ f, f · _) (hom_onmorphisms_is_postcomp _ _) @ _).
  apply curry_nat3.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (curry_unit _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (! internal_postcomp_comp _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (! internal_postcomp_comp _ _ _ @ _)).
  refine (! hom_onmorphisms_is_postcomp _ _).
  refine (internal_lam_tensor_eval _ @ _).
  refine (maponpaths (compose _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · f) (! hom_onmorphisms_is_postcomp _ _) @ _).
  apply (maponpaths internal_lam).
  apply doublePullbackArrowUnique'.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, (_ · f)) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, _ · f) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply assoc.
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
    apply assoc.
  }  
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    refine (! internal_postcomp_comp _ _ _ @ _).
    apply maponpaths.
    apply assoc.
  }
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (bifunctor_rightcomp E _ _ _ _ _ _).  
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (_ @ ! maponpaths (λ f, _ · f) (internal_eval_nat _ _ _ _)).
    rewrite hom_onmorphisms_is_postcomp.
    rewrite (internal_postcomp_comp _).
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (assoc _ _ _)).
    refine (! bifunctor_rightcomp E _ _ _ _ _ _).
  }
  refine (maponpaths (compose _) (! mon_closed_adj_natural_co E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (monoidal_associatornatright E _ _ _ _ _) @ _).
  apply assoc.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply internal_swap_arg_nat2.
  apply maponpaths.
  refine (! maponpaths (compose _) (curry_counit _ _ _) @ _).
  repeat rewrite assoc.
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply internal_swap_tensor_curry. (* completes subgoal *)
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _ @ _).
  apply assoc'.
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply assoc'.
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc'.
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply map_on_two_paths.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  now rewrite assoc.
  now rewrite (functor_comp K).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc.
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
    apply assoc.
  }
  apply maponpaths.
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (_ @ ! maponpaths (λ f, _ · f) (internal_eval_nat _ _ _ _)).
    rewrite hom_onmorphisms_is_postcomp.
    apply assoc'.
  }
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc.  
  refine (maponpaths (compose _) (! mon_closed_adj_natural_co E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply (monoidal_associatornatright E).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (! curry_counit _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite (internal_postcomp_comp _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (λ f, _ · (_ · f)) (id_right _)).
    rewrite <- internal_precomp_id.
    refine (_ @ maponpaths (λ f, _ · f) (curry_nat12 _ _ _)).
    rewrite (when_bifunctor_becomes_leftwhiskering E).
    apply assoc'.
  }
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! curry_nat12 _ _ _).
  apply maponpaths.
  refine (! id_left _ @ _).
  refine (maponpaths (λ f, f · _) (! internal_postcomp_id _ _ @ _)).
  refine (maponpaths (λ f, internal_postcomp _ f) (! internal_precomp_id _ _)).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ maponpaths (compose _) (internal_curry_curry _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  apply cancel_postcomposition.
  refine (_ @ maponpaths (λ f, f · _) (internal_precomp_comp _ _ _)).
  refine (! internal_precomp_comp _ _ _ @ _ @ internal_precomp_comp _ _ _).
  apply (maponpaths (λ f, internal_precomp f _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (compose _) (sym_mon_tensor_lassociator0 E _ _ _)).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ assoc' _ _ _).
  refine (! monoidal_braiding_naturality_right E _ _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
  2 : {
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ assoc' _ _ _).
    rewrite <- (when_bifunctor_becomes_leftwhiskering E).
    apply (sym_mon_hexagon_rassociator E).
  }
  refine (_ @ ! maponpaths (compose _) (pr2 (monoidal_associatorisolaw E _ _ _))).
  rewrite id_right.
  refine (! id_left _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_associatorisolaw E).
Qed.

Lemma double_glued_monoidal_laws {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  disp_monoidal_laws (double_glued_monoidal_data dpbs k).
Proof.
  split5.
  exact (double_glued_disp_leftunitor_law dpbs k).
  exact (double_glued_disp_rightunitor_law dpbs k).
  exact (double_glued_disp_associator_law dpbs k).
  exact (double_glued_disp_triangle_identity dpbs k).
  exact (double_glued_disp_pentagon_identity dpbs k).
Qed.

