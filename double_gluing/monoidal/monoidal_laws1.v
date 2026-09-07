(**************************************

In this file we prove some of the coherence laws of the monoidal structure, namely:
- associator :
  - naturality in each component
  - isolaw
- triangle identity

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

Local Lemma double_glued_monoidal_laws_lemma1 {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧) (ϕ34 : E⟦U3, U4⟧)
  (ψ34 : E⟦X4, X3⟧) (dpb24 := tensor_doublePullback dpbs k ((U2,, l2),, X2,, l2') ((U4,, l4),, X4,, l4'))
  (dpb124 := tensor_doublePullback dpbs k ((U1,, l1),, X1,, l1') ((U2 ⊗_{ E} U4,, l2 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R2 R4),, pr11 dpb24,, doublePullbackPrM dpb24)):
  (doublePullbackPrL dpb124
   · (internal_postcomp U1 (doublePullbackPrR dpb24) · internal_swap_arg U1 X2 U4))
  ⊗^{ E}_{r} U3 · (internal_hom U4 (internal_hom U1 X2) ⊗^{ E}_{l} ϕ34 · internal_eval U4 (internal_hom U1 X2)) · internal_postcomp U1 l2' =
  (doublePullbackPrM dpb124
   · # K (sym_mon_braiding C R4 (R1 ⊗_{ C} R2) · α^{ C }_{ R1, R2, R4})) ⊗^{ E}_{r} U3
  · (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R2)) ⊗^{ E}_{l} (ϕ34 · l4)
     · (sym_mon_braiding E (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R2))) (L R4) · pr1 k R4 (R1 ⊗_{ C} R2)))
  · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2)).
Proof.
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · (_ · f))) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U4))) _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E U3 _ _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, (_ · internal_postcomp U4 f) ⊗^{E}_{r} U3 · _) (hom_onmorphisms_is_postcomp U1 l2') @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U3 · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} U3 · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · (_ · f)) ⊗^{E}_{r} U3 · _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} U3 · _) (assoc _ _ _) @ _).
  rewrite <- (internal_postcomp_comp U1).
  refine (! maponpaths (λ f, (_ · (internal_postcomp U1 f · _)) ⊗^{E}_{r} U3 · _) (doublePullbackSqrRCommutes _) @ _).
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} U3 · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U3 · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} U3 · _) (doublePullbackSqrLCommutes _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U3 · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E U3).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite 3 internal_lam_precomp.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · (_ · internal_lam f)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (internal_lam_natural _ _)).
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (f · _ · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (f · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (f · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_lam (_ · f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (id_left _)).
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (id_left _)).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  rewrite (bifunctor_rightcomp E (K (R4 ⊗_{C} (R1 ⊗_{ C} R2)))).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (pr2 (pr222 k) R4 R1 R2)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (_ · f))) (id_left _)).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (functor_id L).
  rewrite <- (pr2 (monoidal_braiding_inverses C _ _)).
  rewrite (functor_comp L).
  rewrite (bifunctor_rightcomp E (K ((R4 ⊗_{C} R1) ⊗_{ C} R2))).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (_ · f))) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc' _ _ _)).
  generalize (pr122 k R2 _ _ (sym_mon_braiding C R1 R4)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (_ · f))) keq); clear keq.
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f · _ · _))) (assoc _ _ _)).
  rewrite <- (bifunctor_rightcomp E (K ((R4 ⊗_{C} R1) ⊗_{ C} R2))).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f · _))) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_lam (_ · (_ · f · _))) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f · _))) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  unfold monoidal_cat_tensor_pt, monoidal_braiding_data_inv.
  rewrite <- (fsym_respects_braiding L).
  rewrite (bifunctor_rightcomp E (K ((R1 ⊗_{C} R4) ⊗_{ C} R2))).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f · _))) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (id_left _)).
  rewrite <- (bifunctor_leftid E).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (_ ⊗^{E}_{l} f · _))) (functor_id K _)).
  rewrite <- (pr1 (monoidal_associatorisolaw C _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_lam (_ · (_ ⊗^{E}_{l} f · _))) (functor_comp K _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_lam (_ · (compose (C:=E) f _))) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc' _ _ _)).
  generalize (pr2 (pr222 k) R1 R4 R2); simpl; unfold postcompose; intros keq.
  refine (_ @ ! maponpaths (λ f, _ · internal_lam (_ · f)) keq); clear keq.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · ((_ · (internal_postcomp _ (_ · internal_lam f) · _)) ⊗^{E}_{r} _ · _))
            (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · ((_ · (internal_postcomp _ (_ · f) · _)) ⊗^{E}_{r} _ · _))
            (internal_lam_postcomp _ _) @ _).
  refine (maponpaths (λ f, _ · ((_ · (internal_postcomp _ f · _)) ⊗^{E}_{r} _ · _)) (assoc _ _ _) @ _).
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, _ · ((_ · f) ⊗^{E}_{r} _ · _)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · ((_ · f) ⊗^{E}_{r} _ · _)) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E U4).
  rewrite assoc'.
  rewrite assoc.
  rewrite <- (hom_onmorphisms_is_postcomp U4).
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U4))) _ _ _) @ _).
  rewrite assoc.
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (internal_lam_postcomp _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, _ · (internal_lam f · _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _ · _) ⊗^{E}_{r} _ · _) (internal_lam_postcomp _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite <- (internal_postcomp_comp U1).
  refine (maponpaths (λ f, _ · (_ · internal_postcomp U1 f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · internal_postcomp U1 (f · _) · _) ⊗^{E}_{r} _ · _) (pr12 k R1 _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · internal_postcomp U1 f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · internal_postcomp U1 (_ · f) · _) ⊗^{E}_{r} _ · _) (internal_lam_natural _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, _ · (_ · internal_postcomp U1 (_ · internal_lam f) · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · internal_postcomp U1 (_ · internal_lam (f · _)) · _) ⊗^{E}_{r} _ · _)
            (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · internal_postcomp U1 (_ · internal_lam f) · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (maponpaths (λ f, _ · (_ · internal_postcomp U1 (_ · internal_lam f) · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · internal_postcomp U1 (_ · f) · _) ⊗^{E}_{r} _ · _) (internal_lam_postcomp _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · internal_postcomp U1 f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, _ · (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f) ⊗^{E}_{r} _ · _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  rewrite <- (hom_onmorphisms_is_postcomp U4).
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U4))) _ _ _) @ _).
  rewrite assoc.
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f) (internal_lam_postcomp _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite (bifunctor_leftcomp E (K (R1 ⊗_{ C} (R2 ⊗_{ C} R4)))).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite internal_lam_postcomp.
  refine (maponpaths (λ f, (internal_lam f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite internal_lam_natural. 
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! internal_lam_natural _ _).
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).   
  unfold internal_lam.
  rewrite 3 hom_onmorphisms_is_postcomp.
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · internal_postcomp _ (internal_postcomp U4 f) · _) ⊗^{E}_{r} _ · _) (id_left _) @ _).
  unfold monoidal_cat_tensor_pt; simpl.
  rewrite <- (pr1 (monoidal_associatorisolaw E _ _ _)).
  refine (maponpaths (λ f, (_ · internal_postcomp _ (internal_postcomp U4 f) · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (internal_postcomp_comp U4).
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (curry_unit _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · (f · _)) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_swap _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite <- internal_pre_post_comp_as_post_pre_comp.
  rewrite internal_pre_post_comp_as_pre_post_comp.
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (f · _ · _) ⊗^{E}_{r} _ · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (curry_unit _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_postcomp_comp U4 _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_postcomp_comp U4 _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  rewrite <- (hom_onmorphisms_is_postcomp U4).
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U4))) _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_left.
  simpl.
  apply maponpaths.
  refine (! internal_postcomp_comp U1 _ _ @ _).
  apply maponpaths.
  rewrite (maponpaths (λ f, f ⊗^{E}_{r} U4) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E).
  refine (maponpaths (λ f, _ · (_ · (_ · f))) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleftright E).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (bifunctor_leftcomp E).
  rewrite (monoidal_braiding_naturality_left E U4 U1).
  rewrite (bifunctor_leftcomp E).
  refine (maponpaths (λ f, _ · f) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite (monoidal_associatornatleft E).
  rewrite assoc'.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · (f · _) · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f) · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (bifunctor_rightcomp E).
  refine (_ @ ! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (pr1 (monoidal_braiding_inverses E _ _))).
  rewrite (bifunctor_rightid E).
  rewrite id_left.
  refine (_ @ assoc _ _ _).
  do 4 refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  rewrite (monoidal_braiding_naturality_left E).
  do 2 refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, _ · (_ · (_ · f))) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · (_ · (f · _)))) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · (_ · f))) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleft E).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (bifunctor_leftcomp E).
  rewrite (monoidal_braiding_naturality_right E U4).
  rewrite (bifunctor_leftcomp E).
  refine (maponpaths (λ f, _ · f) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite (monoidal_associatornatleftright E).
  rewrite assoc'.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_right E _ _ (L R1)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  do 2 rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite (monoidal_associatorinvnatleft E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  rewrite <- (monoidal_associatornatleft E).
  refine (_ @ assoc' _ _ _).
  rewrite (bifunctor_leftcomp E).
  rewrite 4 assoc.
  apply map_on_two_paths.
  apply (pathscomp0 (b:= sym_mon_braiding E _ _ ⊗^{E}_{r} _ · α^{E}_{_,_,_} · _ ⊗^{E}_{l} sym_mon_braiding E _ _)).
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (sym_mon_tensor_lassociator1 E _ _ _) @ _).
  refine (_ @ id_right _).
  rewrite 2 assoc'.
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  apply (monoidal_braiding_inverses E). (* completes subgoal *)
  do 2 refine (_ @ assoc _ _ _).
  rewrite (monoidal_braiding_naturality_right E).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (_ @ maponpaths (compose _) (id_right _)).
  rewrite <- (bifunctor_leftid E).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr1 (monoidal_braiding_inverses E _ _)).
  rewrite (bifunctor_leftcomp E).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ maponpaths (compose _) (sym_mon_hexagon_lassociator E _ _ _)).
  refine (! id_left _ @ _).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (pr2 (monoidal_associatorisolaw E _ _ _))).
  rewrite id_right.
  apply pathsinv0.
  apply (monoidal_braiding_inverses E). (* completes subgoal *)
  do 2 apply maponpaths.
  refine (_ @ maponpaths (λ f, compose (C:=E) _ f · _) (functor_comp K _ _)).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _)).
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  rewrite assoc.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (sym_mon_hexagon_lassociator C _ _ _)).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering C).
  rewrite (when_bifunctor_becomes_leftwhiskering C).
  refine (! id_left _ @ _).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_rightcomp C _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f ⊗^{C}_{r} _ · _) (pr2 (monoidal_braiding_inverses C _ _))).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_rightid C _ _)).
  rewrite id_right.
  apply pathsinv0.
  apply (monoidal_associatorisolaw C). (* completes subgoal *)
Qed.

Local Lemma double_glued_monoidal_laws_lemma2 {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧) (ϕ34 : E⟦U3, U4⟧)
  (ψ34 : E⟦X4, X3⟧) (dpb24 := tensor_doublePullback dpbs k ((U2,, l2),, X2,, l2') ((U4,, l4),, X4,, l4'))
  (dpb124 := tensor_doublePullback dpbs k ((U1,, l1),, X1,, l1') ((U2 ⊗_{ E} U4,, l2 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R2 R4),, pr11 dpb24,, doublePullbackPrM dpb24)):
  (doublePullbackPrM dpb124
   · # K (sym_mon_braiding C R4 (R1 ⊗_{ C} R2) · α^{ C }_{ R1, R2, R4})) ⊗^{ E}_{r} U3
  · (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R2)) ⊗^{ E}_{l} (ϕ34 · l4)
     · (sym_mon_braiding E (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R2))) (L R4) · pr1 k R4 (R1 ⊗_{ C} R2)))
  · (compose (C:=E) (# K (sym_mon_braiding C R2 R1)) (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1) · internal_precomp l2 (K R1))) =
  (doublePullbackPrR dpb124
     · (internal_precomp (sym_mon_braiding E U4 U2) X1 · internal_curry U4 U2 X1)) ⊗^{ E}_{r} U3 · (internal_hom U4 (internal_hom U2 X1) ⊗^{ E}_{l} ϕ34 · internal_eval U4 (internal_hom U2 X1)) · internal_postcomp U2 l1' .
Proof.
  refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  2 : {
    apply maponpaths.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths.
      refine (_ @ ! internal_eval_nat _ _ _ _).
      now rewrite hom_onmorphisms_is_postcomp.
    }
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply (bifunctor_equalwhiskers E).
  }
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
    apply maponpaths.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths.
      refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _ @ assoc _ _ _).
      2 : {
        apply maponpaths.
        apply curry_nat3.
      }
      apply cancel_postcomposition.
      refine (_ @ internal_pre_post_comp_as_pre_post_comp _ _).
      now rewrite internal_pre_post_comp_as_post_pre_comp.
    }
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply doublePullbackSqrRCommutes.
  }
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_rightcomp E).
  apply maponpaths.
  refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
  2 : {
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
  }
  refine (_ @ ! internal_lam_natural _ _ @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  2 : {
    apply maponpaths.
    refine (! internal_lam_tensor_eval _ @ _).
    apply cancel_postcomposition.
    apply maponpaths.
    refine (! internal_lam_curry _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (! internal_lam_precomp _ _ @ _).
    apply cancel_postcomposition.
    refine (! internal_lam_natural _ _ @ _).
    apply maponpaths.
    apply pathsinv0.
    apply internal_lam_precomp.
  }
  do 2 refine (assoc _ _ _ @ _).
  refine (_ @ internal_lam_natural _ _ @ _).
  apply maponpaths.
  apply internal_lam_precomp.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt; rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ maponpaths (compose _) _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (pr12 k).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_leftcomp E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (functor_comp K).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_rightcomp E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  apply maponpaths.
  apply (natural_contraction_composed k).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply (monoidal_associatorinvnatright E).
  refine ( _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (monoidal_associatorinvnatleftright E).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ bifunctor_equalwhiskers E _ _ _ _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_rightcomp E).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply (fsym_respects_braiding L).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (natural_contraction_extranatural k).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).
  do 2 refine (assoc _ _ _ @ _).
  do 4 refine (_ @ assoc' _ _ _ ).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  2 : {
    apply maponpaths.
    apply (monoidal_braiding_naturality_left E).
  }
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
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
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! monoidal_associatorinvnatleft E _ _ _ _ _).
  apply maponpaths.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (functor_comp K).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right E).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right E).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (functor_comp K).
  refine (assoc' _ _ _ @ _).
  apply map_on_two_paths.
  do 3 apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator0 _ _ _ _) @ _).
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_leftwhiskering C).
  refine (assoc _ _ _ @ _ @ id_right _).
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (! bifunctor_leftcomp C _ _ _ _ _ _ @ _ @ bifunctor_leftid C _ _).
    apply maponpaths.
    apply sym_mon_braiding_inv.
  }
  apply cancel_postcomposition.
  refine (_ @ ! monoidal_braiding_naturality_right C _ _ _ _).
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_leftwhiskering C).
  repeat rewrite assoc.
  apply pathsinv0.
  apply sym_mon_tensor_rassociator.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    apply sym_mon_hexagon_rassociator0.
  }
  refine (_ @ maponpaths (compose _) _ @ _).
  3 : {
    do 2 refine (_ @ assoc _ _ _).
    apply assoc.
  }
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  simpl.
  repeat rewrite assoc.
  
  refine (! id_left _ @ _ @ maponpaths (compose _) _ @ _).
  3 : {
    refine (assoc _ _ _ @ assoc _ _ _).
  }
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_associatorisolaw E).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply sym_mon_tensor_lassociator1.
  refine (_ @ id_right _).
  repeat rewrite assoc'.
  repeat apply maponpaths.
  apply (monoidal_associatorisolaw E).
Qed.

Local Lemma double_glued_monoidal_laws_lemma3 {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧) (f12 : C⟦R1, R2⟧)
  (ϕ12 : E⟦U1, U2⟧) (eqphi : double_glued_mor_eq1 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') f12 ϕ12)
  (dpb34 := tensor_doublePullback dpbs k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb234 := tensor_doublePullback dpbs k ((U2,, l2),, X2,, l2') ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4),, pr11 dpb34,, doublePullbackPrM dpb34)):
  (doublePullbackPrL dpb234
   · (internal_postcomp U2 (doublePullbackPrR dpb34)
      · (internal_precomp ϕ12 (internal_hom U4 X3) · internal_swap_arg U1 X3 U4))) ⊗^{ E}_{r} U4 · internal_eval U4 (internal_hom U1 X3)
  · internal_postcomp U1 l3' =
  (doublePullbackPrM dpb234
   · # K (sym_mon_braiding C R4 (R1 ⊗_{ C} R3) · α^{ C }_{ R1, R3, R4} · f12 ⊗^{ C}_{r} (R3 ⊗_{ C} R4))) ⊗^{ E}_{r} U4
  · (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R3)) ⊗^{ E}_{l} l4
     · (sym_mon_braiding E (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R3))) (L R4) · pr1 k R4 (R1 ⊗_{ C} R3)))
  · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3)).
Proof.
  rewrite assoc'.
  refine (! maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U4))) _ _ _) @ _).
  simpl.
  rewrite (functor_comp (pr1 (pr2 E U1))).
  refine (maponpaths (λ f, _ · ((# _ f) ⊗^{E}_{r} U4 · _)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · ((# _ (f · _)) ⊗^{E}_{r} U4 · _)) (triangle_id_right_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_left.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} U4 · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (assoc _ _ _ @ _).
  rewrite <- (bifunctor_rightcomp E).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U4 · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} U4 · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · (_ · f)) ⊗^{E}_{r} U4 · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · (_ · (_ · f))) ⊗^{E}_{r} U4 · _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (_ · (_ · f)) ⊗^{E}_{r} U4 · _) (assoc _ _ _) @ _).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (maponpaths (λ f, (_ · (_ · f)) ⊗^{E}_{r} U4 · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} U4 · _) (assoc _ _ _) @ _).
  rewrite <- (internal_postcomp_comp U2).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U4 · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · internal_postcomp _ f · _) ⊗^{E}_{r} U4 · _) (doublePullbackSqrRCommutes dpb34) @ _).
  rewrite (internal_postcomp_comp U2).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} U4 · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U4 · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} U4 · _) (doublePullbackSqrLCommutes dpb234) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U4 · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  repeat rewrite internal_lam_precomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! internal_lam_natural _ _).
  do 2 refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite internal_lam_natural.
  rewrite internal_lam_postcomp.
  rewrite internal_lam_precomp.
  refine (maponpaths (λ f, (internal_lam f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite internal_lam_natural.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt; rewrite 3 (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, (internal_lam (internal_lam (f ⊗^{E}_{r} _ · _)) · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (internal_lam (internal_lam ((f · _) ⊗^{E}_{r} _ · _)) · _) ⊗^{E}_{r} _ · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (internal_lam (internal_lam f) · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (internal_lam (internal_lam (f · _)) · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  unfold internal_lam.
  rewrite 3 hom_onmorphisms_is_postcomp.
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · (_ · f)) ⊗^{E}_{r} _ · _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E U4).
  refine (assoc' _ _ _ @ _).
  rewrite <- (hom_onmorphisms_is_postcomp U4).
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U4))) _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _ · _) (internal_swap_arg_unit _ _ _) @ _).
  unfold monoidal_cat_tensor_pt; simpl.
  rewrite (bifunctor_rightcomp E U4).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (hom_onmorphisms_is_postcomp U4).
  refine (maponpaths (λ f, _ · f · _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U4))) _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_left.
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (internal_postcomp_comp U1 _ _) @ _).
  apply (maponpaths (compose _)).
  apply maponpaths.
  repeat rewrite assoc.
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _ · _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f) ⊗^{E}_{r} _ · _ · _ · _) (pr12 k R2 _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _ · _ · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E U4).
  refine (maponpaths (λ f, f · _ · _ · _) (assoc _ _ _) @ _).
  rewrite 3 assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (! id_left _) @ _).
  simpl.
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (! id_left _) @ _).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  rewrite (bifunctor_rightcomp E (K (R2 ⊗_{ C} (R4 ⊗_{ C} R3)))).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  do 2 refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (compose _) (pr2 (pr222 k) R2 R4 R3) @ _).
  rewrite (bifunctor_rightcomp E U1).
  do 3 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  rewrite (bifunctor_rightcomp E (K (R4 ⊗_{C} (R1 ⊗_{ C} R3)))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  do 2 refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (pr2 (pr222 k) R4 R1 R3)).
  rewrite (assoc' (C:=C)).
  rewrite (monoidal_associatornatright C).
  rewrite (assoc (C:=C)).
  rewrite (monoidal_braiding_naturality_left C).
  rewrite (assoc' (C:=C)).
  rewrite (functor_comp K).
  repeat refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U1 · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (f · _) ⊗^{E}_{r} U1 · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U1 · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} U1 · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · (f · _)) ⊗^{E}_{r} U1 · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} U1 · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U1 · _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U1 · _) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E U1).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite (monoidal_associatorinvnatleft E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  unfold monoidal_braiding_data_inv.
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_comp K _ _)).
  rewrite (monoidal_associatornatleftright C).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_comp K _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k R3 _ _ (R4 ⊗^{ C}_{l} f12)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (compose _) keq); clear keq.
  do 3 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (bifunctor_rightcomp E).
  rewrite (fsym_respects_braiding L).
  rewrite (bifunctor_rightcomp E (K ((R4 ⊗_{ C} R2) ⊗_{ C} R3))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  rewrite <- (functor_comp L).
  rewrite (monoidal_braiding_naturality_right C).
  rewrite (functor_comp L).
  rewrite (bifunctor_rightcomp E (K ((R4 ⊗_{ C} R2) ⊗_{ C} R3))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k R3 _ _ (sym_mon_braiding C R2 R4)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (compose _) keq); clear keq.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (bifunctor_rightcomp E).
  (* apply naturality of preservestensordata *)
  rewrite <- fmonoidal_preservestensornatright.
  rewrite (bifunctor_rightcomp E (K ((R4 ⊗_{ C} R2) ⊗_{ C} R3))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite eqphi.
  do 4 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f ⊗^{ E}_{r} U4 · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E U4).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleftright E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (bifunctor_leftcomp E).
  rewrite (monoidal_braiding_naturality_left E).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (monoidal_associatornatleft E).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (bifunctor_leftcomp E _ _ _ _ _ _).
  rewrite <- (monoidal_associatorinvnatright E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite (bifunctor_rightcomp E U4).
  rewrite 3 assoc.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite (monoidal_associatorinvnatleft E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ ! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E (L R2)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite (monoidal_associatorinvnatleft E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (bifunctor_leftcomp E).
  apply map_on_two_paths.
  rewrite 2 assoc'.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleft E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (bifunctor_leftcomp E).
  rewrite (monoidal_braiding_naturality_right E).
  rewrite (bifunctor_leftcomp E (K (R2 ⊗_{ C} (R3 ⊗_{ C} R4)))).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  rewrite (monoidal_associatornatleftright E).
  rewrite (bifunctor_rightcomp E (L R2)).
  rewrite assoc'.
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  repeat refine (maponpaths (compose _) (assoc _ _ _) @ _).
  use pathscomp0.
  apply (compose (α^{E}_{_,_,_})).
  exact (sym_mon_braiding E _ _ · (sym_mon_braiding E _ _ ⊗^{E}_{r} _)).
  apply maponpaths.
  apply (maponpaths (postcompose _)).
  rewrite sym_mon_tensor_lassociator.
  apply (maponpaths (postcompose _)).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite assoc'.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (maponpaths (compose _) (sym_mon_tensor_rassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ id_left _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_right.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  rewrite <- (bifunctor_leftid E).
  apply maponpaths.
  apply (monoidal_braiding_inverses E). (* completes subgoal *)
  refine (maponpaths (λ f, _ · (f · _)) (sym_mon_tensor_lassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  do 4 refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  apply maponpaths.
  refine (! id_left _ @ _).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (sym_mon_tensor_lassociator0 E _ _ _) @ _).
  repeat rewrite assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite 3 assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · _ ⊗^{E}_{l} f · _) (pr1 (monoidal_braiding_inverses E _ _)) @ _).
  rewrite (bifunctor_leftid E).
  rewrite id_right.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ ·  f · _) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_right.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  rewrite <- (bifunctor_rightid E).
  apply maponpaths.
  apply (monoidal_braiding_inverses E). (* completes subgoal *)
  apply maponpaths.
  refine (_ @ maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _)  (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (sym_mon_hexagon_lassociator C _ _ _)).
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt.
  rewrite (when_bifunctor_becomes_leftwhiskering C).
  rewrite (when_bifunctor_becomes_rightwhiskering C).
  refine (! id_left _ @ _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_rightcomp C _ _ _ _ _ _).
  rewrite <- (bifunctor_rightid C).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_inverses C).
Qed.

Local Lemma double_glued_monoidal_laws_lemma4 {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧) (f12 : C⟦R1, R2⟧)
  (ϕ12 : E⟦U1, U2⟧) (ψ12 : E⟦X2, X1⟧) (eqphi : double_glued_mor_eq1 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') f12 ϕ12)
  (eqpsi : double_glued_mor_eq2 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') f12 ψ12)
  (dpb34 := tensor_doublePullback dpbs k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb234 := tensor_doublePullback dpbs k ((U2,, l2),, X2,, l2') ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4),,pr11 dpb34,, doublePullbackPrM dpb34)) :
  (doublePullbackPrM dpb234
   · # K (sym_mon_braiding C R4 (R1 ⊗_{ C} R3) · α^{ C }_{ R1, R3, R4} · f12 ⊗^{ C}_{r} (R3 ⊗_{ C} R4))) ⊗^{ E}_{r} U4
  · (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R3)) ⊗^{ E}_{l} l4
     · (sym_mon_braiding E (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R3))) (L R4) · pr1 k R4 (R1 ⊗_{ C} R3)))
  · (compose (C:=E) (# K (sym_mon_braiding C R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1) · internal_precomp l3 (K R1))) =
  (doublePullbackPrR dpb234
   · (internal_postcomp (U3 ⊗_{ E} U4) ψ12 · (internal_precomp (sym_mon_braiding E U4 U3) X1 · internal_curry U4 U3 X1))) ⊗^{ E}_{r} U4
  · internal_eval U4 (internal_hom U3 X1) · internal_postcomp U3 l1'.
Proof.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat  _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E U4 _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} U4 · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · (f · _)) ⊗^{ E}_{r} U4 · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{ E}_{r} U4 · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · (_ · f)) ⊗^{ E}_{r} U4 · _) (curry_nat3 _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{ E}_{r} U4 · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · (f · _)) ⊗^{ E}_{r} U4 · _) (assoc _ _ _)).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (_ @ maponpaths (λ f, (_ · (f · _)) ⊗^{ E}_{r} U4 · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{ E}_{r} U4 · _) (assoc _ _ _)).
  rewrite <- internal_postcomp_comp.
  refine (_ @ maponpaths (λ f, (_ · (internal_postcomp _ f · _)) ⊗^{ E}_{r} U4 · _) eqpsi).
  refine (_ @ ! maponpaths (λ f, (_ · (compose (C:=E) f _)) ⊗^{ E}_{r} U4 · _) (internal_postcomp_comp _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{ E}_{r} U4 · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} U4 · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{ E}_{r} U4 · _) (doublePullbackSqrRCommutes dpb234)).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} U4 · _) (assoc _ _ _)).
  rewrite 2 (bifunctor_rightcomp E).
  refine (_ @ assoc _ _ _).
  rewrite 2 assoc'.
  apply maponpaths.
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} U4 · _) (_ @ assoc' _ _ _ @ assoc' _ _ _)).
  2 : {
    do 3 apply cancel_postcomposition.
    apply maponpaths.
    apply pathsinv0.
    apply internal_lam_precomp.
  }
  rewrite internal_lam_precomp.
  do 2 refine (assoc _ _ _ @ _).
  rewrite 2 internal_lam_natural.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  rewrite internal_lam_postcomp.
  rewrite internal_lam_precomp.
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} U4 · _) (assoc _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (λ f, (_ · f) ⊗^{ E}_{r} U4 · _) (curry_nat3 _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} U4 · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{ E}_{r} U4 · _) (curry_unit _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} U4 · _) (assoc _ _ _)).
  rewrite <- (internal_postcomp_comp U4).
  refine (_ @ maponpaths (λ f, (_ · internal_postcomp _ f) ⊗^{ E}_{r} U4 · _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} U4 · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{ E}_{r} U4 · _) (internal_postcomp_comp U4 _ _)).
  rewrite (bifunctor_rightcomp E U4).
  refine (_ @ assoc _ _ _).
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _)).
  rewrite id_left.
  apply (maponpaths (compose _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  apply maponpaths.
  do 2 refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (pr12 k R4 _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  do 2 refine (assoc' _ _ _ @ _).
  simpl.
  rewrite (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · (f · _) · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · _ ⊗^{ E}_{l} f · _) (tensor_sym_mon_braiding _ _ _)).
  unfold monoidal_cat_tensor_mor.
  rewrite (bifunctor_equalwhiskers E).
  unfold functoronmorphisms2.
  rewrite 2 (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite (monoidal_associatornatleft E).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (monoidal_associatornatleftright E _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, (f · _ · _) ⊗^{E}_{r} _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  do 2 refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  apply maponpaths.
  do 3 refine (_ @ assoc' _ _ _).
  do 2 refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (pr12 k _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite assoc.
  refine (maponpaths (compose _) (! id_left _) @ _).
  simpl.
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (! id_left _) @ _).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  rewrite (bifunctor_rightcomp E (K (R4 ⊗_{ C} (R3 ⊗_{C} R1)))). 
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  do 2 refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (compose _) (pr2 (pr222 k) R4 R3 R1) @ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite 2 (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (functor_comp K _ _)).
  rewrite <- (monoidal_braiding_naturality_left C).
  refine (_ @ ! maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (functor_comp K _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite (monoidal_associatornatright E).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  do 3 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite <- (bifunctor_rightcomp E (L R4)).
  refine (! maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (functor_comp K _ _) @ _).
  rewrite (assoc (C:=C)).  
  rewrite (functor_comp K).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E (L R3)).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  rewrite (fsym_respects_braiding L).
  rewrite (bifunctor_leftcomp E (K ((R3 ⊗_{ C} R4) ⊗_{ C} R1))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k R1 _ _ (sym_mon_braiding C R4 R3)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (compose _) keq).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite (monoidal_associatornatright E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite <- (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleft E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite (monoidal_braiding_naturality_right E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite <- (bifunctor_rightcomp E).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (monoidal_braiding_naturality_right E).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  apply map_on_two_paths.
  apply maponpaths.
  do 2 rewrite <- (bifunctor_rightcomp E).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  rewrite <- (monoidal_braiding_naturality_right C).
  refine (maponpaths (λ f, _ · (_ · f · _)) (sym_mon_tensor_lassociator C _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering C).
  rewrite (when_bifunctor_becomes_leftwhiskering C).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (pr2 (monoidal_associatorisolaw C _ _ _)) @ _).
  rewrite id_right.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! id_right _ @ _).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr1 (monoidal_braiding_inverses C _ _)).
  rewrite assoc.
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator C _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering C).
  rewrite (when_bifunctor_becomes_leftwhiskering C).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  do 3 refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (pr1 (monoidal_associatorisolaw C _ _ _)) @ _).
  rewrite id_left.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp C R3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{C}_{r} _ · _)) (pr1 (monoidal_braiding_inverses C _ _)) @ _).
  rewrite (bifunctor_rightid C).
  rewrite id_left.
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (pr2 (monoidal_associatorisolaw C _ _ _)) @ _).
  rewrite id_left.
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp C _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ ⊗^{C}_{l} f · _)) (pr1 (monoidal_braiding_inverses C _ _)) @ _).
  rewrite (bifunctor_leftid C).
  rewrite id_left.
  exact (pr1 (monoidal_associatorisolaw C _ _ _)).
  refine (_ @ ! maponpaths (compose _) (sym_mon_tensor_lassociator E _ _ _)).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  do 3 refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr1 (monoidal_associatorisolaw E _ _ _))).
  rewrite id_left.
  apply maponpaths.
  repeat rewrite assoc.
  apply sym_mon_hexagon_rassociator1.
Qed.

Local Lemma double_glued_monoidal_laws_lemma5 {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧) (f23 : C⟦R2, R3⟧)
  (ϕ23 : E⟦U2, U3⟧) (ψ23 : E⟦X3, X2⟧) (eqphi : double_glued_mor_eq1 L K _ _ ((U2,, l2),, X2,, l2') ((U3 ,, l3),, X3,, l3') f23 ϕ23)
  (eqpsi : double_glued_mor_eq2 L K _ _ ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3') f23 ψ23)
  (dpb34 := tensor_doublePullback dpbs k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb134 := tensor_doublePullback dpbs k ((U1,, l1),, X1,, l1') ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4),,pr11 dpb34,, doublePullbackPrM dpb34)) :
(doublePullbackPrL dpb134
   · (internal_postcomp U1 (doublePullbackPrR dpb34) · internal_swap_arg U1 X3 U4))
  ⊗^{ E}_{r} U4 · (internal_eval U4 (internal_hom U1 X3) · internal_postcomp U1 ψ23) · internal_postcomp U1 l2' =
  (doublePullbackPrM dpb134
   · # K (sym_mon_braiding C R4 (R1 ⊗_{ C} R2) · α^{ C }_{ R1, R2, R4} · R1 ⊗^{ C}_{l} (f23 ⊗^{ C}_{r} R4))) ⊗^{ E}_{r} U4
  · (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R2)) ⊗^{ E}_{l} l4
     · (sym_mon_braiding E (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R2))) (L R4) · pr1 k R4 (R1 ⊗_{ C} R2)))
  · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2)).
Proof.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite <- (internal_postcomp_comp U1).
  refine (! maponpaths (λ f, _ · (compose (C:=E) _ (internal_postcomp _ f))) eqpsi @ _).
  refine (maponpaths (λ f, _ · (compose (C:=E) _ f)) (internal_postcomp_comp U1 _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E U4 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite <- (internal_postcomp_comp U1).
  refine (! maponpaths (λ f, (_ · internal_postcomp _ f · _) ⊗^{E}_{r} _ · _) (doublePullbackSqrRCommutes dpb34) @ _).  
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackSqrLCommutes dpb134) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  repeat rewrite internal_lam_precomp.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite internal_lam_postcomp.
  refine (maponpaths (λ f, (internal_lam f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (_ @ assoc' _ _ _).
  rewrite 2 internal_lam_natural.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  unfold internal_lam.
  rewrite 3 hom_onmorphisms_is_postcomp.
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (internal_swap_arg_unit _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _ · _)) (hom_onmorphisms_is_postcomp U4 _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (internal_eval_nat _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_left.
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (! internal_postcomp_comp U1 _ _) @ _).
  refine (! internal_postcomp_comp U1 _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, _ · (f · _)) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (bifunctor_leftcomp E).
  refine (maponpaths (λ f, _ · _ ⊗^{E}_{l} f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite (bifunctor_leftcomp E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).  
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleftright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  rewrite (bifunctor_rightcomp E U1).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E (L R4)).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleftright E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  rewrite (monoidal_braiding_naturality_left E).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E (L R1)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  do 3 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f)) (pr12 k R4 _ _ f23) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f) ⊗^{E}_{r} _ · _) (! functor_comp K _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f) ⊗^{E}_{r} _ · _) (pr12 k R1 _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) ⊗^{E}_{r} _ · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatright E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (monoidal_associatornatright E).
  refine (assoc' _ _ _ @ _).
  rewrite (bifunctor_rightcomp E (L R4)).
  rewrite 3 assoc.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  do 2 refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (pr2 (pr222 k) R4 R1 R2)).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (compose _) (id_left _) @ _).
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (! maponpaths (compose _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (compose _) (id_left _) @ _).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  do 2 refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (compose _) (pr2 (pr222 k) R1 R4 R2) @ _).
  repeat rewrite assoc.
  refine (_ @ maponpaths (compose _) (id_left _)).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (functor_id L).
  rewrite <- (pr1 (monoidal_braiding_inverses C _ _)).
  rewrite (functor_comp L).
  rewrite (bifunctor_rightcomp E (K ((R4 ⊗_{ C} R1) ⊗_{ C} R2))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k R2 _ _ (sym_mon_braiding C R1 R4)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (compose _) keq).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  unfold monoidal_braiding_data_inv, monoidal_cat_tensor_pt.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (monoidal_associatorinvnatleft E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleft E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite (monoidal_braiding_naturality_right E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  rewrite (monoidal_braiding_naturality_right E).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatright E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite (monoidal_associatornatright E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  rewrite (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply map_on_two_paths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  rewrite <- (monoidal_braiding_naturality_left C).
  rewrite (bifunctor_leftcomp C R1).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  do 2 refine (_ @ assoc _ _ _).
  refine (! id_left _ @ _).
  rewrite <- (bifunctor_rightid C).
  rewrite <- (pr2 (monoidal_braiding_inverses C _ _)).
  rewrite (bifunctor_rightcomp C).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite 2 assoc.
  apply pathsinv0.
  rewrite <- (when_bifunctor_becomes_leftwhiskering C).
  rewrite <- (when_bifunctor_becomes_rightwhiskering C).
  apply sym_mon_hexagon_lassociator. (* completes subgoal *)
  repeat rewrite assoc.
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply map_on_two_paths.
  use (pathscomp0 (b:= (α^{E}_{_,_,_} · sym_mon_braiding E _ _))).
  repeat rewrite assoc'.
  apply maponpaths.
  repeat rewrite assoc.
  refine (_ @ ! sym_mon_tensor_lassociator E _ _ _).
  apply (maponpaths (postcompose _)).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc' _ _ _ @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (compose _) (sym_mon_tensor_rassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ id_left _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_right.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_leftid E _ _).
  apply maponpaths.
  exact (pr2 (monoidal_braiding_inverses E _ _)).
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator _ _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  repeat rewrite assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  apply maponpaths.
  repeat rewrite assoc.
  apply pathsinv0.
  apply sym_mon_hexagon_rassociator1.
  apply maponpaths.
  apply (fsym_respects_braiding L).
Qed.

Local Lemma double_glued_monoidal_laws_lemma6 {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧) (f23 : C⟦R2, R3⟧)
  (ϕ23 : E⟦U2, U3⟧) (ψ23 : E⟦X3, X2⟧) (eqphi : double_glued_mor_eq1 L K _ _ ((U2,, l2),, X2,, l2') ((U3 ,, l3),, X3,, l3') f23 ϕ23)
  (eqpsi : double_glued_mor_eq2 L K _ _ ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3') f23 ψ23)
  (dpb34 := tensor_doublePullback dpbs k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb134 := tensor_doublePullback dpbs k ((U1,, l1),, X1,, l1') ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4),,pr11 dpb34,, doublePullbackPrM dpb34)) :
  (doublePullbackPrM dpb134
     · # K (sym_mon_braiding C R4 (R1 ⊗_{ C} R2) · α^{ C }_{ R1, R2, R4} · R1 ⊗^{ C}_{l} (f23 ⊗^{ C}_{r} R4))) ⊗^{ E}_{r} U4
  · (K (monoidal_cat_tensor_pt R4 (R1 ⊗_{ C} R2)) ⊗^{ E}_{l} l4
     · (sym_mon_braiding E (K (R4 ⊗_{C} (R1 ⊗_{ C} R2))) (L R4) · pr1 k R4 (R1 ⊗_{ C} R2)))
  · (compose (C:=E) (# K (sym_mon_braiding C R2 R1)) (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1) · internal_precomp l2 (K R1))) =
  (doublePullbackPrR dpb134
   · (internal_precomp (sym_mon_braiding E U4 U3) X1 · internal_curry U4 U3 X1)) ⊗^{ E}_{r} U4
  · (internal_eval U4 (internal_hom U3 X1) · internal_precomp ϕ23 X1) · internal_postcomp U2 l1'.
Proof.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · (_ · f)) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackSqrRCommutes dpb134)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  simpl. (* necessary *)
  rewrite 2 internal_lam_precomp.
  do 2 refine (assoc _ _ _ @ _).
  rewrite 2 internal_lam_natural.
  unfold monoidal_cat_tensor_mor; rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  rewrite internal_lam_precomp.
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (id_right _)).
  refine (_ @ maponpaths (λ f, (_ · (_ · f)) ⊗^{E}_{r} _ · _) (internal_precomp_id _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_nat12 _ _ _)).
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  rewrite internal_lam_precomp.
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (curry_unit _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_postcomp_comp _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_postcomp_comp _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  rewrite <- (hom_onmorphisms_is_postcomp U4).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _)).
  rewrite id_left.
  apply (maponpaths (compose _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  do 2 refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (pr12 k R4 _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  simpl; unfold monoidal_cat_tensor_pt.
  refine (! maponpaths (compose _) (id_left _) @ _).
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (! maponpaths (compose _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (compose _) (id_left _) @ _).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  do 2 refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (compose _) (pr2 (pr222 k) R4 R2 R1) @ _).  
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} (_ · f) · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} (f · _) · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  rewrite eqphi.
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} (f · _) · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} (_ · f) · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} (_ · (f · _)) · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} (_ · f) · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} (_ · f) · _)) (fmonoidal_preservestensornatright L _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k R1 _ _ (f23 ⊗^{ C}_{r} R4)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (compose _) keq); clear keq.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  rewrite <- (bifunctor_leftid E).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_id K _)).
  rewrite <- (bifunctor_rightid C).
  rewrite <- (pr2 (monoidal_braiding_inverses C _ _)).
  rewrite (bifunctor_rightcomp C R1).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_comp K _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k R1 _ _ (sym_mon_braiding C R2 R4)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (compose _) keq); clear keq.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (monoidal_braiding_naturality_right E).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · (_ · (_ · (_ · f)))) (monoidal_braiding_naturality_left E _ _ _ _)).
  apply map_on_two_paths.
  do 2 apply maponpaths.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  refine (_ @ maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right C _ _ _ _)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite <- (when_bifunctor_becomes_rightwhiskering C).
  refine (_ @ ! maponpaths (λ f, f · _) (sym_mon_tensor_lassociator' C _ _ _)).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering C).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_left C).
  rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (_ @ ! maponpaths (λ f, f · _) (sym_mon_tensor_lassociator1 C _ _ _)).
  refine (! id_right _ @ _).
  repeat rewrite assoc'.
  do 2 apply maponpaths.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (pr1 (monoidal_associatorisolaw C _ _ _))).
  rewrite id_left.
  exact (! pr1 (monoidal_braiding_inverses C _ _)).
  do 3 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  rewrite (fsym_respects_braiding L).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · _ ⊗^{E}_{l} f · _) (tensor_sym_mon_braiding E _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (monoidal_associatornatleftright E _ _ _ _ _)).
  repeat rewrite assoc'.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (monoidal_associatornatleft E _ _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (maponpaths (λ f, _ · (f · _)) (sym_mon_tensor_rassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_right.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (sym_mon_tensor_lassociator1 E _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_right.
  refine (_ @ id_left _).
  repeat rewrite assoc.
  do 2 apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_rightid E _ _).
  apply maponpaths.
  exact (pr1 (monoidal_braiding_inverses E _ _)).
Qed.

Lemma double_glued_disp_associator_nat_leftwhisker {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  disp_associator_nat_leftwhisker (disp_monoidal_associator (double_glued_monoidal_data dpbs k)).
Proof.
  intros R1 R2 R3 R4 f34.
  intros ((U1, l1), (X1, l1')) ((U2, l2), (X2, l2')).
  intros ((U3, l3), (X3, l3')) ((U4, l4), (X4, l4')).
  intros ((ϕ34, eqphi), (ψ34, eqpsi)).
  apply double_glued_mor_eq; split;
    unfold transportb, transportf;
    induction (! associatorlaw_natleft (monoidal_associatorlaw C) R1 R2 R3 R4 f34); revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  apply (associatorlaw_natleft (monoidal_associatorlaw E)).
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply (compose (doublePullbackPrL _)).
    refine (compose _ (internal_uncurry _ _ _)).
    apply (internal_postcomp U1).
    apply (compose (doublePullbackPrL _)).
    exact (internal_postcomp U2 ψ34).
  }
  9 : {
    apply (compose (doublePullbackPrM _)).
    apply (# K).
    apply (compose (_ ⊗^{C}_{l} f34)).
    apply (α^{C}_{_,_,_}).
  }
  9 : {
    apply internal_lam.
    use doublePullbackArrow.
    refine (compose ( _ ⊗^{E}_{r} U3) _).
    apply (compose (doublePullbackPrL _)).
    apply (compose (internal_postcomp U1 (doublePullbackPrR _))).
    apply internal_swap_arg.
    apply (compose (_ ⊗^{E}_{l} ϕ34)).
    exact (internal_eval U4 _).
    refine (compose ( _ ⊗^{E}_{r} U3) _).
    apply (compose (doublePullbackPrM _)).
    apply (# K (sym_mon_braiding C _ _ · α^{C}_{_,_,_})).
    apply (compose (_ ⊗^{E}_{l} (ϕ34 · l4))).
    apply (compose (sym_mon_braiding E _ _)).
    exact (pr1 k R4 _).
    refine (compose ( _ ⊗^{E}_{r} U3) _).
    apply (compose (doublePullbackPrR _)).
    apply (compose (internal_precomp (sym_mon_braiding E _ _) _)).
    apply internal_curry.
    apply (compose (_ ⊗^{E}_{l} ϕ34)).
    exact (internal_eval U4 _).
    exact (double_glued_monoidal_laws_lemma1 dpbs L K k l1 l1' l2 l2' l3 l3' l4 l4' ϕ34 ψ34).
    exact (double_glued_monoidal_laws_lemma2 dpbs L K k l1 l1' l2 l2' l3 l3' l4 l4' ϕ34 ψ34).
  }
  
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (uncurry_nat3 _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (internal_postcomp_comp U1).
  rewrite (maponpaths (internal_postcomp U1) (assoc' _ _ _)).
  rewrite <- (internal_postcomp_comp U2).
  refine (! maponpaths (λ f, _ · (internal_postcomp U1 (_ · internal_postcomp U2 f) · _)) eqpsi @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp U1 (_ · f) · _)) (internal_postcomp_comp U2 _ _) @ _).
  rewrite (maponpaths (internal_postcomp U1) (assoc _ _ _)).
  refine (maponpaths (λ f, _ · (internal_postcomp U1 (f · _) · _)) (doublePullbackSqrLCommutes _) @ _).
  rewrite (maponpaths (internal_postcomp U1) (assoc' _ _ _)).
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _) @ _).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite (maponpaths (internal_postcomp U1) (assoc _ _ _)).
  rewrite assoc.
  rewrite 3 internal_lam_precomp.
  rewrite assoc.
  rewrite 2 internal_lam_postcomp.
  rewrite 2 internal_lam_natural.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  unfold internal_lam.
  rewrite 3 hom_onmorphisms_is_postcomp.
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose _) (uncurry_nat3 _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (uncurry_unit _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite (functor_comp K).
  refine (_ @ ! maponpaths (λ f, _ · (f · _))  (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f))  (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · (f · _))) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f))  (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f))  (pr12 k _ _ _ f34)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _))  (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (pr2 (pr222 k) R1 R2 R4)).
  unfold postcompose.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite (bifunctor_rightcomp E).
  refine (maponpaths (λ f, f · _ · _)  (assoc _ _ _) @ _).
  rewrite 2 assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite (monoidal_braiding_naturality_left E).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (λ f, f · _) (monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleft E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (bifunctor_leftcomp E).
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_pt.
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, _ · (f · _)) (sym_mon_tensor_lassociator' E _ _ _) @ _).
  do 4 refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite 2 assoc.
  refine (_ @ id_right _).
  rewrite <- (pr1 (monoidal_braiding_inverses E _ _)).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (compose _) (sym_mon_tensor_lassociator E _ _ _)).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (! id_left _ @ _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (pr1 (monoidal_associatorisolaw E _ _ _))).
  rewrite id_right.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  unfold monoidal_cat_tensor_pt; rewrite <- (bifunctor_rightid E).
  apply maponpaths.
  apply pathsinv0.
  exact (pr1 (monoidal_braiding_inverses E _ _)).
  rewrite internal_lam_postcomp.
  refine (_ @ ! maponpaths internal_lam (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, internal_lam (f · _) ) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths internal_lam (assoc _ _ _)).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine(_ @ internal_lam_natural _ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite internal_lam_precomp.
  rewrite assoc.
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite eqphi.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k (R1 ⊗_{ C} R2) _ _ f34); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (compose _) keq); clear keq.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite assoc.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  rewrite (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  apply (monoidal_braiding_naturality_right C). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! internal_postcomp_comp U1 _ _ @ _).
  apply maponpaths.
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply (monoidal_associatornatleft C). (*completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_pt, postcompose; simpl.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply doublePullbackArrowUnique.
  rewrite assoc'.
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _  @ _).
  rewrite <- (bifunctor_rightcomp E U3).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite <- (internal_postcomp_comp U1).
  refine (maponpaths (λ f, (internal_postcomp U1 f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  do 2 rewrite assoc'.
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (mon_closed_adj_natural_co E (internal_hom U1 X2) U3 U4 ϕ34)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_swap_arg_nat2. (* completes subgoal *)
  rewrite assoc'.
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _  @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite <- (bifunctor_rightcomp E U3).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite eqphi.
  rewrite (bifunctor_leftcomp E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  generalize (pr122 k (R1 ⊗_{ C} R2) _ _ f34); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (λ f, _ · (_ · f)) keq); clear keq.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  repeat rewrite assoc.
  do 2 apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  rewrite (monoidal_associatornatleft C).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  apply (monoidal_braiding_naturality_right C). (* completes subgoal *)
  rewrite assoc'.
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _  @ _).
  rewrite <- (bifunctor_rightcomp E U3).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc.
  rewrite <- (bifunctor_rightcomp E U3).
  rewrite <- internal_precomp_comp.
  simpl.
  rewrite (monoidal_braiding_naturality_right E).
  rewrite internal_precomp_comp.
  rewrite 2 (bifunctor_rightcomp E U3).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (mon_closed_adj_natural_co E _ U3 U4 ϕ34)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite <- (bifunctor_rightcomp E U3).
  refine (_ @ bifunctor_rightcomp E U3 _ _ _ _ _).
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (curry_nat12 _ _ _ @ _).
  apply maponpaths.
  rewrite internal_precomp_id.
  rewrite internal_postcomp_id.
  apply id_left. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _  @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite 2 assoc'.
  apply maponpaths.
  rewrite internal_postcomp_comp.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply uncurry_nat3. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _  @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  exact (! functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _  @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_precomp _ _ @ _).
  apply maponpaths.
  apply doublePullbackArrowUnique.
  rewrite assoc'.
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  reflexivity.
  rewrite assoc'.
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, f · _ ·_) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  apply maponpaths.
  exact (! functor_comp K _ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  refine (_ @ ! bifunctor_equalwhiskers E _ _ _ _ _ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  apply pathsinv0.
  apply (bifunctor_rightcomp E). (* completes subgoal *)
Qed.

Lemma double_glued_disp_associator_nat_rightwhisker {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
    {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  disp_associator_nat_rightwhisker (disp_monoidal_associator (double_glued_monoidal_data dpbs k)).
Proof.
  intros R1 R2 R3 R4 f12.
  intros ((U1, l1), (X1, l1')) ((U2, l2), (X2, l2')).
  intros ((U3, l3), (X3, l3')) ((U4, l4), (X4, l4')).
  intros ((ϕ12, eqphi), (ψ12, eqpsi)).
  apply double_glued_mor_eq; split;
    unfold transportb, transportf;
    induction (! associatorlaw_natright (monoidal_associatorlaw C) R1 R2 R3 R4 f12); revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  apply (associatorlaw_natright (monoidal_associatorlaw E)).
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply (compose (doublePullbackPrL _)).
    simpl.
    apply (compose (internal_postcomp _ (doublePullbackPrL _))).
    apply (compose (internal_precomp ϕ12 _)).
    apply internal_uncurry.
  }
  9 : {
    apply (compose (doublePullbackPrM _)).
    apply (# K).
    apply (compose (α^{C}_{_,_,_})).
    apply (f12 ⊗^{C}_{r} _).
  }
  9 : {
    apply internal_lam.
    use doublePullbackArrow.
    refine (compose ( _ ⊗^{E}_{r} U4) _).
    apply (compose (doublePullbackPrL _)).
    apply (compose (internal_postcomp U2 (doublePullbackPrR _))).
    apply (compose (internal_precomp ϕ12 _)).
    apply internal_swap_arg.
    exact (internal_eval U4 _).
    refine (compose ( _ ⊗^{E}_{r} U4) _).
    apply (compose (doublePullbackPrM _)).
    apply (# K (sym_mon_braiding C _ _ · α^{C}_{_,_,_} · f12 ⊗^{C}_{r} _)).
    apply (compose (_ ⊗^{E}_{l} l4)).
    apply (compose (sym_mon_braiding E _ _)).
    exact (pr1 k R4 _).
    simpl; unfold monoidal_cat_tensor_pt.
    refine (compose ( _ ⊗^{E}_{r} U4) _).
    apply (compose (doublePullbackPrR _)).
    apply (compose (internal_postcomp _ ψ12)).
    apply (compose (internal_precomp (sym_mon_braiding E _ _) _)).
    apply internal_curry.
    exact (internal_eval U4 _).
    exact (double_glued_monoidal_laws_lemma3 dpbs L K k l1 l1' l2 l2' l3 l3' l4 l4' f12 ϕ12 eqphi).
    exact (double_glued_monoidal_laws_lemma4 dpbs L K k l1 l1' l2 l2' l3 l3' l4 l4' f12 ϕ12 ψ12 eqphi eqpsi).
  }
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · (_ · f))) (uncurry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc _ _ _) @ _).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (internal_postcomp_comp U2).
  refine (maponpaths (λ f, _ · (internal_postcomp U2 f · _)) (doublePullbackSqrLCommutes _) @ _).
  rewrite (internal_postcomp_comp U2).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite 3 internal_lam_precomp.
  do 2 refine (assoc _ _ _ @ _).
  rewrite internal_lam_postcomp.
  rewrite internal_lam_precomp.
  refine (maponpaths (λ f, internal_lam f · _) (assoc _ _ _) @ _).
  rewrite 2 internal_lam_natural.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  unfold internal_lam.
  rewrite 3 hom_onmorphisms_is_postcomp.
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (uncurry_nat3 _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (uncurry_unit _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite (functor_comp K).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (pr2 (pr222 k) R1 R3 R4)).
  unfold postcompose.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleft E).
  rewrite 2 assoc'.
  rewrite (bifunctor_equalwhiskers E).
  unfold functoronmorphisms2; rewrite (bifunctor_leftcomp E).
  repeat refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! maponpaths (λ f, _ · ((f · _ · _) ⊗^{E}_{r} _ · _)) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  rewrite (bifunctor_rightcomp E (L R3)).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_associatornatleft E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  generalize (pr122 k (R3 ⊗_{ C} R4) _ _ f12); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (λ f, _ · _ ⊗^{E}_{l} f) keq); clear keq.
  refine (_ @ ! maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite eqphi.
  rewrite (bifunctor_leftcomp E).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleftright E).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite (bifunctor_rightcomp E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (maponpaths (compose _) (sym_mon_tensor_rassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  repeat rewrite assoc.
  do 2 apply (maponpaths (postcompose _)).
  refine (! id_right _ @ _).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr1 (monoidal_braiding_inverses E _ _)).
  refine (_ @ id_left _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (maponpaths (compose _) (sym_mon_tensor_rassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  repeat refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (pr1 (monoidal_braiding_inverses E _ _)) @ _).
  rewrite (bifunctor_leftid E).
  rewrite id_left.
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (pr1 (monoidal_braiding_inverses E _ _)) @ _).
  rewrite (bifunctor_rightid E).
  rewrite id_left.
  apply monoidal_associatorisolaw. (* completes subgoal *)
  rewrite internal_lam_postcomp.
  refine (_ @ ! maponpaths internal_lam (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  rewrite internal_lam_natural.
  apply maponpaths.
  apply (maponpaths (postcompose _)).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply assoc. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  apply internal_pre_post_comp_as_post_pre_comp. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (functor_comp K). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt, postcompose.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  rewrite <- (bifunctor_rightcomp E U4).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  apply internal_pre_post_comp_as_post_pre_comp. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  rewrite <- (bifunctor_rightcomp E U4).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  exact (! functor_comp K _ _). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  rewrite <- (bifunctor_rightcomp E U4).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  do 2 refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  do 2 rewrite <- (bifunctor_rightcomp E U4).
  apply maponpaths.
  do 2 refine (assoc' _ _ _ @ _).
  reflexivity.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  simpl.
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (uncurry_nat12 _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  rewrite internal_precomp_id.
  rewrite internal_postcomp_id.
  exact (id_left _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite (monoidal_associatornatright C).
  exact (! functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite internal_lam_postcomp.
  apply maponpaths.
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite internal_eval_nat.
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  apply internal_swap_arg_nat1. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (compose _) (pr12 k R4 _ _ (f12 ⊗^{ C}_{r} R3)) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).  
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_left C).
  rewrite assoc'.
  rewrite <- (monoidal_associatornatright C).
  apply assoc. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (bifunctor_rightcomp E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  rewrite <- (bifunctor_rightcomp E U4).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite <- (bifunctor_rightcomp E U4).
  apply maponpaths.
  rewrite assoc'.
  refine (! maponpaths (compose _) (curry_nat3 _ _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  apply internal_pre_post_comp_as_post_pre_comp. (* completes subgoal *)
Qed.

Definition double_glued_disp_associator_leftrightwhisker_compArrowL {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 R4 : ob C} {f23 : R2 --> R3}
  (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (dr4 : double_glued_cat L K R4)
  (df23 : dr2 -->[f23] dr3) (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                doublePullbackObject dP12,, doublePullbackPrM dP12) dr4)
  (X:= pr12 (double_glued_tensor_product dpbs k dr1 (double_glued_tensor_product dpbs k dr3 dr4))) :
  doublePullback_CompetitorArrowL dP12_4 X.
Proof.
  apply (compose (doublePullbackPrL _)).
  refine (compose _ (internal_uncurry _ _ _)).
  apply internal_postcomp.
  apply (compose (doublePullbackPrL _)).
  apply (internal_precomp (pr11 df23) _).
Defined.

Definition double_glued_disp_associator_leftrightwhisker_compArrowM {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 R4 : ob C} {f23 : R2 --> R3}
  (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (dr4 : double_glued_cat L K R4)
  (df23 : dr2 -->[f23] dr3) (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                doublePullbackObject dP12,, doublePullbackPrM dP12) dr4)
  (X:= pr12 (double_glued_tensor_product dpbs k dr1 (double_glued_tensor_product dpbs k dr3 dr4))) :
  doublePullback_CompetitorArrowM dP12_4 X.
Proof.
  apply (compose (doublePullbackPrM _)).
  apply (# K).
  apply (compose (α^{C}_{_,_,_})).
  exact (_ ⊗^{C}_{l} (f23 ⊗^{C}_{r} _)).
Defined.

Definition double_glued_disp_associator_leftrightwhisker_compArrowR {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 R4 : ob C} {f23 : R2 --> R3}
  (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (dr4 : double_glued_cat L K R4)
  (df23 : dr2 -->[f23] dr3) (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                doublePullbackObject dP12,, doublePullbackPrM dP12) dr4)
  (X:= pr12 (double_glued_tensor_product dpbs k dr1 (double_glued_tensor_product dpbs k dr3 dr4))) :
  doublePullback_CompetitorArrowR dP12_4 X.
Proof.
  set (U1 := pr11 dr1); set (l1 := pr21 dr1); set (X1 := pr12 dr1); set (l1' := pr22 dr1).
  set (U2 := pr11 dr2); set (l2 := pr21 dr2); set (X2 := pr12 dr2); set (l2' := pr22 dr2).
  set (U3 := pr11 dr3); set (l3 := pr21 dr3); set (X3 := pr12 dr3); set (l3' := pr22 dr3).
  set (U4 := pr11 dr4); set (l4 := pr21 dr4); set (X4 := pr12 dr4); set (l4' := pr22 dr4).
  set (ϕ23 := pr11 df23); set (ψ23 := pr12 df23).
  generalize (pr21 df23) (pr22 df23); simpl; intros eqphi eqpsi.
  apply internal_lam.
  use doublePullbackArrow.
  refine (compose ( _ ⊗^{E}_{r} _) _).
  apply (compose (doublePullbackPrL _ )).
  apply (compose (internal_postcomp _ (doublePullbackPrR _))).
  apply (internal_swap_arg _ _ _).
  apply (compose (internal_eval U4 _)).
  exact (internal_postcomp U1 ψ23).
  refine (compose ( _ ⊗^{E}_{r} _) _).
  apply (compose (doublePullbackPrM _ )).
  refine (# K _).
  refine (compose _ (R1 ⊗^{C}_{l} (f23 ⊗^{C}_{r} R4))).
  refine (compose _ (α^{C}_{_,_,_})).
  apply sym_mon_braiding.
  apply (compose (_ ⊗^{E}_{l} l4)).
  apply (compose (sym_mon_braiding E _ _)).
  apply (pr1 k). (* completes subgoal *)
  refine (compose ( _ ⊗^{E}_{r} _) _).
  apply (compose (doublePullbackPrR _ )).
  apply (compose (internal_precomp (sym_mon_braiding _ _ _) _)).
  apply internal_curry.
  apply (compose (internal_eval U4 _)).
  exact (internal_precomp ϕ23 _).
  exact (double_glued_monoidal_laws_lemma5 dpbs L K k l1 l1' l2 l2' l3 l3' l4 l4' f23 ϕ23 ψ23 eqphi eqpsi).
  exact (double_glued_monoidal_laws_lemma6 dpbs L K k l1 l1' l2 l2' l3 l3' l4 l4' f23 ϕ23 ψ23 eqphi eqpsi).
Defined.

Lemma double_glued_disp_associator_leftrightwhisker_compSqrL {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 R4 : ob C} {f23 : R2 --> R3}
  (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (dr4 : double_glued_cat L K R4)
  (df23 : dr2 -->[f23] dr3) (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                doublePullbackObject dP12,, doublePullbackPrM dP12) dr4) :
  doublePullback_CompetitorSqrL dP12_4 _
    (double_glued_disp_associator_leftrightwhisker_compArrowL dpbs k dr1 dr2 dr3 dr4 df23)
    (double_glued_disp_associator_leftrightwhisker_compArrowM dpbs k dr1 dr2 dr3 dr4 df23).
Proof.
  refine (_ @ ! maponpaths (λ f, _ · (_ · f)) (internal_precomp_comp _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (internal_lam_precomp _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_lam f · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (f · _) · _)) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_lam f · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, (compose (C:=E) _ (# K f)) · _) (monoidal_associatornatleftright C _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, (compose (C:=E) _ f) · _) (functor_comp K _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (internal_lam_natural _ _)).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ maponpaths (λ f, _ · (internal_lam f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (f · _) · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam f · _)) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_lam (_ · (f · _)) · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · f) · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · (f · _)) · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · (_ · f · _)) · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · (f · _)) · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · f) · _)) (assoc _ _ _)).
  generalize (pr122 k R4 _ _ (R1 ⊗^{ C}_{l} f23)); rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (λ f, _ · (internal_lam (_ · (_ · f)) · _)) keq); clear keq.
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · f) · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · (f · _)) · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · (_ · f · _)) · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · (_ · f ⊗^{E}_{r} _ · _)) · _)) (fmonoidal_preservestensornatleft L _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_lam (_ · (_ · f · _)) · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · (f · _)) · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · f) · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · (f · _)) · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · f) · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam f · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_lam (f · _) · _)) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam f · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (internal_lam_precomp _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_lam (_ · f) · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_lam (_ · f) · _)) (pr2 (pr222 k) R1 R3 R4)).
  unfold postcompose.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (uncurry_nat3 _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ f · _)) (assoc' _ _ _) @ _).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (maponpaths (λ f, _ · (internal_postcomp _ f · _)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ (f · _) · _)) (doublePullbackSqrLCommutes _) @ _).
  refine (maponpaths (λ f, _ · (internal_postcomp _ f · _)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  rewrite 5 internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  rewrite internal_lam_postcomp.
  rewrite internal_lam_natural.
  
  refine (internal_lam_uncurry _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  do 3 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  do 3 refine (assoc' _ _ _ @ _).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  exact (maponpaths (λ f, _ ⊗^{E}_{l} f) (pr21 df23)).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  apply cancel_postcomposition.
  apply (bifunctor_rightcomp E).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  apply maponpaths.
  apply  (bifunctor_leftcomp E).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ _ @ assoc _ _ _).
  2 : {
    apply cancel_postcomposition.
    refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
    apply maponpaths.
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    apply (bifunctor_leftcomp E).
  }
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_associatorinvnatleftright E).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorinvnatleft E).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_leftcomp E).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc _ _ _ @ _ @ assoc' _ _ _).
  2 : {
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (monoidal_braiding_naturality_left E).
  }
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (sym_mon_tensor_rassociator E _ _ _ @ _).
  do 3 refine (assoc' _ _ _ @ _).
  unfold monoidal_cat_tensor_mor; now rewrite (when_bifunctor_becomes_leftwhiskering E).
  apply cancel_postcomposition.
  apply (monoidal_associatorisolaw E).
  refine (id_left _ @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  apply pathsinv0.
  apply (sym_mon_hexagon_lassociator E).
  refine (_ @ id_left _).
  apply cancel_postcomposition.
  apply (monoidal_associatorisolaw E). (* completes subgoal *)
Qed.

Lemma double_glued_disp_associator_leftrightwhisker_compSqrR {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 R4 : ob C} {f23 : R2 --> R3}
  (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (dr4 : double_glued_cat L K R4)
  (df23 : dr2 -->[f23] dr3) (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                doublePullbackObject dP12,, doublePullbackPrM dP12) dr4) :
  doublePullback_CompetitorSqrR dP12_4 _
    (double_glued_disp_associator_leftrightwhisker_compArrowM dpbs k dr1 dr2 dr3 dr4 df23)
    (double_glued_disp_associator_leftrightwhisker_compArrowR dpbs k dr1 dr2 dr3 dr4 df23).
Proof.
  refine (_ @ ! internal_lam_postcomp _ _).
  refine (_ @ ! maponpaths internal_lam (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  do 2 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  do 3 apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ ).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply assoc. (* completes subgoal *)
Qed.

Lemma double_glued_disp_associator_leftrightwhisker_compTrianL {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 R4 : ob C} {f23 : R2 --> R3}
  (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (dr4 : double_glued_cat L K R4)
  (df23 : dr2 -->[f23] dr3) (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                  doublePullbackObject dP12,, doublePullbackPrM dP12) dr4)
  (arrL := (double_glued_assoc_data_comp2 dpbs k dr1 dr2 dr4) ·
             (double_glued_leftwhiskering_comp2 dpbs k dr1 (double_glued_tensor_product dpbs k dr2 dr4)
                (double_glued_tensor_product dpbs k dr3 dr4)
                (disp_rightwhiskering_on_morphisms (double_glued_disp_bifunctor_data dpbs L K k) R2 R3 R4 f23 dr2 dr3 dr4 df23))) :
  doublePullback_CompetitorTriangleL dP12_4 _ arrL
    (double_glued_disp_associator_leftrightwhisker_compArrowL dpbs k dr1 dr2 dr3 dr4 df23).
Proof.
  unfold double_glued_disp_associator_leftrightwhisker_compArrowL.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  simpl. (* absolutely necessary! *)
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _). (*completes subgoal *)
Qed.

Lemma double_glued_disp_associator_leftrightwhisker_compTrianM {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 R4 : ob C} {f23 : R2 --> R3}
  (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (dr4 : double_glued_cat L K R4)
  (df23 : dr2 -->[f23] dr3) (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                  doublePullbackObject dP12,, doublePullbackPrM dP12) dr4)
  (arrM := double_glued_assoc_data_comp2 dpbs k dr1 dr2 dr4 · double_glued_leftwhiskering_comp2 dpbs k dr1
             (double_glued_tensor_product dpbs k dr2 dr4) (double_glued_tensor_product dpbs k dr3 dr4)
             (disp_rightwhiskering_on_morphisms (double_glued_disp_bifunctor_data dpbs L K k) R2 R3 R4 f23 dr2 dr3 dr4 df23)) :
  doublePullback_CompetitorTriangleM dP12_4 _ arrM (double_glued_disp_associator_leftrightwhisker_compArrowM dpbs k dr1 dr2 dr3 dr4 df23).
Proof.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  exact (! functor_comp K _ _).
Qed.

Lemma double_glued_disp_associator_leftrightwhisker_compTrianR {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 R4 : ob C} {f23 : R2 --> R3}
  (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (dr4 : double_glued_cat L K R4)
  (df23 : dr2 -->[f23] dr3) (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                  doublePullbackObject dP12,, doublePullbackPrM dP12) dr4)
  (arrR := double_glued_assoc_data_comp2 dpbs k dr1 dr2 dr4 ·
             double_glued_leftwhiskering_comp2 dpbs k dr1 (double_glued_tensor_product dpbs k dr2 dr4)
             (double_glued_tensor_product dpbs k dr3 dr4)
             (disp_rightwhiskering_on_morphisms (double_glued_disp_bifunctor_data dpbs L K k) R2 R3 R4 f23 dr2 dr3 dr4 df23)) :
  doublePullback_CompetitorTriangleR dP12_4 _ arrR (double_glued_disp_associator_leftrightwhisker_compArrowR dpbs k dr1 dr2 dr3 dr4 df23).
Proof.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  simpl. unfold postcompose, monoidal_cat_tensor_pt.
  refine (internal_lam_natural _ _ @ _).
  unfold double_glued_disp_associator_leftrightwhisker_compArrowR.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (internal_swap_arg_nat3 _ _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! internal_postcomp_comp _ _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  exact (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  exact (! functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (id_right _)).
  rewrite <- internal_precomp_id.
  refine (_ @ maponpaths (compose _) (curry_nat12 _ _ _)).
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! internal_precomp_comp _ _ _ @ _ @ internal_precomp_comp _ _ _).
  apply (maponpaths (λ f, internal_precomp f _)).
  apply (monoidal_braiding_naturality_left E). (* completes subgoal *)
Qed. 
  
(*
Definition double_glued_disp_associator_leftrightwhisker_compArrows {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 R4 : ob C} {f23 : R2 --> R3}
  (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (dr4 : double_glued_cat L K R4)
  (df23 : dr2 -->[f23] dr3) (dP12 := tensor_doublePullback dpbs k dr1 dr2)
  (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                doublePullbackObject dP12,, doublePullbackPrM dP12) dr4)
  (X:= pr12 (double_glued_tensor_product dpbs k dr1 (double_glued_tensor_product dpbs k dr3 dr4))) :
  doublePullback_CompetitorArrows dP12_4 X.
Proof.
  use tpair.
  split3; simpl.
  exact (double_glued_disp_associator_leftrightwhisker_compArrowL dpbs k dr1 dr2 dr3 dr4 df23).
  exact (double_glued_disp_associator_leftrightwhisker_compArrowM dpbs k dr1 dr2 dr3 dr4 df23).
  exact (double_glued_disp_associator_leftrightwhisker_compArrowR dpbs k dr1 dr2 dr3 dr4 df23).
  split.
  exact (double_glued_disp_associator_leftrightwhisker_compSqrL dpbs k dr1 dr2 dr3 dr4 df23).
  exact (double_glued_disp_associator_leftrightwhisker_compSqrR dpbs k dr1 dr2 dr3 dr4 df23).
Defined. *)

Lemma double_glued_disp_associator_nat_leftrightwhisker {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
    {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) : 
  disp_associator_nat_leftrightwhisker
    (disp_monoidal_associator (double_glued_monoidal_data dpbs k)).
Proof.
  intros R1 R2 R3 R4 f23.
  intros dr1 dr2 dr3 dr4 df23.
  set (U1 := pr11 dr1); set (l1 := pr21 dr1); set (X1 := pr12 dr1); set (l1' := pr22 dr1).
  set (U2 := pr11 dr2); set (l2 := pr21 dr2); set (X2 := pr12 dr2); set (l2' := pr22 dr2).
  set (U3 := pr11 dr3); set (l3 := pr21 dr3); set (X3 := pr12 dr3); set (l3' := pr22 dr3).
  set (U4 := pr11 dr4); set (l4 := pr21 dr4); set (X4 := pr12 dr4); set (l4' := pr22 dr4).
  set (ϕ23 := pr11 df23); set (ψ23 := pr12 df23).
  generalize (pr21 df23) (pr22 df23); simpl; intros eqphi eqpsi.
  apply double_glued_mor_eq; split; unfold transportb, transportf;
    induction (! associatorlaw_natleftright (monoidal_associatorlaw C) R1 R2 R3 R4 f23).
  apply (monoidal_associatornatleftright E). (*completes subgoal *)
  (*
  set (dP12 := tensor_doublePullback dpbs k dr1 dr2).
  set (dP12_4 := tensor_doublePullback dpbs k
               ((pr11 dr1 ⊗_{ E} pr11 dr2,, pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2),,
                doublePullbackObject dP12,, doublePullbackPrM dP12) dr4).
  set (X:= double_glued_tensor_product dpbs k dr1 (double_glued_tensor_product dpbs k dr3 dr4)).*)
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply (double_glued_disp_associator_leftrightwhisker_compArrowL dpbs k dr1 dr2 dr3 dr4 df23) .
  }
  9 : {
    apply (double_glued_disp_associator_leftrightwhisker_compArrowM dpbs k dr1 dr2 dr3 dr4 df23) .
  }
  9 : {
    apply (double_glued_disp_associator_leftrightwhisker_compArrowR dpbs k dr1 dr2 dr3 dr4 df23) .
  }
  apply (double_glued_disp_associator_leftrightwhisker_compSqrL dpbs k dr1 dr2 dr3 dr4 df23).
  apply (double_glued_disp_associator_leftrightwhisker_compSqrR dpbs k dr1 dr2 dr3 dr4 df23).
  apply (double_glued_disp_associator_leftrightwhisker_compTrianL dpbs k dr1 dr2 dr3 dr4 df23).
  apply (double_glued_disp_associator_leftrightwhisker_compTrianM dpbs k dr1 dr2 dr3 dr4 df23).
  apply (double_glued_disp_associator_leftrightwhisker_compTrianR dpbs k dr1 dr2 dr3 dr4 df23).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  unfold double_glued_disp_associator_leftrightwhisker_compArrowL.
  apply maponpaths.
  refine (_ @ ! maponpaths (λ f, f · _) (internal_postcomp_comp _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  refine (uncurry_nat12 _ _ _ @ _).
  rewrite internal_precomp_id.
  now rewrite id_right.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  unfold double_glued_disp_associator_leftrightwhisker_compArrowM.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  exact (monoidal_associatornatleftright C _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_postcomp _ _ @ _).
  unfold double_glued_disp_associator_leftrightwhisker_compArrowR.
  apply maponpaths.
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  exact (assoc' _ _ _ @ assoc _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f)) (pr12 k R4 _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E U4 _ _ _ _ _ @ _).
  apply maponpaths.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  exact (maponpaths (compose _) (! monoidal_associatornatleftright C _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  now repeat rewrite assoc.
(* crashes here sometimes *)
Qed.


Lemma double_glued_disp_associator_isolaw {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
    {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  disp_associator_iso (disp_monoidal_associator (double_glued_monoidal_data dpbs k))
    (disp_monoidal_associatorinv (double_glued_monoidal_data dpbs k)).
Proof.
  intros R1 R2 R3.
  intros ((U1, l1), (X1, l1')) ((U2, l2), (X2, l2')) ((U3, l3), (X3, l3')).
  split; apply double_glued_mor_eq; split; unfold transportb, transportf;
    induction (! pr2 ((pr222 (monoidal_associatorlaw C)) R1 R2 R3)); try apply (monoidal_associatorisolaw E).
  refine (doublePullbackArrowUnique' _ _ (doublePullbackPrL _) (doublePullbackPrM _)(doublePullbackPrR _) _ _ _ _ _ _ @
            ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _); try exact (id_left _).
  apply doublePullbackSqrLCommutes.
  apply doublePullbackSqrRCommutes.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply internal_funext.
  unfold monoidal_cat_tensor_mor.
  intros A h.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  unfold internal_lam.
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (λ f, _ · f) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_left.
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  13 : {
    apply (compose ((doublePullbackPrL _) ⊗^{E}_{r} _)).
    apply (compose (internal_eval _ _)).
    apply doublePullbackPrL.
  }
  13 : {
    apply (compose ((doublePullbackPrM _) ⊗^{E} l1)).
    apply (compose (sym_mon_braiding E _ _)).
    apply (pr1 k).
  }
  13 : {
    apply (compose ((doublePullbackPrL _) ⊗^{E}_{r} _)).
    apply (compose (internal_eval _ _)).
    apply doublePullbackPrR.
  }
  set (dpb23 := tensor_doublePullback dpbs k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')).
  set (dpb123 := tensor_doublePullback dpbs k ((U1,, l1),, X1,, l1')
                   ((U2 ⊗_{ E} U3,, l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L) R2 R3),, pr11 dpb23,, doublePullbackPrM dpb23)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackSqrLCommutes dpb23) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackSqrLCommutes dpb123) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite internal_lam_precomp.
  unfold internal_lam.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _) @ _).
  exact (id_left _).
  set (dpb23 := tensor_doublePullback dpbs k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')).
  set (dpb123 := tensor_doublePullback dpbs k ((U1,, l1),, X1,, l1')
                   ((U2 ⊗_{ E} U3,, l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L) R2 R3),, pr11 dpb23,, doublePullbackPrM dpb23)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (doublePullbackSqrRCommutes dpb23)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackSqrLCommutes dpb123)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite internal_lam_precomp.
  unfold internal_lam.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _)).
  exact (! id_left _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat U1 _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E U1 _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ id_right _).
  rewrite hom_onmorphisms_is_postcomp.
  apply maponpaths.
  apply internal_uncurry_curry. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_id K _).
  apply maponpaths.
  apply (monoidal_associatorisolaw C). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (internal_lam_postcomp _ _) @ _).
  refine (maponpaths (λ f, (internal_lam f) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat U1 _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E U1 _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, f · _) (! internal_lam_natural _ _) @ _).
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  unfold internal_lam.
  refine (maponpaths (λ f, _ · (f · _)) (triangle_id_right_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_left.
  apply internal_swap_arg_involution. (* completes subgoal *)
  apply assoc'. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackSqrLCommutes _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_lam_precomp _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ id_left _).
  apply (maponpaths (postcompose _)).
  exact (triangle_id_left_ad (pr2 (pr2 E _)) _).
  apply assoc'. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_id K _).
  apply maponpaths.
  apply (monoidal_associatorisolaw C). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  rewrite internal_lam_postcomp.
  refine (maponpaths (λ f, internal_lam f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _) · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _) · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (! maponpaths (λ f, f · _) (internal_lam_natural _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (triangle_id_right_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_right.
  refine (_ @ id_right _).
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (internal_curry_uncurry _ _ _) @ _).
  rewrite id_left.
  refine (! internal_precomp_comp _ _ _ @ _ @ internal_precomp_id _ _).
  apply (maponpaths (λ f, internal_precomp f X1)).
  apply (monoidal_braiding_inverses E). (* completes subgoal *)
  induction (! pr1 ((pr222 (monoidal_associatorlaw C)) R1 R2 R3)).
  apply (monoidal_associatorisolaw E). (* completes subgoal *)
  induction (! pr1 ((pr222 (monoidal_associatorlaw C)) R1 R2 R3)).
  refine (doublePullbackArrowUnique' _ _ (doublePullbackPrL _) (doublePullbackPrM _) (doublePullbackPrR _) _ _ _ _ _ _ @
            ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _); try exact (id_left _).
  exact (doublePullbackSqrLCommutes _).
  exact (doublePullbackSqrRCommutes _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_postcomp _ _) @ _).
  refine (maponpaths (λ f, internal_lam f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _) · _) (! bifunctor_rightcomp E U1 _ _ _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (! maponpaths (λ f, f · _) (internal_lam_natural _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (triangle_id_right_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_right.
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  exact (internal_curry_uncurry _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_id K _).
  apply maponpaths.
  apply (monoidal_associatorisolaw C). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  apply internal_funext.
  intros A h.
  unfold monoidal_cat_tensor_mor.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply (compose ((doublePullbackPrR _) ⊗^{E}_{r} _)).
    apply (compose (internal_eval _ _)).
    exact (doublePullbackPrL _).
  }
  9 : {
    apply (compose ((doublePullbackPrM _) ⊗^{E}_{r} _)).
    apply (compose ((# K (sym_mon_braiding C _ _)) ⊗^{E} l3)).
    apply (compose (sym_mon_braiding E _ _)).
    apply (pr1 k).
  }
  9 : {
    apply (compose ((doublePullbackPrR _) ⊗^{E}_{r} _)).
    apply (compose (internal_eval _ _)).
    apply (doublePullbackPrR _).
  }
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackSqrLCommutes _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, f ⊗^{ E}_{r} U3 · _) (doublePullbackSqrRCommutes _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite internal_lam_precomp.
  apply internal_lam_tensor_eval. (* completes subgoal *)
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (doublePullbackSqrRCommutes _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} U3 · _) (doublePullbackSqrRCommutes _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite internal_lam_precomp.
  rewrite internal_lam_natural.
  refine (_ @ ! internal_lam_tensor_eval _).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  unfold monoidal_cat_tensor_mor.
  now rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite internal_lam_natural.
  refine (maponpaths (λ f, f · _) (internal_lam_tensor_eval _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_postcomp _ _) @ _).
  refine (maponpaths (λ f, internal_lam f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f) · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f · _)) · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _) · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (! maponpaths (λ f, f · _) (internal_lam_natural _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (triangle_id_right_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_right.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  apply internal_swap_arg_involution. (*completes subgoal *)
  refine (maponpaths (λ f, f · _ · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (internal_lam_tensor_eval _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_id K _).
  apply maponpaths.
  apply (monoidal_associatorisolaw C). (* completes subgoal *)
  rewrite internal_lam_natural.
  refine (maponpaths (λ f, f · _) (internal_lam_tensor_eval _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (map_on_two_paths compose (! bifunctor_rightcomp E _ _ _ _ _ _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (internal_precomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · (internal_precomp f _ · _)) (pr1 (monoidal_braiding_inverses E U3 U2)) @ _).
  rewrite internal_precomp_id.
  rewrite id_left.
  exact (internal_uncurry_curry _ _ _).
  apply assoc'. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, f ⊗^{ E}_{r} U3 · _) (doublePullbackSqrRCommutes _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite internal_lam_precomp.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  exact (internal_lam_tensor_eval _).
  apply assoc'. (*completes subgoal *)
Qed.

Lemma double_glued_disp_associator_law {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
    {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) : 
disp_associator_law (disp_monoidal_associator (double_glued_monoidal_data dpbs k))
  (disp_monoidal_associatorinv (double_glued_monoidal_data dpbs k)).
Proof.
  split4.
  exact (double_glued_disp_associator_nat_leftwhisker dpbs k).
  exact (double_glued_disp_associator_nat_rightwhisker dpbs k).
  exact (double_glued_disp_associator_nat_leftrightwhisker dpbs k).
  exact (double_glued_disp_associator_isolaw dpbs k).
Qed.


Lemma double_glued_disp_triangle_identity {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E)
    {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) : 
  disp_triangle_identity
    (disp_monoidal_leftunitor (double_glued_monoidal_data dpbs k))
    (disp_monoidal_rightunitor (double_glued_monoidal_data dpbs k))
    (disp_monoidal_associator (double_glued_monoidal_data dpbs k)).
Proof.
  intros R1 R2.
  intros ((U1, l1), (X1, l1')).
  intros ((U2, l2), (X2, l2')).
  apply double_glued_mor_eq; split;
    unfold transportb, transportf;
    induction (! monoidal_triangleidentity C R1 R2).
  apply (monoidal_triangleidentity E).
  simpl. (* necessary *)
  unfold double_glued_rightwhiskering_comp2. (* necessary *)
  apply (doublePullbackArrowUnique' (C:=E)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, internal_postcomp U1 f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  apply internal_uncurry_runitor. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply (monoidal_triangleidentity C). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply internal_funext.
  intros A h.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply (compose (doublePullbackPrM _ ⊗^{E}_{r} _)).
    apply (compose ((# K (sym_mon_braiding C _ _)) ⊗^{E} l2)).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose (pr1 k _ _)).
    apply (compose (C:=E) (# K ru^{C}_{R1})).
    apply internal_lam.
    apply (compose (_ ⊗^{E}_{l} l1)).
    apply (compose (sym_mon_braiding E _ _)).
    apply (pr1 k _ _).
  }
  9 : {
    apply (compose (doublePullbackPrM _ ⊗^{E}_{r} _)).
    apply (compose ((# K (sym_mon_braiding C _ _)) ⊗^{E} l2)).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose (pr1 k _ _)).
    apply (# K ru^{C}_{R1}).
  }
  9 : {
    apply (compose (doublePullbackPrR _ ⊗^{E}_{r} _)).
    apply (compose (internal_eval _ _)).
    apply internal_lam.
    apply (ru^{E}_{_}).
  }
  refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
  rewrite id_right.
  repeat rewrite assoc'.
  repeat apply maponpaths.
  exact (! internal_lam_precomp _ _).
  refine (assoc _ _ _ @ _ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  refine (internal_lam_natural _ _ @ _ @ ! maponpaths (λ f, f · _) (internal_lam_natural _ _)).
  refine (_ @ ! internal_lam_postcomp _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_rightunitornat E _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (doublePullbackSqrRCommutes _)).
  refine (_ @ ! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} I_{ E} · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite internal_lam_precomp.
  rewrite internal_lam_natural.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ ! maponpaths (λ f, f ⊗^{E}_{r} _ · _) (internal_lam_tensor_eval _)).
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  rewrite <- (bifunctor_leftid E).
  refine (! maponpaths (λ f, _ · (_ ⊗^{ E}_{l} f · _)) (functor_id K _) @ _).
  rewrite <- (pr1 (monoidal_leftunitorisolaw C _)).
  refine (maponpaths (λ f, _ · (_ ⊗^{ E}_{l} f · _)) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ ! pr1 (pr222 k) R1) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (sym_mon_braiding_lunitor E _) @ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  do 3 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, _ · (f · _)) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) _ (# K f)) (sym_mon_braiding_linvunitor C _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_id K _).
  apply maponpaths.
  apply (monoidal_rightunitorisolaw C). (* completes subgoal *)
  refine (maponpaths (λ f, f · _) (internal_lam_tensor_eval _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, (_ · internal_postcomp U1 f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackSqrLCommutes _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ assoc' _ _ _ @  _).
  apply maponpaths.
  rewrite internal_lam_precomp.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite internal_lam_postcomp.
  rewrite internal_lam_natural.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  unfold internal_lam; rewrite 2 hom_onmorphisms_is_postcomp.
  rewrite (internal_postcomp_comp U1).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ assoc' _ _ _ @  _).
  rewrite <- (hom_onmorphisms_is_postcomp U2).
  refine (! maponpaths (compose _) (internal_eval_nat _ _ _ _) @  _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} U2 · _) (internal_swap_arg_unit _ _ _) @  _).
  rewrite <- (hom_onmorphisms_is_postcomp U2).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_tensor_eval _) @  _).
  refine (assoc' _ _ _ @ maponpaths (compose _) (! internal_postcomp_comp U1 _ _) @ _).
  rewrite <- (hom_onmorphisms_is_postcomp U1).
  do 3 refine (_ @ assoc' _ _ _).
  refine (_ @ ! internal_lam_natural _ _).
  apply (maponpaths internal_lam).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @  _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @  _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @  _).
  refine (! maponpaths (λ f, _ · (_ · f) · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @  _).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @  _).
  refine (! maponpaths (λ f, _ · (f · _) · _) (bifunctor_leftcomp E _ _ _ _ _ _) @  _).
  rewrite (monoidal_braiding_naturality_right E).
  refine (maponpaths (λ f, _ · (f · _) · _) (bifunctor_leftcomp E _ _ _ _ _ _) @  _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @  _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @  _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleftright E _ _ _ _ _) @  _).
  refine (assoc' _ _ _ @ _).
  do 2 refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (pr12 k R2 _ _ _)).
  refine (assoc _ _ _ @ _ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E  _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E  _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (pr2 (monoidal_associatorisolaw E _ _ _))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr1 (monoidal_braiding_inverses E _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  do 2 refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (pr2 (pr222 k) R2 R1 I_{C})).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (pr12 k R1 _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (compose _) (id_left _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  refine (! maponpaths (compose _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (compose _) (id_left _) @ _).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr1 (monoidal_braiding_inverses E _ _)).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  do 2 refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (compose _) (pr2 (pr222 k) R1 R2 I_{C}) @ _).
  do 4 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatleftright E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  rewrite (monoidal_braiding_naturality_left E).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  do 4 refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 4 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_associatorinvnatright E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · f) ⊗^{ E}_{r} _ · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, (f ⊗^{ E}_{r} _) ⊗^{ E}_{r} _ · _) (functor_comp K _ _)).
  refine (_ @ maponpaths (λ f, (# K f ⊗^{ E}_{r} _) ⊗^{ E}_{r} _ · _) (monoidal_braiding_naturality_left C _ _ _ _)).
  do 5 refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_leftid E _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_id K _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (bifunctor_rightid C _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K (f ⊗^{C}_{r} _) · _)) (pr2 (monoidal_braiding_inverses C _ _))).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (bifunctor_rightcomp C _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_comp K _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k I_{C} _ _ (sym_mon_braiding C R2 R1)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (compose _) keq); clear keq.
  refine (_ @ assoc' _ _ _).
  repeat refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  rewrite <- (fsym_respects_braiding L).
  refine (_ @ ! maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (monoidal_associatorinvnatleft E _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f ⊗^{ E}_{r} _ · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply map_on_two_paths.
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  etrans.
  rewrite <- (when_bifunctor_becomes_leftwhiskering C).
  refine (! maponpaths (compose _) (mon_runitor_triangle _ _) @ _).
  refine (_ @ id_left _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  apply (monoidal_associatorisolaw C).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_left C _ _ _ _)).
  rewrite <- (when_bifunctor_becomes_leftwhiskering C).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (mon_runitor_triangle _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (pr1 (monoidal_associatorisolaw C _ _ _))).
  rewrite id_right.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (monoidal_rightunitornat C _ _ _)).
  refine (! id_right _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_inverses C).
  do 3 refine ( _ @ assoc' _ _ _).
  do 5 refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  use (pathscomp0 (b:= α^{E}_{_,_,_} · sym_mon_braiding E _ _)).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, _ · (_ · (f · _))) (sym_mon_tensor_lassociator' E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E).
  repeat rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · (f · _)) (sym_mon_tensor_rassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E); rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_right.
  do 2 refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ ⊗^{ E}_{l} f · _)) (pr2 (monoidal_braiding_inverses E _ _)) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_leftid E _ _) @ _).
  rewrite id_left.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightid E _ _).
  apply maponpaths.
  apply (monoidal_braiding_inverses E).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (sym_mon_hexagon_rassociator1 E _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (sym_mon_tensor_lassociator1 E _ _ _)).
  repeat rewrite assoc'.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, f ⊗^{E}_{r} _ · _) (pr2 (monoidal_braiding_inverses E _ _))).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightid E _ _)).
  rewrite id_left.
  apply maponpaths.
  refine (! id_right _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorisolaw E). (* completes subgoal *)
  refine (maponpaths (λ f, f · _) (internal_lam_tensor_eval _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  do 3 refine (assoc _ _ _ @ _).
  refine (_ @ maponpaths (compose _) (pr12 k R2 _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  rewrite <- (when_bifunctor_becomes_leftwhiskering C).
  refine (! maponpaths (compose _) (mon_triangle _ _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering C).
  apply (monoidal_braiding_naturality_left C). (* completes subgoal *)
  refine (maponpaths (λ f, f · _) (internal_lam_tensor_eval _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, f ⊗^{E}_{r} _ · _) (internal_precomp_comp _ _ _) @ _).
  rewrite (sym_mon_braiding_lunitor E).
  refine (_ @ ! internal_eval_nat _ _ _ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (internal_lam_natural _ _ @ _).
  rewrite internal_lam_natural.
  unfold monoidal_cat_tensor_mor; rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, internal_lam (internal_lam f)) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, internal_lam (internal_lam (f · _))) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (internal_lam f)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (internal_lam (_ · f))) (mon_closed_adj_natural_co E _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (internal_lam f)) (assoc _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  refine (! maponpaths (λ f, internal_lam (internal_lam (_ · f · _))) (mon_runitor_triangle _ _) @ _).
  refine (maponpaths (λ f, internal_lam (internal_lam (f · _))) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (internal_lam (f · _ · _))) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_left.
  refine (! maponpaths (λ f, internal_lam (internal_lam f)) (monoidal_rightunitornat _ _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (! maponpaths internal_lam (internal_lam_natural _ _) @ _).
  refine (maponpaths (compose _) (functor_comp _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (triangle_id_right_ad (pr2 (pr2 E _)) _) @ _).
  exact (id_left _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{ E}_{r} _ · _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, (_ · internal_postcomp _ f) ⊗^{ E}_{r} _ · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{ E}_{r} _ · _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (f · _) ⊗^{ E}_{r} _ · _) (doublePullbackSqrRCommutes _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite 2 internal_lam_precomp.
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite internal_lam_postcomp.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_tensor_eval _) @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  exact (assoc' _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{ E}_{r} _ · _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, (_ · internal_postcomp _ f) ⊗^{ E}_{r} _ · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{ E}_{r} _ · _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (f · _) ⊗^{ E}_{r} _ · _) (doublePullbackSqrRCommutes _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite internal_lam_precomp.
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite internal_lam_postcomp.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_tensor_eval _) @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  exact (assoc' _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, (internal_postcomp _ f) ⊗^{ E}_{r} _ · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite <- hom_onmorphisms_is_postcomp.
  apply pathsinv0.
  apply internal_eval_nat. (* completes subgoal *)
Qed.

