(************************************

In this file the remaining monoidal laws are proven, namely:

- triangle identity
- pentagon identity

for proofs of the other laws, see file monoidal_laws1.v

************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

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
Require Import double_gluing.monoidal.monoidal_laws1.


Lemma double_glued_monoidal_laws {E C : sym_mon_closed_cat} (pb : Pullbacks E)
  (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) :
  disp_monoidal_laws (double_glued_monoidal_data pb L K k).
Proof.
Admitted.

(*
Local Lemma double_glued_monoidal_laws_lemma7  {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E)
  (K : functor C (E^opp)) (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧)
  (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧)
  (dpb34 := tensor_doublePullback pb k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb234 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4),,
                                                                        pr11 dpb34,,  doublePullbackPrM dpb34))
  (dpb1234 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
                      ((U2 ⊗_{ E} (U3 ⊗_{ E} U4),, l2 ⊗^{ E} (l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4) · (fmonoidal_preservestensordata L) R2 (R3 ⊗_{ C} R4)),,
                         pr11 dpb234,,  doublePullbackPrM dpb234)) :  
   ((doublePullbackPrL dpb1234      
    · (internal_postcomp U1
         (doublePullbackPrR dpb234
          · internal_precomp (sym_mon_braiding E U4 U3) X2 · internal_curry U4 U3 X2)
       · internal_swap_arg U1 (internal_hom U3 X2) U4)) ⊗^{ E}_{r} U4
   · (internal_eval U4 (internal_hom U1 (internal_hom U3 X2)) · internal_swap_arg U1 X2 U3)) ⊗^{ E}_{r} U3
  · internal_eval U3 (internal_hom U1 X2) · internal_postcomp U1 l2' =
  (doublePullbackPrM dpb1234 ⊗^{ E}_{r} U4)  ⊗^{ E}_{r} U3
  · (α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))), U4, U3}
     · K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗^{ E}_{l} sym_mon_braiding E U4 U3
     · sym_mon_braiding E (K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4)))) (monoidal_cat_tensor_pt U3 U4)
     · ((l3 ⊗^{ E} l4 · fmonoidal_preservestensordata L R3 R4)
        ⊗^{ E} # K (sym_mon_braiding C (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2) · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4})
        · pr1 k (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2)))
  · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2)).
Proof.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, ((f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, ((_ · f) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, ((f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, ((_ · f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, ((_ · internal_postcomp _ f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, ((_ · internal_postcomp _ (_ · f) · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _)
            (! curry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, ((_ · internal_postcomp _ f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, ((_ · internal_postcomp _ (f · _) · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (maponpaths (λ f, ((_ · internal_postcomp _ (f · _) · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, ((_ · internal_postcomp _ f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, ((_ · internal_postcomp _ (f · _) · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _)
            (! doublePullbackSqrRCommutes dpb234) @ _).
  refine (maponpaths (λ f, ((_ · internal_postcomp _ f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, ((_ · f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, ((f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, ((f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (doublePullbackSqrLCommutes dpb1234) @ _).
  refine (maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite 3 internal_lam_precomp.
  repeat rewrite internal_lam_natural.
  refine (maponpaths (λ f, ((_ · (internal_postcomp _ f · _)) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite internal_lam_precomp, internal_lam_postcomp.
  refine (maponpaths (λ f, ((internal_lam f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite internal_lam_natural.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt.
  repeat rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, ((internal_lam f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (internal_lam_curry _) @ _).
  refine (maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (internal_lam_lam_swap _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (internal_lam_postcomp _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (internal_lam_tensor_eval _) @ _).
  rewrite internal_lam_natural.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (internal_lam_lam_swap _) @ _).
  refine (internal_lam_tensor_eval _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E U1).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f,  _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f,  _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
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
  refine (_ @ maponpaths (compose _) (pr2 (pr222 k) (R3 ⊗_{C} R4) R1 R2)).
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (! pr12 k _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_rightid E _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (! pr1 (monoidal_braiding_inverses E _ _ )) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  do 2 refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (! pr2 (pr222 k) R1 (R3 ⊗_{ C} R4) R2) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (id_left _)).
  refine (_ @ maponpaths (λ f,  _ · (f · _)) (bifunctor_leftid E _ _)).
  refine (_ @ maponpaths (λ f,  _ · (_ ⊗^{E}_{l} f · _)) (functor_id K _)).
  refine (_ @ maponpaths (λ f,  _ · (_ ⊗^{E}_{l} # K f · _)) (bifunctor_rightid C _ _)).
  refine (_ @ maponpaths (λ f,  _ · (_ ⊗^{E}_{l} (# K (f ⊗^{C}_{r} _)) · _)) (pr2 (monoidal_braiding_inverses C _ _))).
  refine (_ @ maponpaths (λ f,  _ · (_ ⊗^{E}_{l} # K f · _)) (! bifunctor_rightcomp C _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f,  _ · (_ ⊗^{E}_{l} f · _)) (! functor_comp K _ _)).
  refine (_ @ maponpaths (λ f,  _ · (f · _)) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k R2 _ _ (sym_mon_braiding C (R3 ⊗_{ C} R4) R1)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (compose _) (! keq)); clear keq.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  unfold monoidal_cat_tensor_pt.
  do 6 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E U1 _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (! monoidal_associatorinvnatleft E _ _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _ · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  do 5 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @  _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @  _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @  _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @  _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply map_on_two_paths.
  do 5 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f) ⊗^{E}_{r} _ · _) (! monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f · _) ⊗^{E}_{r} _ · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · _ ⊗^{E}_{l} f · _) ⊗^{E}_{r} _ · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f · _) ⊗^{E}_{r} _ · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) ⊗^{E}_{r} _ · _) (monoidal_associatornatleft E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · _ ⊗^{E}_{l} f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  do 4 refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 3 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  rewrite <- (fsym_respects_braiding L).
  do 6 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply (maponpaths (postcompose _)).
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (! monoidal_associatorinvnatleftright E _ _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f ⊗^{E}_{r} _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (pathscomp0 (b:= α^{E}_{_,_,_} ⊗^{E}_{r} _ · sym_mon_braiding E _ _ · αinv^{E}_{_,_,_} · _ ⊗^{E}_{l} (sym_mon_braiding E _ _) · sym_mon_braiding E _ _ · αinv^{E}_{_,_,_})).
  do 2 refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite 2 assoc.
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  apply pathsinv0.
  apply sym_mon_hexagon_rassociator. (*completes subgoal *)
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, _ · f · _) (sym_mon_tensor_rassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E), (when_bifunctor_becomes_leftwhiskering E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  rewrite id_right.
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (compose _) (assoc' _ _ _) @ assoc _ _ _ @ _).
  assert (α^{E}_{K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))),U4,U3} ⊗^{ E}_{r} L R1 · α^{E}_{K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))),U4 ⊗_{ E} U3,L R1} = α^{E}_{_,_,_} · α^{E}_{_,_,_} · (_ ⊗^{E}_{l} αinv^{E}_{_,_,_})) as penteq.
  refine (_ @ maponpaths (λ f, f · _) (monoidal_pentagonidentity E _ _ _ _)).
  refine (! id_right _ @ _).
  repeat rewrite assoc'.
  repeat apply maponpaths.
  refine (! bifunctor_leftid E _ _ @ _ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorisolaw E).
  refine (maponpaths (λ f, f · _) penteq @ _); clear penteq.
  do 2 refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  assert (αinv^{E}_{K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))),L R1,U4} ⊗^{ E}_{r} U3 · α^{E}_{K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗_{ E} L R1,U4,U3} = α^{E}_{_,_,_} · _ ⊗^{E}_{l} α^{E}_{_,_,_} · αinv^{E}_{_,_,_}) as penteq.
  refine (! id_right _ @ _).
  rewrite <- (pr1 (monoidal_associatorisolaw E _ _ _)).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_pentagonidentity E _ _ _ _) @ _ @ id_left _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightid E _ _).
  apply maponpaths.
  apply (monoidal_associatorisolaw E).
  refine (_ @ maponpaths (compose _) (! penteq )); clear penteq.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite (bifunctor_rightcomp E U3).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (monoidal_associatornatleftright E _ _ _ _ _)).
  refine (_ @ assoc _ _ _ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  assert (αinv^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗_{ E} U4, L R1, U3}
     · (α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))), U4, L R1} ⊗^{ E}_{r} U3
     · α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))), U4 ⊗_{ E} L R1, U3}) = α^{E}_{_,_,_} · _ ⊗^{E}_{l} αinv^{ E }_{_,_,_}) as penteq.
  refine (_ @ id_left _).
  rewrite <- (pr2 (monoidal_associatorisolaw E _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_pentagonidentity E _ _ _ _)).
  refine (! id_right _ @ _).
  repeat rewrite assoc'.
  repeat apply maponpaths.
  refine (! bifunctor_leftid E _ _ @ _ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  exact (! (pr1 (monoidal_associatorisolaw E _ _ _))).
  refine (_ @ maponpaths (λ f, _ · f · _) ( ! penteq)); clear penteq.
  refine (_ @ assoc _ _ _ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_associatornatleft E _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ map_on_two_paths compose (bifunctor_leftcomp E _ _ _ _ _ _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (maponpaths (compose _) (sym_mon_tensor_rassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E), (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ id_left _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  apply (monoidal_associatorisolaw E). (* completes subgoal *)
  apply maponpaths.
  refine (_ @ maponpaths (compose (C:=E) _ ) (functor_comp K _ _) @ assoc _ _ _).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (! sym_mon_hexagon_lassociator C _ _ _ @ assoc' _ _ _) @ assoc _ _ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering C), (when_bifunctor_becomes_leftwhiskering C).
  refine (! id_left _ @ _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  apply pathsinv0.
  refine (! bifunctor_rightcomp C _ _ _ _ _ _ @ _ @ bifunctor_rightid C _ _).
  apply maponpaths.
  apply (monoidal_braiding_inverses C). 
Qed.

Lemma double_glued_monoidal_laws_lemma8  {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E)
  (K : functor C (E^opp)) (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧)
  (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧)
  (dpb34 := tensor_doublePullback pb k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb234 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4),,
                                                                        pr11 dpb34,,  doublePullbackPrM dpb34))
  (dpb1234 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
                      ((U2 ⊗_{ E} (U3 ⊗_{ E} U4),, l2 ⊗^{ E} (l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4) · (fmonoidal_preservestensordata L) R2 (R3 ⊗_{ C} R4)),,
                         pr11 dpb234,,  doublePullbackPrM dpb234)) :  
  (doublePullbackPrM dpb1234 ⊗^{ E}_{r} U4) ⊗^{ E}_{r} U3
  · (α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))), U4, U3} · K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗^{ E}_{l} sym_mon_braiding E U4 U3
     · sym_mon_braiding E (K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4)))) (monoidal_cat_tensor_pt U3 U4)
     · ((l3 ⊗^{ E} l4 · fmonoidal_preservestensordata L R3 R4)
        ⊗^{ E} # K (sym_mon_braiding C (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2) · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4}) · pr1 k (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2)))
  · (compose (C:=E) (# K (sym_mon_braiding C R2 R1)) (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1) · internal_precomp l2 (K R1))) =
  ((doublePullbackPrR dpb1234
    · (internal_precomp (sym_mon_braiding E U4 (U2 ⊗_{ E} U3) · α^{ E }_{ U2, U3, U4}) X1 · internal_curry U4 (U2 ⊗_{ E} U3) X1)) ⊗^{ E}_{r} U4
   · (internal_eval U4 (internal_hom (U2 ⊗_{ E} U3) X1) · (internal_precomp (sym_mon_braiding E U3 U2) X1 · internal_curry U3 U2 X1))) ⊗^{ E}_{r} U3
  · internal_eval U3 (internal_hom U2 X1) · internal_postcomp U2 l1'.
Proof.
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _) @ assoc _ _ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
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
  refine (_ @ maponpaths (λ f, ((f · _) ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (doublePullbackSqrRCommutes dpb1234)).
  refine (_ @ maponpaths (λ f, (f ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite 2 internal_lam_precomp.
  rewrite 3 internal_lam_natural.
  refine (_ @ maponpaths (λ f, (f ⊗^{ E}_{r} U4 · _) ⊗^{ E}_{r} U3  · _) (assoc' _ _ _)).
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

Lemma double_glued_monoidal_laws_lemma9  {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E)
  (K : functor C (E^opp)) (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧)
  (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧)
  (dpb34 := tensor_doublePullback pb k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb234 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4),,
                                                                        pr11 dpb34,,  doublePullbackPrM dpb34))
  (dpb1234 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
                      ((U2 ⊗_{ E} (U3 ⊗_{ E} U4),, l2 ⊗^{ E} (l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4) · (fmonoidal_preservestensordata L) R2 (R3 ⊗_{ C} R4)),,
                         pr11 dpb234,,  doublePullbackPrM dpb234)) :
   (doublePullbackPrL dpb1234
   · (internal_postcomp U1 (doublePullbackPrL dpb234 · (internal_postcomp U2 (doublePullbackPrR dpb34) · internal_swap_arg U2 X3 U4))
      · internal_swap_arg U1 (internal_hom U2 X3) U4)) ⊗^{ E}_{r} U4
  · (internal_eval U4 (internal_hom U1 (internal_hom U2 X3)) · internal_uncurry U1 U2 X3) · internal_postcomp (U1 ⊗_{ E} U2) l3' =
  (doublePullbackPrM dpb1234
   · # K (sym_mon_braiding C R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3) · (α^{ C }_{ R1 ⊗_{ C} R2, R3, R4} · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4}))) ⊗^{ E} l4
  · (sym_mon_braiding E (K (monoidal_cat_tensor_pt R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3))) (L R4) · pr1 k R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3))
  · (internal_lam (sym_mon_braiding E (K ((R1 ⊗_{ C} R2) ⊗_{ C} R3)) (L (R1 ⊗_{ C} R2)) · pr1 k (R1 ⊗_{ C} R2) R3)
       · internal_precomp (l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2) (K R3)).
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
  refine (maponpaths (λ f, f ⊗^{E}_{r} U4 · _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ assoc' _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (! internal_postcomp_comp U1 _ _ @ _).
  refine (maponpaths (internal_postcomp U1) _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (! internal_postcomp_comp U2 _ _ @ _).
  refine (maponpaths (internal_postcomp U2) _).
  exact (! doublePullbackSqrRCommutes dpb34).
  refine (maponpaths (compose _) (internal_postcomp_comp U2 _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes dpb234) @ _).
  apply assoc'.
  apply assoc'.
  apply (internal_postcomp_comp U1 _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes dpb1234) @ _).
  apply assoc'.
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ assoc' _ _ _ @ _).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
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
  refine (maponpaths (λ f, _ · ((f ⊗^{ E}_{r} U4) ⊗^{ E}_{r} U2 · _)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{ E}_{r} U2 · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
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
  refine (maponpaths (λ f, f ⊗^{ E}_{r} U4) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply assoc'.
  apply assoc.
  apply (bifunctor_rightcomp E U4).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} U4) (assoc' _ _ _ @ _) @ _).
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
  apply (bifunctor_rightcomp E U4).
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
  refine (maponpaths (λ f, _ · (f ⊗^{ E}_{r} U4 · _)) (assoc' _ _ _ @ _) @ _).
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
  refine (maponpaths (λ f, f ⊗^{ E}_{r} U2) _ @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} U4) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
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
  refine (maponpaths (λ f, f ⊗^{ E}_{r} U4) (assoc _ _ _ @ _)).
  apply tensor_sym_mon_braiding.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} U4) (assoc' _ _ _ @ _)).
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
  rewrite 2 (bifunctor_rightcomp E U4).
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

Local Definition double_glued_monoidal_laws_lemma10_type {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K)
  {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧)
  (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧) : UU.
Proof.
  set (dpb34 := tensor_doublePullback pb k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4')).
  set (dpb234 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4),, pr11 dpb34,,  doublePullbackPrM dpb34)).
  set (dpb1234 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
                    ((U2 ⊗_{ E} (U3 ⊗_{ E} U4),,
                        l2 ⊗^{ E} (l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L) R3 R4) · (fmonoidal_preservestensordata L) R2 (R3 ⊗_{ C} R4)),,
                       pr11 dpb234,,  doublePullbackPrM dpb234)).
  set (dpb12 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')).
  exact ( (doublePullbackPrM dpb1234
   · # K (sym_mon_braiding C R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3) · (α^{ C }_{ R1 ⊗_{ C} R2, R3, R4} · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4}))) ⊗^{ E} l4
  · (sym_mon_braiding E (K (R4 ⊗_{C} ((R1 ⊗_{ C} R2) ⊗_{ C} R3))) (L R4) · pr1 k R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3))
  · (compose (C:=E) (# K (sym_mon_braiding C R3 (R1 ⊗_{ C} R2)))
     (internal_lam ((pr121 E) (K (R3 ⊗_{ C} (R1 ⊗_{ C} R2))) (L R3) · pr1 k R3 (R1 ⊗_{ C} R2)) · internal_precomp l3 (K (R1 ⊗_{ C} R2)))) =
  internal_lam
    (doublePullbackArrow dpb12 ((pr11 dpb1234 ⊗_{E} U4) ⊗_{E} U3)
       (((doublePullbackPrL dpb1234
          · (internal_postcomp U1
               (doublePullbackPrR dpb234
                · internal_precomp (sym_mon_braiding E U4 U3) X2 · internal_curry U4 U3 X2) · internal_swap_arg U1 (internal_hom U3 X2) U4)) ⊗^{ E}_{r} U4
         · (internal_eval U4 (internal_hom U1 (internal_hom U3 X2)) · internal_swap_arg U1 X2 U3)) ⊗^{ E}_{r} U3 · internal_eval U3 (internal_hom U1 X2))
       ((doublePullbackPrM dpb1234 ⊗^{ E}_{r} U4) ⊗^{ E}_{r} U3
        · (α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))), U4, U3} · K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗^{ E}_{l} sym_mon_braiding E U4 U3
           · sym_mon_braiding E (K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4)))) (U3 ⊗_{E} U4)
           · ((l3 ⊗^{ E} l4 · fmonoidal_preservestensordata L R3 R4)
              ⊗^{ E} # K (sym_mon_braiding C (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2) · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4}) · pr1 k (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2))))
       (((doublePullbackPrR dpb1234
          · (internal_precomp (sym_mon_braiding E U4 (U2 ⊗_{ E} U3) · α^{ E }_{ U2, U3, U4}) X1 · internal_curry U4 (U2 ⊗_{ E} U3) X1)) ⊗^{ E}_{r} U4
         · (internal_eval U4 (internal_hom (U2 ⊗_{ E} U3) X1) · (internal_precomp (sym_mon_braiding E U3 U2) X1 · internal_curry U3 U2 X1))) ⊗^{ E}_{r} U3
        · internal_eval U3 (internal_hom U2 X1)) (double_glued_monoidal_laws_lemma7 pb L K k l1 l1' l2 l2' l3 l3' l4 l4')
       (double_glued_monoidal_laws_lemma8 pb L K k l1 l1' l2 l2' l3 l3' l4 l4'))
  · internal_postcomp U3 (doublePullbackPrM dpb12)).
Defined.


Local Lemma double_glued_monoidal_laws_lemma10  {E C : sym_mon_closed_cat} (pb : Pullbacks E)
  (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K)
  {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧)
  (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧) :
  double_glued_monoidal_laws_lemma10_type pb L K k l1 l1' l2 l2' l3 l3' l4 l4'.
Proof.
  refine (_ @ ! internal_lam_postcomp _ _).
  refine (_ @ maponpaths internal_lam (! doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} U3) (assoc' _ _ _ @ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E U4 _ _ _ _ _) @ _).
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
  refine (bifunctor_rightcomp E U3 _ _ _ _ _ @ _).
  refine (maponpaths (compose _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
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


Lemma double_glued_disp_triangle_identity {E C : sym_mon_closed_cat} (pb : Pullbacks E)
    (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) : 
  disp_triangle_identity
    (disp_monoidal_leftunitor (double_glued_monoidal_data pb L K k))
    (disp_monoidal_rightunitor (double_glued_monoidal_data pb L K k))
    (disp_monoidal_associator (double_glued_monoidal_data pb L K k)).
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
  apply (doublePullbackArrowUnique (C:=E)).
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
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
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
  show_id_type.
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
  rewrite doublePullbackSqrMCommutes.
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
  rewrite doublePullbackSqrMCommutes.
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

Local Lemma double_glued_monoidal_laws_lemma11  {E C : sym_mon_closed_cat} (pb : Pullbacks E)
  (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K)
  {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧)
  (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧)
  (dpb34 := tensor_doublePullback pb k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb2_34 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2')
                ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L R3 R4)),,
                 pr11 dpb34,,
                 doublePullbackPrM dpb34))
  (dpb1_2_34 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
                  ((U2 ⊗_{ E} (U3 ⊗_{ E} U4),,
                      l2 ⊗^{ E} (l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L R3 R4)) ·
                             (fmonoidal_preservestensordata L R2 (R3 ⊗_{ C} R4))),,
                     pr11 dpb2_34,, doublePullbackPrM dpb2_34)):
   doublePullbackPrL dpb1_2_34
  · (internal_postcomp U1
       (doublePullbackPrL dpb2_34
        · (internal_postcomp U2
             (doublePullbackPrL dpb34)
           · internal_uncurry U2 U3 X4))
     · internal_uncurry U1 (U2 ⊗_{ E} U3) X4 · internal_precomp α^{ E }_{ U1, U2, U3} X4)
  · internal_postcomp ((U1 ⊗_{ E} U2) ⊗_{ E} U3) l4' =
  doublePullbackPrM dpb1_2_34
  · # K (α^{ C }_{ R1 ⊗_{ C} R2, R3, R4} · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4})
  · (internal_lam
       (sym_mon_braiding E (K (((R1 ⊗_{ C} R2) ⊗_{ C} R3) ⊗_{ C} R4)) (L ((R1 ⊗_{ C} R2) ⊗_{ C} R3))
        · pr1 k ((R1 ⊗_{ C} R2) ⊗_{ C} R3) R4)
     · internal_precomp ((l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L R1 R2)) ⊗^{ E} l3 · (fmonoidal_preservestensordata L (R1 ⊗_{ C} R2) R3))
     (K R4)).
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

Local Definition double_glued_monoidal_laws_lemma12_type {E C : sym_mon_closed_cat} (pb : Pullbacks E)
  (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K)
  {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧)
  (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧) : UU.
Proof.
  set (dpb34 := tensor_doublePullback pb k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4')).
  set (dpb2_34 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2')
                ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L R3 R4)),,
                 pr11 dpb34,, doublePullbackPrM dpb34)).
  set (dpb1_2_34 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
                  ((U2 ⊗_{ E} (U3 ⊗_{ E} U4),,
                      l2 ⊗^{ E} (l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L R3 R4)) ·
                             (fmonoidal_preservestensordata L R2 (R3 ⊗_{ C} R4))),,
                     pr11 dpb2_34,, doublePullbackPrM dpb2_34)).
  set (dpb12 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')).
  set (dpb12_3 := tensor_doublePullback pb k
                  ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L R1 R2)),,
                       pr11 dpb12,, doublePullbackPrM dpb12) ((U3,, l3),, X3,, l3')).
  exact (doublePullbackPrM dpb1_2_34
  · # K (α^{ C }_{ R1 ⊗_{ C} R2, R3, R4} · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4})
  · (compose (C:=E) (# K (sym_mon_braiding C R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3)))
     (internal_lam
          ((pr121 E) (K (R4 ⊗_{ C} ((R1 ⊗_{ C} R2) ⊗_{ C} R3))) (L R4)
           · pr1 k R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3))
        · internal_precomp l4 (K ((R1 ⊗_{ C} R2) ⊗_{ C} R3)))) =
  internal_lam
    (doublePullbackArrow _ ((pr11 dpb1_2_34) ⊗_{E} U4)
       ((doublePullbackPrL dpb1_2_34
         · (internal_postcomp U1
              (doublePullbackPrL dpb2_34
               · (internal_postcomp U2
                    (doublePullbackPrR dpb34)
                  · internal_swap_arg U2 X3 U4))
            · internal_swap_arg U1 (internal_hom U2 X3) U4))
        ⊗^{ E}_{r} U4
        · (internal_eval U4 (internal_hom U1 (internal_hom U2 X3)) · internal_uncurry U1 U2 X3))
       ((doublePullbackPrM dpb1_2_34
         · # K
             (sym_mon_braiding C R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3)
              · (α^{ C }_{ R1 ⊗_{ C} R2, R3, R4} · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4})))
        ⊗^{ E} l4
        · (sym_mon_braiding E (K (monoidal_cat_tensor_pt R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3))) (L R4)
           · pr1 k R4 ((R1 ⊗_{ C} R2) ⊗_{ C} R3)))
       (internal_lam
          (doublePullbackArrow dpb12
             ((pr11 dpb1_2_34 ⊗_{E} U4) ⊗_{E} U3)
             (((doublePullbackPrL dpb1_2_34
                · (internal_postcomp U1
                     (doublePullbackPrR dpb2_34
                      · internal_precomp (sym_mon_braiding E U4 U3) X2 · 
                      internal_curry U4 U3 X2)
                   · internal_swap_arg U1 (internal_hom U3 X2) U4))
               ⊗^{ E}_{r} U4
               · (internal_eval U4 (internal_hom U1 (internal_hom U3 X2))
                  · internal_swap_arg U1 X2 U3))
              ⊗^{ E}_{r} U3 · internal_eval U3 (internal_hom U1 X2))
             ((doublePullbackPrM dpb1_2_34 ⊗^{ E}_{r} U4)  ⊗^{ E}_{r} U3
              · (α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))), U4, U3}
                 · K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗^{ E}_{l} sym_mon_braiding E U4 U3
                 · sym_mon_braiding E (K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))))
                     (U3 ⊗_{E} U4)
                 · ((l3 ⊗^{ E} l4 · fmonoidal_preservestensordata L R3 R4)
                    ⊗^{ E} # K (sym_mon_braiding C (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2)
                              · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4})
                    · pr1 k (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2))))
             (((doublePullbackPrR dpb1_2_34
                · (internal_precomp (sym_mon_braiding E U4 (U2 ⊗_{ E} U3) · α^{ E }_{ U2, U3, U4}) X1
                   · internal_curry U4 (U2 ⊗_{ E} U3) X1))
               ⊗^{ E}_{r} U4
               · (internal_eval U4 (internal_hom (U2 ⊗_{ E} U3) X1)
                  · (internal_precomp (sym_mon_braiding E U3 U2) X1 · internal_curry U3 U2 X1)))
              ⊗^{ E}_{r} U3 · internal_eval U3 (internal_hom U2 X1))
             (double_glued_monoidal_laws_lemma7 pb L K k l1 l1' l2 l2' l3 l3' l4 l4')
             (double_glued_monoidal_laws_lemma8 pb L K k l1 l1' l2 l2' l3 l3' l4 l4')))
       (double_glued_monoidal_laws_lemma9 pb L K k l1 l1' l2 l2' l3 l3' l4 l4')
       (double_glued_monoidal_laws_lemma10 pb L K k l1 l1' l2 l2' l3 l3' l4 l4'))
  · internal_postcomp U4
      (doublePullbackPrM dpb12_3)).
Defined.


Local Lemma double_glued_monoidal_laws_lemma12 {E C : sym_mon_closed_cat} (pb : Pullbacks E)
  (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K)
  {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧)
  (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧)
  (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧)
  (l4' : E ^opp ⟦ K R4, X4 ⟧) :
  double_glued_monoidal_laws_lemma12_type pb L K k l1 l1' l2 l2' l3 l3' l4 l4'.
Proof.
  unfold double_glued_monoidal_laws_lemma12_type.
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

Local Definition double_glued_monoidal_laws_lemma13_type_arrow1 {E C : sym_mon_closed_cat}
  (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E}
  (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧)
  (dpb34 := tensor_doublePullback pb k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb2_34 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2')
                ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L R3 R4)),,
                   pr11 dpb34,, doublePullbackPrM dpb34))
  (dpb1_2_34 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
                  ((U2 ⊗_{ E} (U3 ⊗_{ E} U4),,
                      l2 ⊗^{ E} (l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L R3 R4)) ·
                             (fmonoidal_preservestensordata L R2 (R3 ⊗_{ C} R4))),,
                     pr11 dpb2_34,, doublePullbackPrM dpb2_34)) : 
  E ⟦ (doublePullbackObject dpb1_2_34 ⊗_{ E} U4) ⊗_{ E} U3, K (R1 ⊗_{ C} R2) ⟧.
Proof.
  exact ((doublePullbackPrM dpb1_2_34 ⊗^{ E}_{r} U4) ⊗^{ E}_{r} U3
  · (α^{ E }_{ K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))), U4, U3}
     · K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4))) ⊗^{ E}_{l} sym_mon_braiding E U4 U3
     · sym_mon_braiding E (K (R1 ⊗_{ C} (R2 ⊗_{ C} (R3 ⊗_{ C} R4)))) (U3 ⊗_{ E} U4)
     · ((l3 ⊗^{ E} l4 · fmonoidal_preservestensordata L R3 R4)
        ⊗^{ E} # K (sym_mon_braiding C (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2)
                  · α^{ C }_{ R1, R2, R3 ⊗_{ C} R4})
            · pr1 k (R3 ⊗_{ C} R4) (R1 ⊗_{ C} R2)))).
Defined.

Local Definition double_glued_monoidal_laws_lemma13_type_arrow2 {E C : sym_mon_closed_cat}
  (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E}
  (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (l4 : E ⟦ U4, L R4 ⟧) (l4' : E ^opp ⟦ K R4, X4 ⟧)
  (dpb1_23 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
          ((U2 ⊗_{ E} U3,, l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L R2 R3)),,
           pr11 (tensor_doublePullback pb k ((U2,, l2),, X2,, l2')
                   ((U3,, l3),, X3,, l3')),,
           doublePullbackPrM
           (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))))
  (dpb23 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))
  (dpb23_4 := tensor_doublePullback pb k
                         ((U2 ⊗_{ E} U3,, l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L R2 R3)),, pr11 dpb23,, doublePullbackPrM
                            (tensor_doublePullback pb k ((U2,, l2),, X2,, l2')
                               ((U3,, l3),, X3,, l3'))) ((U4,, l4),, X4,, l4'))
  (dpb1_23_4 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
                (((U2 ⊗_{ E} U3) ⊗_{ E} U4,,
                  (l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L R2 R3)) ⊗^{ E} l4
                  · (fmonoidal_preservestensordata L (R2 ⊗_{ C} R3) R4)),,
                   pr11 dpb23_4,, doublePullbackPrM dpb23_4))
  (dpb12 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))
  (dpb34 := tensor_doublePullback pb k ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
  (dpb2_34 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2')
                ((U3 ⊗_{ E} U4,, l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L R3 R4)),,
                   pr11 dpb34,, doublePullbackPrM dpb34))
  (dpb1_2_34 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
                  ((U2 ⊗_{ E} (U3 ⊗_{ E} U4),,
                      l2 ⊗^{ E} (l3 ⊗^{ E} l4 · (fmonoidal_preservestensordata L R3 R4)) ·
                             (fmonoidal_preservestensordata L R2 (R3 ⊗_{ C} R4))),,
                     pr11 dpb2_34,, doublePullbackPrM dpb2_34)) : 
  E ⟦ (doublePullbackObject dpb1_2_34 ⊗_{ E} U4) ⊗_{ E} U3, K (R1 ⊗_{ C} R2) ⟧.
Proof.
  exact (
      (double_glued_leftwhiskering_comp2 pb k ((U1,, l1),, X1,, l1')
         (double_glued_tensor_product pb L K k (R2 ⊗_{ C} R3) R4
            (double_glued_tensor_product pb L K k R2 R3 ((U2,, l2),, X2,, l2')
               ((U3,, l3),, X3,, l3')) ((U4,, l4),, X4,, l4'))
         (double_glued_tensor_product pb L K k R2 (R3 ⊗_{ C} R4) ((U2,, l2),, X2,, l2')
            (double_glued_tensor_product pb L K k R3 R4 ((U3,, l3),, X3,, l3')
               ((U4,, l4),, X4,, l4')))
         (disp_monoidal_associator (double_glued_monoidal_data pb L K k) R2 R3 R4
            ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3') ((U4,, l4),, X4,, l4'))
         ⊗^{ E}_{r} U4
   · doublePullbackArrow dpb1_23
   (pr11 dpb1_23_4 ⊗_{E} U4)
       ((doublePullbackPrL dpb1_23_4 · (internal_postcomp U1 (doublePullbackPrR dpb23_4)
                                          · internal_swap_arg U1 (pr11 dpb23)  U4))
          ⊗^{ E}_{r} U4
        · internal_eval U4 (internal_hom U1 (pr11 dpb23)))
       (pr11 dpb1_23_4 ⊗^{ E}_{l} l4 ·
                           (doublePullbackPrM dpb1_23_4 · (compose (C:=E) (# K α^{ C }_{ R1, R2 ⊗_{ C} R3, R4}) (# K (sym_mon_braiding C R4 (R1 ⊗_{ C} (R2 ⊗_{ C} R3))))))
                           ⊗^{ E}_{r} L R4
                               · (sym_mon_braiding E (K (R4 ⊗_{ C} (R1 ⊗_{ C} (R2 ⊗_{ C} R3)))) (L R4) · pr1 k R4 (R1 ⊗_{ C} (R2 ⊗_{ C} R3))))
       (doublePullbackPrR dpb1_23_4 ⊗^{ E}_{r} U4
        · (internal_precomp (sym_mon_braiding E U4 (U2 ⊗_{ E} U3)) X1 ⊗^{ E}_{r} U4
           · (internal_curry U4 (U2 ⊗_{ E} U3) X1 ⊗^{ E}_{r} U4
              · internal_eval U4 (internal_hom (U2 ⊗_{ E} U3) X1))))
       (associator.assocdata_lemma1 pb k l1 l1' (l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L R2 R3)) (doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))) l4 l4')
       (associator.assocdata_lemma2 pb k l1 l1' (l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L R2 R3)) (doublePullbackPrM dpb23) l4 l4'))
        ⊗^{ E}_{r} U3
            · doublePullbackArrow dpb12 (pr11 dpb1_23 ⊗_{ E} U3)
      ((doublePullbackPrL dpb1_23 · (internal_postcomp U1 (doublePullbackPrR dpb23)
                                       · internal_swap_arg U1 X2 U3))
         ⊗^{ E}_{r} U3 · internal_eval U3 (internal_hom U1 X2))
      (pr11 dpb1_23 ⊗^{ E}_{l} l3 · (doublePullbackPrM dpb1_23 · (compose (C:=E) (# K α^{ C }_{ R1, R2, R3}) (# K (sym_mon_braiding C R3 (R1 ⊗_{ C} R2))))) ⊗^{ E}_{r} L R3 · (sym_mon_braiding E (K (R3 ⊗_{ C} (R1 ⊗_{ C} R2))) (L R3) · pr1 k R3 (R1 ⊗_{ C} R2)))
      (doublePullbackPrR dpb1_23 ⊗^{ E}_{r} U3
       · (internal_precomp (sym_mon_braiding E U3 U2) X1 ⊗^{ E}_{r} U3
          · (internal_curry U3 U2 X1 ⊗^{ E}_{r} U3
             · internal_eval U3 (internal_hom U2 X1))))
      (associator.assocdata_lemma1 pb k l1 l1' l2 l2' l3 l3')
      (associator.assocdata_lemma2 pb k l1 l1' l2 l2' l3 l3')
  · doublePullbackPrM dpb12 ).
Defined.

Local Definition double_glued_monoidal_laws_lemma13_type {E C : sym_mon_closed_cat} (pb : Pullbacks E)
  (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K)
  {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧)
  (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧)
  (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧)
  (l4' : E ^opp ⟦ K R4, X4 ⟧) : UU.
Proof.
  exact (double_glued_monoidal_laws_lemma13_type_arrow2 pb L K k l1 l1' l2 l2' l3 l3' l4 l4'
        = double_glued_monoidal_laws_lemma13_type_arrow1 pb L K k l1 l1' l2 l2' l3 l3' l4 l4').
Defined.

Local Lemma double_glued_monoidal_laws_lemma13 {E C : sym_mon_closed_cat} (pb : Pullbacks E)
  (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K)
  {R1 R2 R3 R4: C} {U1 X1 U2 X2 U3 X3 U4 X4: E} (l1 : E ⟦ U1, L R1 ⟧)
  (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧)
  (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) (l4 : E ⟦ U4, L R4 ⟧)
  (l4' : E ^opp ⟦ K R4, X4 ⟧) :
  double_glued_monoidal_laws_lemma13_type pb L K k l1 l1' l2 l2' l3 l3' l4 l4'.
Proof.
  unfold double_glued_monoidal_laws_lemma13_type,
    double_glued_monoidal_laws_lemma13_type_arrow1,
    double_glued_monoidal_laws_lemma13_type_arrow2.
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
  apply maponpaths.
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
Qed.


Lemma double_glued_disp_pentagon_identity {E C : sym_mon_closed_cat} (pb : Pullbacks E)
    (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) : 
  disp_pentagon_identity
    (disp_monoidal_associator (double_glued_monoidal_data pb L K k)).
Proof.
  intros R1 R2 R3 R4.
  intros ((U1, l1), (X1, l1')) ((U2, l2), (X2, l2')).
  intros ((U3, l3), (X3, l3')) ((U4, l4), (X4, l4')).
  apply double_glued_mor_eq; split;
    unfold transportb, transportf;
    induction (! monoidal_pentagonidentity C R1 R2 R3 R4).
  apply (monoidal_pentagonidentity E).
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  (*
  Unshelve.
  9 : {
    apply (compose (doublePullbackPrL _)).
    refine (compose _ (internal_precomp (α^{E}_{_,_,_}) _)).
    refine (compose _ (internal_uncurry _ _ _)).
    apply internal_postcomp.
    apply (compose (doublePullbackPrL _)).
    refine (compose _ (internal_uncurry _ _ _)).
    apply internal_postcomp.
    apply (doublePullbackPrL _).
  }
  9 : {
    apply (compose (doublePullbackPrM _)).
    apply (# K).
    apply (α^{C}_{_,_,_} · α^{C}_{_,_,_}).
  }
  9 : {
    apply internal_lam.
    use doublePullbackArrow.
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (doublePullbackPrL _ )).
    refine (compose (internal_postcomp U1  _) _).
    apply (compose (doublePullbackPrL _ )).
    apply (compose (internal_postcomp U2 (doublePullbackPrR _))).
    apply internal_swap_arg.
    apply internal_swap_arg.
    apply (compose (internal_eval U4 _)).
    apply internal_uncurry. (*completes subgoal *)
    refine (compose (_ ⊗^{E} l4) _).
    apply (compose (doublePullbackPrM _ )).
    refine (# K _).
    refine (compose _ (α^{C}_{_,_,_} · α^{C}_{_,_,_})).
    apply (sym_mon_braiding C _ _).
    apply (compose (sym_mon_braiding E _ _)).
    apply (pr1 k). (*completes subgoal *)
    simpl.
    apply internal_lam.
    use doublePullbackArrow.
    refine (compose (_ ⊗^{E}_{r} _) _).
    refine (compose (_ ⊗^{E}_{r} _) _).
    refine (compose (doublePullbackPrL _ ) _).
    apply (compose (internal_postcomp U1 (doublePullbackPrR _ · internal_precomp (sym_mon_braiding E _ _) _ · internal_curry _ _ _))).
    apply (internal_swap_arg _ _ _ ).
    apply (internal_eval U4 _ · internal_swap_arg _ _ _).
    apply (internal_eval U3 _). (*completes subgoal *)
    apply (compose (((doublePullbackPrM _) ⊗^{E}_{r} _ ) ⊗^{E}_{r} _ )).
    apply (compose (α^{E}_{_,_,_} · _ ⊗^{E}_{l} (sym_mon_braiding E U4 U3) · sym_mon_braiding E _ _)).
    apply (compose (((l3 ⊗^{E} l4) · fmonoidal_preservestensordata L _ _) ⊗^{E} (# K (sym_mon_braiding C _ _ · α^{C}_{_,_,_})))).
    apply (pr1 k). (*completes subgoal *)
    simpl.
    refine (compose (_ ⊗^{E}_{r} _) _).
    refine (compose (_ ⊗^{E}_{r} _) _).
    refine (compose (doublePullbackPrR _ ) _).
    apply (compose (internal_precomp (sym_mon_braiding E _ _ · α^{E}_{_,_,_}) _)).
    apply internal_curry.
    apply (compose (internal_eval _ _)).
    apply (compose (internal_precomp (sym_mon_braiding E _ _) _)).
    apply internal_curry.
    apply (internal_eval U3 _). (*completes subgoal *)
    exact (double_glued_monoidal_laws_lemma7 pb L K k l1 l1' l2 l2' l3 l3' l4 l4').
    exact (double_glued_monoidal_laws_lemma8 pb L K k l1 l1' l2 l2' l3 l3' l4 l4').
    exact (double_glued_monoidal_laws_lemma9 pb L K k l1 l1' l2 l2' l3 l3' l4 l4').
    exact (double_glued_monoidal_laws_lemma10 pb L K k l1 l1' l2 l2' l3 l3' l4 l4').
  } *)
  exact (double_glued_monoidal_laws_lemma11 pb L K k l1 l1' l2 l2' l3 l3' l4 l4').  
  exact (double_glued_monoidal_laws_lemma12 pb L K k l1 l1' l2 l2' l3 l3' l4 l4').
  simpl.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! internal_postcomp_comp U1 _ _ @ _).
  apply maponpaths.
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ ! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  exact (monoidal_pentagonidentity C R1 R2 R3 R4).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (internal_lam_postcomp _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; refine (maponpaths (λ f, f · _) (when_bifunctor_becomes_rightwhiskering E _ _) @ _).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  unfold postcompose.
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 3 refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
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
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (! maponpaths (compose _) (pr12 k _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
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
  refine (maponpaths (λ f, compose (C:=E) _ f · _) (! functor_comp K _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  exact (monoidal_pentagonidentity C _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (when_bifunctor_becomes_rightwhiskering E _ _) @ _).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (! internal_postcomp_comp U1 _ _) @ _).
  refine (! internal_postcomp_comp U1 _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_postcomp _ _ @ _).
  refine (maponpaths internal_lam (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E U4).
  refine (! internal_lam_natural _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _)) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E U4).
  refine (! internal_lam_natural _ _ @ _).
  refine (_ @ id_right _).
  apply maponpaths.
  exact (triangle_id_right_ad (pr2 (pr2 E _)) _).
  exact (double_glued_monoidal_laws_lemma13 pb L K k l1 l1' l2 l2' l3 l3' l4 l4').
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  (* simpl. *)
  unfold postcompose, monoidal_cat_tensor_pt.
  do 3 refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths compose (! bifunctor_rightcomp E _ _ _ _ _ _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  do 3 refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths compose (! bifunctor_rightcomp E _ _ _ _ _ _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (compose _) (internal_precomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  exact (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (internal_postcomp_comp U1 _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (uncurry_nat3 _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) (! internal_postcomp_comp U1 _ _)).
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
  apply maponpaths.
  exact (! functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply (maponpaths internal_lam).
  simpl. unfold postcompose, monoidal_cat_tensor_pt, monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (_ @ ! maponpaths (compose _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! internal_postcomp_comp U1 _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, f · _) (! internal_postcomp_comp U1 _ _)).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (uncurry_nat3 _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply internal_uncurry_tensor_swap. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) _ (# K f)) (assoc' _ _ _)).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (_ @ ! maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  exact (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  simpl. unfold postcompose, monoidal_cat_tensor_pt.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (internal_lam_precomp _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · (f · _)) ⊗^{E}_{r} _ · _) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (curry_unit _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (! hom_onmorphisms_is_postcomp _ _) @ _).
  refine (internal_lam_tensor_eval _ @ _).
  refine (maponpaths (compose _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · f) (! hom_onmorphisms_is_postcomp _ _) @ _).
  apply (maponpaths internal_lam).
  apply doublePullbackArrowUnique.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f · _)) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, (((internal_postcomp _ f · _) ⊗^{E}_{r} _) · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (((f · _) ⊗^{E}_{r} _) · _) ⊗^{E}_{r} _ · _) (internal_postcomp_comp _ _ _)).
  refine (_ @ maponpaths (λ f, ((f ⊗^{E}_{r} _) · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  rewrite (internal_postcomp_comp U1).
  refine (_ @ maponpaths (λ f, ((f ⊗^{E}_{r} _) · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (compose _) (! mon_closed_adj_natural_co E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, (f ⊗^{ E}_{r} _) ⊗^{ E}_{r} _ · _) (internal_swap_arg_nat2 _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! maponpaths (compose _) (curry_counit _ _ _) @ _).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply internal_swap_tensor_curry. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · (f · _))) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply map_on_two_paths.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  now rewrite assoc.
  now rewrite (functor_comp K).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f · _)) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (λ f, (_ · f) ⊗^{ E}_{r} _ · _) (internal_eval_nat _ _ _ _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f ⊗^{ E}_{r} _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (!mon_closed_adj_natural_co E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (curry_counit _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  rewrite (internal_postcomp_comp U4).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f) · _) (id_right _)).
  rewrite <- internal_precomp_id.
  refine (_ @ maponpaths (λ f, _ · f · _) (curry_nat12 _ _ _)).
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, _ · (_ · f) · _) (! id_left _) @ _).
  refine (maponpaths (λ f, _ · (_ · (f · _)) · _) (! internal_postcomp_id _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · (internal_postcomp _ f · _)) · _) (! internal_precomp_id _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! curry_nat12 _ _ _) @ _).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _ ).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (compose _) (internal_curry_curry _ _ _ _)).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose _) (assoc _ _ _)).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (internal_precomp_comp _ _ _)).
  refine (! internal_precomp_comp _ _ _ @ _ @ internal_precomp_comp _ _ _).
  apply (maponpaths (λ f, internal_precomp f _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (compose _) (sym_mon_tensor_lassociator0 E _ _ _)).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ assoc' _ _ _).
  refine (! monoidal_braiding_naturality_right E _ _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (assoc' _ _ _)).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ maponpaths (λ f, _ · f · _) (sym_mon_hexagon_rassociator E _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (pr2 (monoidal_associatorisolaw E _ _ _))).
  rewrite id_right.
  refine (! id_left _ @ _).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (monoidal_associatorisolaw E).
Qed.

Lemma double_glued_monoidal_laws {E C : sym_mon_closed_cat} (pb : Pullbacks E)
  (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) :
  disp_monoidal_laws (double_glued_monoidal_data pb L K k).
Proof.
  split5.
  exact (double_glued_disp_leftunitor_law pb L K k).
  exact (double_glued_disp_rightunitor_law pb L K k).
  exact (double_glued_disp_associator_law pb L K k).
  exact (double_glued_disp_triangle_identity pb L K k).
  exact (double_glued_disp_pentagon_identity pb L K k).
Qed.
*)
