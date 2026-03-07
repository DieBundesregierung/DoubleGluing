(*************************

In this file we define the symmetric monoidal structure of the bang functor of the double glued category.


**************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
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
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.Semantics.LinearLogic.LinearCategory.
Require Import UniMath.Semantics.LinearLogic.LinearNonLinear.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.

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
Require Import double_gluing.monoidal.monoidal_laws.
Require Import double_gluing.monoidal.monoidal.
Require Import double_gluing.monoidal.symmetry.

Require Import double_gluing.closed.internal_hom.
Require Import double_gluing.closed.adjunction.
Require Import double_gluing.closed.closed.

Require Import double_gluing.linear_cat.linear_functor.
Require Import double_gluing.linear_cat.bang.


Local Lemma double_glued_total_bang_preserves_tensor_lemma1 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_ob L K R1) (dr2 : double_glued_ob L K R2) :
  compose (C:=E) (# K (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R2))
  (internal_lam
      (sym_mon_braiding E (K ((pr111 (linear_category_bang C)) R1 ⊗_{ C} (pr111 (linear_category_bang C)) R2)) ((pr111 (linear_category_bang E)) (pr11 dr1))
       · ((# (pr111 (linear_category_bang E)) (pr21 dr1) · pr1 κ^{ L} R1)
          ⊗^{ E}_{r} K ((pr111 (linear_category_bang C)) R1 ⊗_{ C} (pr111 (linear_category_bang C)) R2)
          · pr1 k ((pr111 (linear_category_bang C)) R1) ((pr111 (linear_category_bang C)) R2))))
  · internal_postcomp ((pr111 (linear_category_bang E)) (pr11 dr1)) (identity (K ((pr111 (linear_category_bang C)) R2))) =
  compose (C:=E) (# K (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R2))
  (internal_lam
       (sym_mon_braiding E (K ((pr111 (linear_category_bang C)) R1 ⊗_{ C} (pr111 (linear_category_bang C)) R2)) (L ((pr111 (linear_category_bang C)) R1))
        · pr1 k ((pr111 (linear_category_bang C)) R1) ((pr111 (linear_category_bang C)) R2))
     · internal_precomp (# (pr111 (linear_category_bang E)) (pr21 dr1) · (pr121 L) R1) (K ((pr111 (linear_category_bang C)) R2))).
Proof.
  unfold postcompose; simpl.
  rewrite (internal_postcomp_id ((pr111 (linear_category_bang E)) (pr11 dr1))).
  rewrite id_right.
  apply maponpaths.
  unfold internal_lam.
  rewrite 2 hom_onmorphisms_is_postcomp.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  exact (assoc _ _ _).
Qed.

Local Lemma double_glued_total_bang_preserves_tensor_lemma2 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_ob L K R1) (dr2 : double_glued_ob L K R2) :
  compose (C:=E) (# K (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R2))
   (compose (C:=E) (# K (sym_mon_braiding C ((pr111 (linear_category_bang C)) R2) ((pr111 (linear_category_bang C)) R1)))
     (internal_lam
          (sym_mon_braiding E (K ((pr111 (linear_category_bang C)) R2 ⊗_{ C} (pr111 (linear_category_bang C)) R1)) (L ((pr111 (linear_category_bang C)) R2))
           · pr1 k ((pr111 (linear_category_bang C)) R2) ((pr111 (linear_category_bang C)) R1))
        · internal_precomp (# (pr111 (linear_category_bang E)) (pr21 dr2) · (pr121 L) R2) (K ((pr111 (linear_category_bang C)) R1)))) =
  compose (C:=E) (# K (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R2))
  (compose (C:=E) (# K (sym_mon_braiding C ((pr111 (linear_category_bang C)) R2) ((pr111 (linear_category_bang C)) R1)))
     (internal_lam
         (sym_mon_braiding E (K (monoidal_cat_tensor_pt ((pr111 (linear_category_bang C)) R2) ((pr111 (linear_category_bang C)) R1)))
            ((pr111 (linear_category_bang E)) (pr11 dr2))
          · ((# (pr111 (linear_category_bang E)) (pr21 dr2) · pr1 κ^{ L} R2)
             ⊗^{ E}_{r} K (monoidal_cat_tensor_pt ((pr111 (linear_category_bang C)) R2) ((pr111 (linear_category_bang C)) R1))
             · pr1 k ((pr111 (linear_category_bang C)) R2) ((pr111 (linear_category_bang C)) R1)))))
  · internal_postcomp ((pr111 (linear_category_bang E)) (pr11 dr2)) (identity (K ((pr111 (linear_category_bang C)) R1))).
Proof.
  unfold postcompose; simpl.
  rewrite (internal_postcomp_id ((pr111 (linear_category_bang E)) (pr11 dr2))).
  rewrite id_right.
  do 2 apply maponpaths.
  unfold internal_lam.
  rewrite 2 hom_onmorphisms_is_postcomp.
  rewrite assoc'.
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  exact (assoc' _ _ _).
Qed.

Lemma double_glued_total_bang_preserves_tensor_eq1 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_ob L K R1) (dr2 : double_glued_ob L K R2):
  fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad E (linear_category_bang E)) (pr11 dr1) (pr11 dr2)
  · (# (pr111 (linear_category_bang E)) (pr21 dr1 ⊗^{ E} pr21 dr2 · fmonoidal_preservestensordata L R1 R2) · (pr121 L) (R1 ⊗_{ C} R2)) =
  (# (pr111 (linear_category_bang E)) (pr21 dr1) · (pr121 L) R1) ⊗^{ E} (# (pr111 (linear_category_bang E)) (pr21 dr2) · (pr121 L) R2)
  · fmonoidal_preservestensordata L ((pr111 (linear_category_bang C)) R1) ((pr111 (linear_category_bang C)) R2)
  · # L (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R2).
Proof.
  unfold functoronmorphisms1; simpl.
  rewrite assoc.
  rewrite 2 (functor_comp (pr11 (linear_category_bang E))).
  rewrite assoc.
  refine (maponpaths (λ f, f · _ · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (λ f, f · _ · _) (fmonoidal_preservestensornatright _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (fmonoidal_preservestensornatleft _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  rewrite (bifunctor_rightcomp E).
  rewrite (bifunctor_leftcomp E).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · f) · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 2 rewrite assoc.
  exact (pr12 (pr222 L) R1 R2).
Qed.

Definition double_glued_total_bang_preserves_tensor {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : preserves_tensordata (double_glued_total_monoidal pb L K k) (double_glued_total_monoidal pb L K k)
  (double_glued_total_bang_functor pb L k).
Proof.
  intros (R1, dr1) (R2, dr2).
  exists (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R2).
  split.
  exists (fmonoidal_preservestensordata (linear_category_bang_functor E) _ _).
  exact (double_glued_total_bang_preserves_tensor_eq1 pb L k dr1 dr2).
  use tpair.
  use doublePullbackArrow.
  apply (compose (C:=E) (# K (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R2))).
  apply internal_lam.
  apply (compose (C:=E) (sym_mon_braiding E _ _)).
  apply (postcompose (pr1 k ((pr111 (linear_category_bang C)) R1) _)).
  refine (_ ⊗^{E}_{r} _).
  apply (postcompose (pr1 κ^{L} R1)).
  exact (# _ (pr21 dr1)).
  exact (# K (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R2)).
  apply (compose (C:=E) (# K (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R2))).
  apply (compose (C:=E) (# K (sym_mon_braiding C _ _))).
  apply internal_lam.
  apply (compose (C:=E) (sym_mon_braiding E _ _)).
  apply (postcompose (pr1 k ((pr111 (linear_category_bang C)) R2) _)).
  refine (_ ⊗^{E}_{r} _).
  apply (postcompose (pr1 κ^{L} R2)).
  exact (# _ (pr21 dr2)).
  exact (double_glued_total_bang_preserves_tensor_lemma1 pb L k dr1 dr2).
  exact (double_glued_total_bang_preserves_tensor_lemma2 pb L k dr1 dr2).
  refine (id_left (C:=E) _ @ _).
  exact (! doublePullbackArrow_PrM _ _ _ _ _ _ _).
Defined.

Definition double_glued_total_bang_preserves_unit {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : 
  preserves_unit (pr1 (double_glued_total_sym_mon_closed_cat pb k)) (pr1 (double_glued_total_sym_mon_closed_cat pb k))
    (double_glued_total_bang_functor pb L k).
Proof.
  unfold preserves_unit.
  exists (fmonoidal_preservesunit (linear_category_bang_functor C)).
  split.
  exists (fmonoidal_preservesunit (linear_category_bang_functor E)).
  refine (assoc _ _ _ @ _).
  exact (pr22 (pr222 L)).
  use tpair.
  apply (# K).
  exact (fmonoidal_preservesunit (linear_category_bang_functor C)).
  simpl. (* necessary *)
  refine (id_left _ @ _).
  exact (! id_right _).
Defined.

Local Lemma double_glued_total_bang_laxlaws_lemma1 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {U1 U2 U3 X1 X2 X3 : ob E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧):
  internal_lam
    (sym_mon_braiding E (K ((linear_category_bang C) (R1 ⊗_{ C} (R2 ⊗_{ C} R3))) ⊗_{E} (linear_category_bang E) U3)
       ((linear_category_bang E) U1)
     · (αinv^{ E }_{ linear_category_bang E U1, K ((linear_category_bang C) (R1 ⊗_{ C} (R2 ⊗_{ C} R3))),
        (linear_category_bang E) U3}
        · (((linear_category_bang E) U1
            ⊗^{ E}_{l} # K
                         (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1
                            (R2 ⊗_{ C} R3))
            · ((# (linear_category_bang E) l1 · pr1 κ^{ L} R1)
               ⊗^{ E}_{r} K ((linear_category_bang C) R1 ⊗_{ C} (linear_category_bang C) (R2 ⊗_{ C} R3))
               · pr1 k ((linear_category_bang C) R1) ((linear_category_bang C) (R2 ⊗_{ C} R3))))
           ⊗^{ E}_{r} (linear_category_bang E) U3
           · (sym_mon_braiding E (K ((linear_category_bang C) (R2 ⊗_{ C} R3))) ((linear_category_bang E) U3)
              · ((linear_category_bang E) U3
                 ⊗^{ E}_{l} # K
                              (sym_mon_braiding C ((linear_category_bang C) R3) ((linear_category_bang C) R2)
                               · fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C))
                                   R2 R3)
                 · ((# (linear_category_bang E) l3 · pr1 κ^{ L} R3)
                    ⊗^{ E}_{r} K (monoidal_cat_tensor_pt ((linear_category_bang C) R3) ((linear_category_bang C) R2))
                    · pr1 k ((linear_category_bang C) R3) ((linear_category_bang C) R2)))))))
  · internal_postcomp ((linear_category_bang E) U1) (identity (K ((linear_category_bang C) R2))) =
  # K
    (sym_mon_braiding C ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2))
     · fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) (R1 ⊗_{ C} R2) R3
     · # (linear_category_bang C) α^{ C }_{ R1, R2, R3})
  ⊗^{ E}_{r} (linear_category_bang E) U3
  · (sym_mon_braiding E
       (K (monoidal_cat_tensor_pt ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2))))
       ((linear_category_bang E) U3)
     · ((# (linear_category_bang E) l3 · pr1 κ^{ L} R3)
        ⊗^{ E}_{r} K (monoidal_cat_tensor_pt ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2)))
        · (pr1 k ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2))
           · # K (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R2))))
  · (internal_lam
       (sym_mon_braiding E (K ((linear_category_bang C) R1 ⊗_{ C} (linear_category_bang C) R2))
          (L ((linear_category_bang C) R1))
        · pr1 k ((linear_category_bang C) R1) ((linear_category_bang C) R2))
       · internal_precomp (# (linear_category_bang E) l1 · (pr121 L) R1) (K ((linear_category_bang C) R2))).
Proof.
    refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
    rewrite id_right.
    refine (_ @ maponpaths (compose _) (! internal_lam_precomp _ _)).
    refine (_ @ ! internal_lam_natural _ _).
    apply maponpaths.
    unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (_ @ assoc' _ _ _)).
      apply pathsinv0.
      apply (bifunctor_rightcomp E).
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (compose _) (pr12 k _ _ _ _)).
      apply assoc'.
    }
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
        refine (_ @ assoc _ _ _).
        refine (maponpaths (compose _) (! natural_contraction_composed k _ _ _)).
      }
      apply assoc'.
    }
    refine (assoc _ _ _ @ _).
    refine (maponpaths (compose _) _ @ _).
    refine (maponpaths (λ f, f · _) _ @ _).
    refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
    apply maponpaths.
    apply assoc.
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
    refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
    refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _ @ _) @ _).
    refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply (pr12 k).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
    refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (natural_contraction_composed k _ _ _ @ _) @ _).
    refine (maponpaths (compose _) (! id_left _ @ _) @ _).
    refine (maponpaths (λ f, f · _) (! bifunctor_leftid E _ _ @ _) @ _).
    refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
    apply maponpaths.
    refine (! functor_id K _ @ _).
    refine (_ @ functor_comp K _ _).
    apply maponpaths.
    refine (! bifunctor_rightid C _ _ @ _).
    refine (_ @ bifunctor_rightcomp C _ _ _ _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_braiding_inverses C).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (natural_contraction_extranatural k _ _ _ _) @ _).
    apply assoc.
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
    refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
    refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
    refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
    apply maponpaths.
    assert (is_symmetric_monoidal_functor C E L) as issymL.
    apply (pr211 L).
    now rewrite issymL.
    apply assoc.
    apply assoc'.
    apply assoc.
    apply assoc.
    apply assoc.
    apply assoc.
    apply assoc.
    do 2 refine (assoc _ _ _ @ _ ).
    do 2 refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    (* move #K's to the bottom : *)
    refine (maponpaths (compose _) _ @ _).
    refine (maponpaths (λ f, f · _) _ @ _).
    refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) _ @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) _ @ _).
    apply pathsinv0.
    apply (monoidal_braiding_naturality_right E).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) _ @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) _ @ _).
    refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
    refine (maponpaths (λ f, _ ⊗^{E}_{l} f) _).
    apply pathsinv0.
    apply (bifunctor_leftcomp E).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) _ @ _).
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) _ @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) _ @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) _ @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) _ @ _).
    apply (monoidal_associatorinvnatleft E).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) _ @ _).
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
    apply assoc.
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) _).
    apply pathsinv0.
    apply (bifunctor_leftcomp E).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) _ @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
    apply assoc.
    apply assoc.
    apply assoc.
    apply assoc.
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) _).
      2 : {
        refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
        apply maponpaths.
        refine (_ @ maponpaths (λ f, f · _) _).
        2 : {
          refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
          refine (_ @ assoc _ _ _).
          refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
          apply assoc'.
        }
        refine (_ @ assoc _ _ _).
        apply maponpaths.
        apply (bifunctor_leftcomp E).
      }
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) _).
      2 : {
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
        refine (_ @ assoc _ _ _).
        refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
        apply assoc'.
      }
      apply assoc'.
    }
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatorinvnatleft E _ _ _ _ _)).
        refine (_ @ assoc _ _ _).
        refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
        apply assoc'.
      }
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      apply (bifunctor_leftcomp E).
    }
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply map_on_two_paths.
    do 4 refine (assoc _ _ _ @ _).
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
      apply maponpaths.
      apply pathsinv0.
      apply (monoidal_braiding_naturality_left E).
    }
    refine (maponpaths (λ f, f · _) _ @ _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
    refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
    refine (maponpaths (compose _) (! monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
    apply assoc'.
    apply assoc'.
    apply assoc'.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
    refine (maponpaths (compose _) (! monoidal_associatorinvnatright E _ _ _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
    apply assoc'.
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
      apply assoc.
    }
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
    repeat rewrite assoc'.
    apply maponpaths.
    repeat rewrite assoc.
    refine (maponpaths (λ f, f · _) (sym_mon_hexagon_rassociator E _ _ _) @ _).
    unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E), (when_bifunctor_becomes_rightwhiskering E).
    refine (_ @ id_right _).
    repeat rewrite assoc'.
    repeat apply maponpaths.
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightid E _ _).
    apply maponpaths.
    apply (monoidal_braiding_inverses E).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    refine (map_on_two_paths (compose (C:=E)) _ _ @ _); apply pathsinv0.
    apply (functor_comp K).
    apply (functor_comp K).
    refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
    refine (! functor_comp K _ _ @ _  @ functor_comp K _ _).
    apply maponpaths.
    refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
    refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
    refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_left C _ _ _ _) @ _).
    apply assoc'.
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (fmonoidal_preservesassociativity _ _ _ _) @ _).
    refine (maponpaths (compose _) (assoc' _ _ _) @ _).
    now rewrite 2 assoc.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    rewrite (bifunctor_leftcomp C).
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    rewrite <- (when_bifunctor_becomes_leftwhiskering C), <- (when_bifunctor_becomes_rightwhiskering C).
    refine (assoc _ _ _ @ _).
    apply (sym_mon_hexagon_lassociator C).
Qed.

Local Lemma double_glued_total_bang_laxlaws_lemma2 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {U1 U2 U3 X1 X2 X3 : ob E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧):
# K
    (sym_mon_braiding C ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2))
     · fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) (R1 ⊗_{ C} R2) R3
     · # (linear_category_bang C) α^{ C }_{ R1, R2, R3})
  ⊗^{ E}_{r} (linear_category_bang E) U3
  · (sym_mon_braiding E
       (K (monoidal_cat_tensor_pt ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2))))
       ((linear_category_bang E) U3)
     · ((# (linear_category_bang E) l3 · pr1 κ^{ L} R3)
        ⊗^{ E}_{r} K (monoidal_cat_tensor_pt ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2)))
        · (pr1 k ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2))
           · # K (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R2))))
  · (compose (C:=E) (# K (sym_mon_braiding C ((linear_category_bang C) R2) ((linear_category_bang C) R1)))
     (internal_lam
          ((sym_mon_braiding E) (K ((linear_category_bang C) R2 ⊗_{ C} (linear_category_bang C) R1))
             (L ((linear_category_bang C) R2))
           · pr1 k ((linear_category_bang C) R2) ((linear_category_bang C) R1))
        · internal_precomp (# (linear_category_bang E) l2 · (pr121 L) R2) (K ((linear_category_bang C) R1)))) =
  internal_lam
    ((sym_mon_braiding E (K ((linear_category_bang C) (R1 ⊗_{ C} (R2 ⊗_{ C} R3)))) ((linear_category_bang E) U3)
      · ((linear_category_bang E) U3
         ⊗^{ E}_{l} # K
                      (sym_mon_braiding C ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2))
                       · fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C))
                           (R1 ⊗_{ C} R2) R3
                       · # (linear_category_bang C) α^{ C }_{ R1, R2, R3})
         · ((# (linear_category_bang E) l3 · pr1 κ^{ L} R3)
            ⊗^{ E}_{r} K (monoidal_cat_tensor_pt ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2)))
            · pr1 k ((linear_category_bang C) R3) ((linear_category_bang C) (R1 ⊗_{ C} R2)))))
     ⊗^{ E}_{r} (linear_category_bang E) U2
     · (sym_mon_braiding E (K ((linear_category_bang C) (R1 ⊗_{ C} R2))) ((linear_category_bang E) U2)
        · ((linear_category_bang E) U2
           ⊗^{ E}_{l} # K
                        (sym_mon_braiding C ((linear_category_bang C) R2) ((linear_category_bang C) R1)
                         · fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R2)
           · ((# (linear_category_bang E) l2 · pr1 κ^{ L} R2)
              ⊗^{ E}_{r} K (monoidal_cat_tensor_pt ((linear_category_bang C) R2) ((linear_category_bang C) R1))
              · pr1 k ((linear_category_bang C) R2) ((linear_category_bang C) R1)))))
    · internal_postcomp ((linear_category_bang E) U2) (identity (K ((linear_category_bang C) R1))).
Proof.
    refine (_ @ ! internal_lam_postcomp _ _).
    rewrite internal_lam_precomp.
    refine (assoc _ _ _ @ _).
    refine (internal_lam_natural _ _ @ _).
    apply maponpaths.
    refine (_ @ ! id_right _).
    unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
    do 2 refine (assoc _ _ _ @ _).
    do 3 refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (! monoidal_braiding_naturality_left E _ _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    refine (! monoidal_braiding_naturality_right E _ _ _ _ @ _).
    refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
    apply maponpaths.
    do 2 refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
    refine (_ @ assoc _ _ _).
    do 2 refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
    refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (monoidal_braiding_naturality_right E).
Qed.


Lemma double_glued_total_bang_preserves_tensor_nat_left {C E : linear_category} (pb : Pullbacks E)
  (L : linear_distributive_functor C E) {K : functor C (E^opp)} (k : natural_contraction C E L K) : 
preserves_tensor_nat_left (fmonoidal_preservestensordata
                             (double_glued_total_bang_preserves_tensor pb L k,,
                                double_glued_total_bang_preserves_unit pb L k)).
Proof.
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))) (R3, ((U3, l3), (X3, l3'))).
  intros (f23, ((ϕ23, eqphi),(ψ32, eqpsi))).
  apply (double_glued_total_mor_eq_transp k); split3.
  apply (fmonoidal_preservestensornatleft). (* completes subgoal *)
  apply (fmonoidal_preservestensornatleft). (* completes subgoal *)
  set (dpb := tensor_doublePullback pb k
       (((pr111 (linear_category_bang E)) U1,, # (pr111 (linear_category_bang E)) l1 · (pr121 L) R1),,
        K ((pr111 (linear_category_bang C)) R1),, identity (K ((pr111 (linear_category_bang C)) R1)))
       (((pr111 (linear_category_bang E)) U2,, # (pr111 (linear_category_bang E)) l2 · (pr121 L) R2),,
        K ((pr111 (linear_category_bang C)) R2),, identity (K ((pr111 (linear_category_bang C)) R2)))).
  refine (doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _  @ ! doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
  apply internal_lam.
  apply (compose (sym_mon_braiding E _ _)).
  apply (compose ((# _ l1 · pr1 κ^{L} R1)⊗^{E}_{r} _)).
  apply (compose (_ ⊗^{E}_{l} # K (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R3))).
  apply (compose (pr1 k _ _)).
  apply (# K).
  exact (# _ f23).
  }
  9 : {
  apply (# K).
  apply (compose (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R2)).
  apply (# _).
  exact (R1 ⊗^{C}_{l} f23).
  }
  9 : {
  apply (compose (C:=E) (# K (# _ (sym_mon_braiding C R3 R1)))).
  apply (compose (C:=E) (# K (fmonoidal_preservestensordata (linear_category_bang_functor C) R3 R1))).
  apply internal_lam.
  apply (compose (sym_mon_braiding E _ _)).
  apply (compose ((# _ l2 · pr1 κ^{L} R2)⊗^{E}_{r} _)).
  apply (compose (# _ f23 ⊗^{E}_{r} _)).
  exact (pr1 k _ _).
  }
  unfold internal_lam.
  rewrite 2 hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
  rewrite id_right.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f)) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (mon_closed_adj_natural E _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (internal_postcomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E ((pr111 (linear_category_bang E)) U1)))) _ _ _)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, _ · f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (compose _) (pr12 k _ _ _ _) @ _).
  rewrite assoc.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (! maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  unfold functoronmorphisms2.
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply (fmonoidal_preservestensornatleft (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C))). (* completes subgoal *)
  refine (_ @ maponpaths (compose _) (! internal_postcomp_id _ _)).
  rewrite id_right.
  rewrite internal_lam_precomp.
  unfold internal_lam.
  do 2 rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _ · _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints _) _ _ _) @ _).
  do 2 refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _ · _) (functor_comp K _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints _) _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite (monoidal_braiding_naturality_left E).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (natural_contraction_extranatural k _ _ _ _)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  rewrite (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (pr221 (linear_category_bang C) _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_right C).
  rewrite 2 assoc'.
  apply maponpaths.
  exact (! fmonoidal_preservestensornatleft _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL dpb _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold internal_lam, postcompose; simpl.
  rewrite 2 hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E ((pr111 (linear_category_bang E)) U1)))) _ _ _) @ _).
  repeat rewrite assoc'.
  apply maponpaths.
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  exact (assoc' _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply fmonoidal_preservestensornatleft. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  unfold internal_lam, postcompose; simpl.
  rewrite 2 hom_onmorphisms_is_postcomp.
  do 2 refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose (C:=E) _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ ·  f · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (! maponpaths (λ f, compose (C:=E) f _ · _) (functor_comp K _ _) @ _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _ ) (functor_comp K _ _)).
  rewrite assoc'.
  apply map_on_two_paths.
  apply maponpaths.
  exact ((pr221 (linear_category_bang C)) R3 R1).
  rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (! functor_comp _ _ _) @ _).
  refine (maponpaths (λ f, # _ f · _) eqphi @ _).
  rewrite functor_comp.
  do 2 rewrite assoc'.
  apply maponpaths.
  apply (pr2 κ^{L}). (* completes subgoal *)
  unfold double_glued_total_bang_functor; simpl.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL dpb _ _ _ _ _ _) @ _).
  unfold postcompose, internal_lam.
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  rewrite 2 hom_onmorphisms_is_postcomp.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (pr12 k _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  apply pathsinv0.
  apply fmonoidal_preservestensornatleft. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM dpb _ _ _ _ _ _) @ _).
  exact (! functor_comp K _ _ ).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR dpb _ _ _ _ _ _) @ _).
  unfold postcompose.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) f  _) (functor_comp K _ _)).
  do 2 rewrite assoc.
  refine (! maponpaths (λ f, (compose (C:=E) f _) · _) (functor_comp K _ _) @ _).
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  unfold double_glued_total_monoidal; simpl; unfold monoidal_cat_tensor_pt, internal_lam.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (natural_contraction_extranatural k _ _ _ _)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  do 2 rewrite <- (monoidal_braiding_naturality_right E).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  rewrite assoc'.
  rewrite <- (fmonoidal_preservestensornatleft (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C))).
  rewrite assoc.
  rewrite (monoidal_braiding_naturality_right C).
  rewrite assoc'.
  apply maponpaths.
  apply (pr221 (linear_category_bang C) R3 R1). (* completes "preserves_tensor_nat_right" *)
Qed.

Lemma double_glued_total_bang_preserves_tensor_nat_right {C E : linear_category} (pb : Pullbacks E)
  (L : linear_distributive_functor C E) {K : functor C (E^opp)} (k : natural_contraction C E L K) : 
preserves_tensor_nat_right (fmonoidal_preservestensordata
                             (double_glued_total_bang_preserves_tensor pb L k,,
                                double_glued_total_bang_preserves_unit pb L k)).
Proof.
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))) (R3, ((U3, l3), (X3, l3'))).
  intros (f12, ((ϕ12, eqphi),(ψ21, eqpsi))).
  apply (double_glued_total_mor_eq_transp k); split3.
  apply fmonoidal_preservestensornatright. (* completes subgoal *)
  apply fmonoidal_preservestensornatright. (* completes subgoal *)
  set (dpb := tensor_doublePullback pb k
                    (((pr111 (linear_category_bang E)) U1,, # (pr111 (linear_category_bang E)) l1 · (pr121 L) R1),,
                     K ((pr111 (linear_category_bang C)) R1),, identity (K ((pr111 (linear_category_bang C)) R1)))
                    (((pr111 (linear_category_bang E)) U3,, # (pr111 (linear_category_bang E)) l3 · (pr121 L) R3),,
                     K ((pr111 (linear_category_bang C)) R3),, identity (K ((pr111 (linear_category_bang C)) R3)))).
  refine (doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _  @ ! doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply internal_lam.
    apply (compose (_ ⊗^{E}_{l} (# _ (l1 · # L f12) · pr1 κ^{L} _)) ).
    apply (compose (# K (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R2 R3) ⊗^{E}_{r} _) ).
    apply (compose (sym_mon_braiding E _ _)).
    unfold monoidal_cat_tensor_pt; simpl.
    exact (pr1 k _ _).
  }
  9 : {
    apply (# K).
    apply (compose (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R3)).
    apply (# _).
    exact (f12 ⊗^{C}_{r} R3).
  }
  9 : {
    apply internal_lam.
    apply (compose (_ ⊗^{E}_{l} (# _ l3  · pr1 κ^{L} _))).
    apply (compose ((# K (sym_mon_braiding C _ _ ·
                            fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R2 R3)) ⊗^{E}_{r} _)).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose (pr1 k _ _)).
    apply (# K).
    exact (# _ f12).
  }
  refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
  rewrite id_right.
  rewrite internal_lam_precomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _)).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  simpl.
  refine (_ @ functor_comp _ _ _).
  apply maponpaths.
  repeat refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  do 2 refine (_ @ assoc _ _ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite assoc'.
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (functor_comp _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (pr2 κ^{L} _ _ f12) @ _).
  simpl.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (bifunctor_rightcomp E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  set (keq := pr122 k (pr111 (linear_category_bang C) R3) _ _ (# (pr111 (linear_category_bang C)) f12));
    unfold rightwhiskering_on_morphisms, leftwhiskering_on_morphisms in keq; generalize keq; clear keq.
  do 2 rewrite id_right; simpl; intros keq.
  rewrite assoc.
  refine (! maponpaths (compose _) keq @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply fmonoidal_preservestensornatright. (* completes subgoal *)
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id _ _)).
  rewrite id_right.
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  rewrite internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  repeat refine (assoc _ _ _ @ _).
  do 2 refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose (C:=E) _) (pr12 k _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left C _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply fmonoidal_preservestensornatright. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL dpb _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold postcompose.
  refine (assoc' _ _ _ @ _).
  rewrite internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc'.
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (! maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, ((# _ f) · _) ⊗^{E}_{r} _ · _) eqphi).
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (! functor_comp _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM dpb _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  unfold postcompose.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply fmonoidal_preservestensornatright. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR dpb _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  unfold postcompose.
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _ · _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! maponpaths (compose _) (functor_comp _ _ _) @ _).
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  do 2 refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  do 2 refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  rewrite (monoidal_braiding_naturality_left E).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  apply (bifunctor_equalwhiskers E). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL dpb _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  unfold postcompose.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  do 2 refine ( _ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  do 2 refine ( _ @ assoc _ _ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (functor_comp K).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  rewrite (functor_comp (linear_category_bang E)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (pr2 κ^{L} _ _ f12)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  set (keq := pr122 k (pr111 (linear_category_bang C) R3) _ _ (# (pr111 (linear_category_bang C)) f12));
    unfold rightwhiskering_on_morphisms, leftwhiskering_on_morphisms in keq; generalize keq; clear keq.
  do 2 rewrite id_right; simpl; intros keq.
  refine (_ @ maponpaths (compose _) keq).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  apply pathsinv0.
  apply fmonoidal_preservestensornatright. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM dpb _ _ _ _ _ _) @ _).
  exact (! functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR dpb _ _ _ _ _ _) @ _).
  unfold postcompose.
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  do 2 refine ( _ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (pr12 k _ _ _ _)).
  refine ( _ @ assoc' _ _ _).
  do 2 rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc.
  refine (_ @ assoc _ _ _).
  simpl.
  rewrite (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (compose _)).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left C _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply fmonoidal_preservestensornatright. (* completes subgoal *)
Qed.

Lemma double_glued_total_bang_preserves_associativity {C E : linear_category} (pb : Pullbacks E)
  (L : linear_distributive_functor C E) {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  preserves_associativity (fmonoidal_preservestensordata
                             (double_glued_total_bang_preserves_tensor pb L k,,
                                double_glued_total_bang_preserves_unit pb L k)).
Proof.
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))) (R3, ((U3, l3), (X3, l3'))).
  apply (double_glued_total_mor_eq_transp k); split3.
  apply fmonoidal_preservesassociativity. (* completes subgoal *)
  apply fmonoidal_preservesassociativity. (* completes subgoal *)
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _  @ ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    simpl.
    apply internal_lam.
    apply (compose (# K ((fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _)) ⊗^{E}_{r} _ )).
    apply (compose αinv^{E}_{_,_,_}).
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (# _ l1)).
    exact (pr1 κ^{L} _).
    exact (pr1 k _ _).
    apply (compose (# K ((fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _)) ⊗^{E}_{r} _ )).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (# _ l2)).
    exact (pr1 κ^{L} _).
    exact (pr1 k _ _).
  }
  9 :{
    apply (# K).
    apply (compose ((fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _) ⊗^{C}_{r} _)).
    apply (compose (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _)).
    exact (# _ α^{C}_{_,_,_}).
  }
  9 : {
    simpl.
    apply internal_lam.
    use doublePullbackArrow.
    apply internal_lam.
    unfold monoidal_cat_tensor_pt.
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose αinv^{E}_{_,_,_}).
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (_ ⊗^{E}_{l} # K ((fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _)))).
    apply (compose ((# _ l1 · pr1 κ^{L} R1) ⊗^{E}_{r} _)).
    exact (pr1 k _ _).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{l} # K _) _).
    refine (compose _ (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R2 R3)).
    exact (sym_mon_braiding C _ _).
    apply (compose ((# _ l3 · pr1 κ^{L} R3) ⊗^{E}_{r} _)).
    exact (pr1 k _ _).
    unfold monoidal_cat_tensor_pt.
    refine (compose (# K _ ⊗^{E}_{r} _) _).
    refine (compose _ (# _ α^{C}_{_,_,_})).
    refine (compose _ (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _)).
    exact (sym_mon_braiding C _ _).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose ((# _ l3 · pr1 κ^{L} _) ⊗^{E}_{r} _)).
    apply (compose (pr1 k _ _)).
    exact (# K ((fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _))).
    apply internal_lam.
    unfold monoidal_cat_tensor_pt.
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{l} # K _) _).
    refine (compose _ (# _ α^{C}_{_,_,_})).
    refine (compose _ (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _)).
    exact (sym_mon_braiding C _ _).
    apply (compose ((# _ l3 · pr1 κ^{L} _)⊗^{E}_{r} _)).
    exact (pr1 k _ _).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{l} # K _) _).
    refine (compose _ (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _)).
    exact (sym_mon_braiding C _ _).
    apply (compose ((# _ l2 · pr1 κ^{L} _)⊗^{E}_{r} _)).
    exact (pr1 k _ _).
    exact (double_glued_total_bang_laxlaws_lemma1 pb L k l1 l1' l2 l2' l3 l3').
    exact (double_glued_total_bang_laxlaws_lemma2 pb L k l1 l1' l2 l2' l3 l3').
  }
  refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
  rewrite id_right.
  rewrite internal_lam_precomp.
  refine (_ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  do 2 refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (! natural_contraction_tensor1 k _ _ _)).
  refine (_ @ assoc' _ _ _).
  do 5 refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (pr12 k).
  apply assoc.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
      2 : {
        refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
        apply maponpaths.
        apply pathsinv0.
        apply (tensor_sym_mon_braiding E).
      }
      apply assoc'.
    }
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) _).
    2 : {
      refine (_ @ assoc _ _ _ @ _).
      2 : {
        apply cancel_postcomposition.
        apply pathsinv0.
        unfold monoidal_cat_tensor_mor; rewrite (bifunctor_equalwhiskers E).
        apply (bifunctor_rightcomp E).
      }
      refine (_ @ assoc' _ _ _ @ _).
      2 : {
        apply maponpaths.
        apply (monoidal_associatornatright E).
      }
      apply cancel_postcomposition.
      apply (monoidal_associatornatleftright E).
    }
    apply assoc'.
  }
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc _ _ _ @ _).
  do 2 refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorinvnatright E).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_rightcomp E).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
    2 : {
      refine (_ @ assoc' _ _ _ @ _).
      2 : {
        apply maponpaths.
        apply pathsinv0.
        apply (monoidal_braiding_naturality_right E).
      }
      apply cancel_postcomposition.
      apply (bifunctor_rightcomp E).
    }
    apply assoc.
  }
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (assoc' _ _ _ @ _ ).
  apply map_on_two_paths.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (assoc _ _ _ @ _).
    apply pathsinv0.
    apply fmonoidal_preservesassociativity.
  }
  refine (! id_left _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_associatorisolaw C).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ ! sym_mon_tensor_lassociator E _ _ _)).
  2 : {
    unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
    do 3 refine (_ @ assoc _ _ _).
    reflexivity.
  }
  do 2 (refine (_ @ assoc _ _ _); apply maponpaths ).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  repeat rewrite assoc.
  apply (sym_mon_tensor_rassociator E). (* completes subgoal *)
  refine (assoc (C:=E) _ _ _ @ _).
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  rewrite internal_lam_precomp.
  unfold internal_lam.
  rewrite 2 hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! internal_postcomp_comp _ _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  refine ( _ @ ! doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ assoc _ _ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc'.  
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (pr12 k _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  unfold functoronmorphisms1.
  do 2 apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left C _ _ _ _)).
  exact (assoc _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  rewrite internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _)).
  unfold postcompose.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    do 2 refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
      apply maponpaths.
      apply assoc'.
    }
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) _).
    2 : {
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
      2 : {
        refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
        apply maponpaths.
        apply (pr12 k).
      }
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (! natural_contraction_composed k _ _ _)).
      apply assoc'.
    }
    apply assoc'.
  }
  (*move fmonoidal_preseves... of bang to end to change argument of k*)
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (functor_comp _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (functor_comp _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! fmonoidal_preservestensornatright ((linear_category_bang_functor E)) _ _ U2 l1) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! fmonoidal_preservestensornatleft ((linear_category_bang_functor E)) _ _ _ _) @ _).
  apply assoc'.
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (assoc _ _ _ @ _).
  (*using that κ is monoidal as a nat-trans*)
  refine (pr12 (pr222 L) R1 R2 @ _).
  refine (_ @ assoc' _ _ _).
  apply assoc.
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (_ @ assoc' _ _ _ @ _) @ _).
  apply cancel_postcomposition.
  apply (bifunctor_rightcomp E).
  refine (maponpaths (compose _) (! natural_contraction_extranatural k (linear_category_bang C R3) _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  apply assoc.
  do 3 refine (_ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  do 2 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) _).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) _).
        2 : {
          apply pathsinv0.
          apply (monoidal_associatorinvnatright E).
        }
        refine (_ @ assoc _ _ _).
        apply maponpaths.
        refine (_ @ maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
        refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
        apply maponpaths.
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) _).
        2 : {
          refine (_ @ assoc' _ _ _).
          refine (_ @ maponpaths (λ f, f · _) _).
          2 : {
            apply (monoidal_braiding_naturality_right E).
          }
          refine (assoc' _ _ _ @ _ @ assoc _ _ _).
          apply maponpaths.
          apply (bifunctor_equalwhiskers E).
        }
        refine (_ @ assoc _ _ _).
        apply maponpaths.
        apply (bifunctor_leftcomp E).
      }
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      apply (monoidal_braiding_naturality_right E).
    }
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    apply (bifunctor_equalwhiskers E).
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (monoidal_associatorinvnatleft E).
  }
  do 4 refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths.
    apply (bifunctor_leftcomp E).
    apply cancel_postcomposition.
    apply (bifunctor_equalwhiskers E).
  }
  refine (_ @ assoc' _ _ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  apply pathsinv0.
  apply (bifunctor_leftcomp E).
  apply map_on_two_paths.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
      apply cancel_postcomposition.
      2 : {
        apply maponpaths.
        apply pathsinv0.
        apply (monoidal_braiding_naturality_left E).
      }      
      refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
      2 : {
        apply maponpaths.
        refine (_ @ maponpaths (λ f, f · _) _).
        refine (assoc' _ _ _ @ _ @ assoc _ _ _).
        apply maponpaths.
        apply pathsinv0.
        apply (bifunctor_equalwhiskers E).
        refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
        apply maponpaths.
        apply pathsinv0.
        apply (monoidal_braiding_naturality_left E).
      }
      apply cancel_postcomposition.
      refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _ @ _ @ assoc' _ _ _).
      apply cancel_postcomposition.
      apply (bifunctor_leftcomp E).
      apply maponpaths.
      apply (monoidal_associatorinvnatleft E).
      apply cancel_postcomposition.
      apply (monoidal_associatorinvnatleftright E).
    }
    apply assoc.
  }
  refine (monoidal_braiding_naturality_left E _ _ _ _ @ _).
  do 3 refine (_ @ assoc _ _ _).
  apply map_on_two_paths.
  apply maponpaths.
  rewrite (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (_ @ ! bifunctor_equalwhiskers E _ _ _ _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_leftcomp E).
  refine (sym_mon_tensor_lassociator E _ _ _ @ _).
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering E), (when_bifunctor_becomes_leftwhiskering E).
  do 2 refine (assoc' _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply pathsinv0.
  apply (sym_mon_hexagon_rassociator1 E).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply fmonoidal_preservesassociativity. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (! maponpaths (compose (C:=E) _) (functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  exact (assoc' _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  simpl.
  do 2 rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _ · _) (functor_comp K _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _ · _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! maponpaths (compose _) (functor_comp _ _ _) @ _).
  refine (! functor_comp (pr1 (pr211 E ((pr111 (linear_category_bang E)) U3))) _ _ @ _).
  apply maponpaths.
  unfold postcompose.
  set (dpb := tensor_doublePullback pb k
                  (((pr111 (linear_category_bang E)) U1,, # (pr111 (linear_category_bang E)) l1 · (pr121 L) R1),,
                   K ((pr111 (linear_category_bang C)) R1),, identity (K ((pr111 (linear_category_bang C)) R1)))
                  (((pr111 (linear_category_bang E)) U2,, # (pr111 (linear_category_bang E)) l2 · (pr121 L) R2),,
                   K ((pr111 (linear_category_bang C)) R2),, identity (K ((pr111 (linear_category_bang C)) R2)))).
  refine (doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _  @ ! doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  12 : {
    apply internal_lam.
    apply (compose (_ ⊗^{E}_{l} (# _ l1 · pr1 κ^{L} R1))).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose αinv^{E}_{_,_,_}).
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (_ ⊗^{E}_{l} # K (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _))).
    exact (pr1 k _ _).
    apply (compose (_ ⊗^{E}_{l} (# _ l3 · pr1 κ^{L} R3))).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose (_ ⊗^{E}_{l} # K (sym_mon_braiding C _ _ · fmonoidal_preservestensordata (linear_category_bang_functor C) _ _))).
    exact (pr1 k _ _).
  }
  12 : {
    apply (compose (_ ⊗^{E}_{l} (# _ l3 · pr1 κ^{L} R3))).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{l} (# K _)) _).
    refine (compose _ (# (linear_category_bang_functor C) α^{C}_{R1,R2,R3})).
    exact (sym_mon_braiding C _ _ · fmonoidal_preservestensordata (linear_category_bang_functor C) _ _).
    apply (compose (pr1 k _ _)).
    exact (# K (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _)).
  }
  12 : {
    apply internal_lam.
    unfold monoidal_cat_tensor_pt; simpl.
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (_ ⊗^{E}_{l} (# _ l3 · pr1 κ^{L} R3))).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{l} # K _) _).
    refine (compose _ (# _ α^{C}_{_,_,_})).
    refine (compose _ (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _)).
    apply (sym_mon_braiding C).
    apply (pr1 k).
    apply (compose (_ ⊗^{E}_{l} (# _ l2 · pr1 κ^{L} R2))).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose (_ ⊗^{E}_{l} # K (sym_mon_braiding C _ _ · fmonoidal_preservestensordata (linear_category_bang_functor C) _ _))).
    apply (pr1 k).
  }
  rewrite internal_lam_precomp.
  refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
  rewrite id_right.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) ).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  refine (_ @ functor_comp (pr1 (pr211 E ((pr111 (linear_category_bang E)) U1))) _ _).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
    apply maponpaths.
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    apply (bifunctor_leftcomp E).
    apply maponpaths.
    apply (pr12 k).
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    apply maponpaths.
    2 : {
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (bifunctor_equalwhiskers E).
    }
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    apply maponpaths.
    2 : {
      apply cancel_postcomposition.
      apply (monoidal_braiding_naturality_right E).
    }
    apply pathsinv0.
    apply (natural_contraction_composed k).
  }
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (pr12 k).
  apply maponpaths.
  apply (natural_contraction_composed k).
  do 4 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  do 3 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply (pr11 L).
  apply maponpaths.
  apply pathsinv0.
  apply (natural_contraction_extranatural k).
  apply assoc.
  do 2 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      apply pathsinv0.
      apply (bifunctor_rightcomp E).      
    }
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    apply maponpaths.
    2 : {
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (bifunctor_equalwhiskers E).
    }
    apply (monoidal_braiding_naturality_right E).
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _ )).
  2 : {
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _ )).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) _).
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      apply (bifunctor_leftcomp E).
      refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _ @ assoc' _ _ _).
      apply maponpaths.
      apply (bifunctor_equalwhiskers E).
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (monoidal_associatorinvnatleft E).
    }
    apply assoc'.
  }
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_leftcomp E).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply (monoidal_associatorinvnatleft E).
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  apply map_on_two_paths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorinvnatleft E).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  do 2 refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply map_on_two_paths.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite 2 assoc.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E), <- (when_bifunctor_becomes_rightwhiskering E).
  apply (sym_mon_hexagon_rassociator E).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths (compose (C:=E)) (! functor_comp K _ _) (! functor_comp K _ _) @ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ assoc _ _ _ @ _).
    2 : {
      apply cancel_postcomposition.
      refine (assoc _ _ _ @ _ @ assoc' _ _ _).
      apply cancel_postcomposition.
      apply (monoidal_braiding_naturality_left C).
    }
    apply maponpaths.
    apply pathsinv0.
    apply fmonoidal_preservesassociativity.
  }
  do 2 refine (_ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (maponpaths (compose _) (bifunctor_leftcomp C _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  rewrite <- (when_bifunctor_becomes_leftwhiskering C), <- (when_bifunctor_becomes_rightwhiskering C).
  apply pathsinv0.
  apply (sym_mon_hexagon_lassociator C). (* completes subgoal *)
  rewrite internal_lam_precomp.
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id _ _)).
  rewrite id_right.
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  refine (! functor_comp (pr1 (pr211 E ((pr111 (linear_category_bang E)) U2))) _ _ @ _).
  apply maponpaths.
  repeat refine (assoc _ _ _ @ _).
  repeat refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  do 3 refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  do 2 refine (_ @ assoc _ _ _).
  repeat refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  apply maponpaths.
  rewrite assoc.
  rewrite (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (compose _)).
  apply maponpaths.
  exact (! functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite doublePullbackArrow_PrL.
  rewrite assoc.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  refine (! functor_comp (pr1 (pr211 E _)) _ _ @ _).
  apply maponpaths.
  simpl.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) _ @ _ @ assoc' _ _ _).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _  @ _).
  do 3 refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (pr12 k).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (natural_contraction_composed k _ _ _) @ _).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (bifunctor_equalwhiskers E).
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply (monoidal_braiding_naturality_right E).    
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition.
    refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
    refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    apply (pr12 k).
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (! natural_contraction_composed k _ _ _)).
  refine (maponpaths (compose _) _ @ _).
  do 3 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply (fsym_respects_braiding L).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (natural_contraction_extranatural k).
  do 4 refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_leftcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  do 2 refine (assoc' _ _ _ @ _).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply (monoidal_associatorinvnatleft E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_leftcomp E).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_leftcomp E).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
      2 : {
        apply cancel_postcomposition.
        refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
        2 : {
          apply cancel_postcomposition.
          refine (_ @ maponpaths (λ f, f · _) _).
          2 : {
            apply maponpaths.
            apply (bifunctor_leftcomp E).
          }
          apply pathsinv0.
          apply (monoidal_associatorinvnatleft E).          
        }
        apply maponpaths.
        apply (bifunctor_equalwhiskers E).
      }
      apply maponpaths.
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      apply (bifunctor_leftcomp E).
    }
    apply maponpaths.
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    apply (bifunctor_equalwhiskers E).
  }
  do 2 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ assoc' _ _ _).
  apply map_on_two_paths.
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_left E).
  refine (assoc' _ _ _ @ _).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  2 : {
    apply (monoidal_associatorinvnatleft E).
  }
  do 2 refine (_ @ assoc' _ _ _).
  rewrite  <- (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ maponpaths (λ f, f · _) (! sym_mon_hexagon_rassociator E _ _ _)).
  refine (! id_right _ @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (! bifunctor_rightid E _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_inverses E).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths compose (! functor_comp K _ _) (! functor_comp K _ _) @ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left C).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply fmonoidal_preservesassociativity.
  do 2 refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  rewrite (bifunctor_leftcomp C).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _).
  apply (sym_mon_hexagon_lassociator C).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering C), (when_bifunctor_becomes_leftwhiskering C).
  refine (_ @ id_left _).
  repeat rewrite assoc.
  do 2 apply cancel_postcomposition.
  refine (! bifunctor_rightcomp C _ _ _ _ _ _ @ _ @ bifunctor_rightid C _ _).
  apply maponpaths.
  apply (monoidal_braiding_inverses C). (* completes subgoal *)
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, _ · f) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc'.
  apply maponpaths.
  repeat rewrite assoc.
  reflexivity.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (compose (C:=E) f  _)) (functor_comp K _ _) @ _).
  rewrite assoc.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  refine (! functor_comp (pr1 (pr211 E _)) _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  simpl.
  rewrite (bifunctor_rightcomp E).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  exact (! bifunctor_equalwhiskers E _ _ _ _ _ _).
  rewrite doublePullbackArrow_PrL.
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  do 2 rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, _ · f) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  rewrite (monoidal_associatorinvnatright E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  exact (! bifunctor_equalwhiskers E _ _ _ _ _ _).
  rewrite doublePullbackArrow_PrM.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  exact (! bifunctor_equalwhiskers E _ _ _ _ _ _).
  rewrite doublePullbackArrow_PrR.
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (_ @ assoc _ _ _ ).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ ).
  apply maponpaths.
  exact (! bifunctor_equalwhiskers E _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold postcompose.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, f · _ · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ maponpaths (λ f, internal_lam f) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, internal_lam (f · _)) (monoidal_associatorinvnatright E _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, internal_lam f) (assoc _ _ _)).
  unfold internal_lam.
  refine (_ @ ! maponpaths (compose _) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (uncurry_unit _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (compose _) (uncurry_nat3 _ _ _)).
  refine (_ @ assoc' _ _ _).
  do 3 refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ internal_postcomp_comp _ _ _).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! maponpaths (λ f, f · _ · _) (internal_postcomp_comp _ _ _) @ _).
  refine (! maponpaths (λ f, f · _) (internal_postcomp_comp _ _ _) @ _).
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  rewrite assoc'.
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  simpl.
  refine (! functor_comp _ _ _ @ _).  
  rewrite hom_onmorphisms_is_postcomp.
  apply maponpaths.
  unfold postcompose.
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  repeat rewrite assoc.
  reflexivity.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (! maponpaths (compose (C:=E) _) (functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply pathsinv0.
  apply (fmonoidal_preservesassociativity (linear_category_bang_functor C)). (*completes subgoal*)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  unfold postcompose, monoidal_cat_tensor_pt, monoidal_cat_tensor_mor.
  now rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (internal_lam_natural _ _ @ _).
  unfold postcompose, monoidal_cat_tensor_pt, monoidal_cat_tensor_mor.
  apply maponpaths.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (! internal_postcomp_comp _ _ _ @ _)).
  apply maponpaths.
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (_ @ internal_lam_tensor_eval _).
  apply cancel_postcomposition.
  apply maponpaths.
  refine (_ @ internal_lam_lam_swap _).
  apply cancel_postcomposition.
  apply (maponpaths internal_lam).
  do 2 refine (assoc _ _ _ @ _).
  apply internal_lam_natural.
  apply internal_lam_natural.
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  unfold postcompose.
  do 4 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _ @ _).
  unfold postcompose.
  apply internal_lam_natural.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply (monoidal_associatorinvnatright E).
  refine (maponpaths (compose _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (functor_comp K).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (internal_lam_tensor_eval _ @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ maponpaths (λ f, f · _) (! sym_mon_tensor_rassociator E _ _ _)).
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering E), (when_bifunctor_becomes_leftwhiskering E).
  refine (! id_right _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorisolaw E). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (_ @ assoc' _ _ _).
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  apply cancel_postcomposition.
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (_ @ maponpaths (compose _) _).
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  apply map_on_two_paths.
  3 : {
    refine (_ @ maponpaths (compose _) _).
    2 : {
      refine (assoc _ _ _ @ _ @ assoc' _ _ _@ _).
      2 : {
        apply maponpaths.
        apply (pr12 k).
      }
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (bifunctor_equalwhiskers E).
    }
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (monoidal_braiding_naturality_right E).
  }
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (map_on_two_paths (compose (C:=E)) (! functor_comp K _ _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply (monoidal_braiding_naturality_left C).
  }
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply pathsinv0.
  apply fmonoidal_preservesassociativity.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _ @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (functor_comp K).
  refine (_ @ internal_lam_natural _ _).
  apply maponpaths.
  apply internal_lam_precomp.
  do 2 refine (assoc _ _ _ @ _ ).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (_ @ ! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply internal_lam_precomp.
  apply maponpaths.
  apply internal_lam_curry.
  refine (internal_lam_tensor_eval _ @ _).
  apply maponpaths.
  unfold postcompose, monoidal_cat_tensor_mor, monoidal_cat_tensor_pt;
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  
  refine (_ @ maponpaths (λ f, f · _) _).
  refine (_ @ assoc _ _ _).
  2 : {
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ assoc' _ _ _).
  }
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply (monoidal_braiding_naturality_right E).
    }
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
      refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
      apply maponpaths.
      apply (pr12 k).
    }
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply (bifunctor_equalwhiskers E).
    }
    apply maponpaths.
    refine (_ @ ! natural_contraction_composed k _ _ _).
    do 3 refine (_ @ assoc _ _ _).
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (bifunctor_equalwhiskers E).
    }
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
      refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
      apply maponpaths.
      apply pathsinv0.
      apply (fsym_respects_braiding L).
    }
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply (natural_contraction_extranatural k).
  }
  refine (_ @ assoc' _ _ _).
  do 2 refine (assoc _ _ _ @ _).  
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  simpl.
  rewrite functor_comp.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply maponpaths.
  apply functor_comp.
  apply cancel_postcomposition.
  apply pathsinv0.
  apply fmonoidal_preservestensornatright.
  apply maponpaths.
  apply pathsinv0.
  apply fmonoidal_preservestensornatleft.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  apply assoc.
  apply maponpaths.
  apply (pr12 (pr222 L) R2 R3). (* κ^{L} is monoidal *)
  apply maponpaths.
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply assoc.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (natural_contraction_extranatural k).
  do 4 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  do 4 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_leftcomp E).
  do 3 refine (_ @ assoc _ _ _).
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply cancel_postcomposition.
    apply (monoidal_braiding_naturality_right E).
  }
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
      refine (_ @ ! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
      2 : {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply cancel_postcomposition.
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      apply maponpaths.
      apply (bifunctor_equalwhiskers E).
      }
      apply maponpaths.
      apply maponpaths.
      apply (bifunctor_leftcomp E).
    }
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply (bifunctor_equalwhiskers E).      
    }
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
      2 : {
        apply cancel_postcomposition.
        apply pathsinv0.
        apply (monoidal_associatorinvnatleft E).
      }
      apply maponpaths.
      apply (bifunctor_leftcomp E).
    }
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply (bifunctor_equalwhiskers E).       
    }
    apply maponpaths.
    apply (bifunctor_leftcomp E).    
  }
  do 3 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ assoc' _ _ _).
  apply map_on_two_paths.
  refine (maponpaths (compose _) _ @ _).
  apply (bifunctor_rightcomp E).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (_ @ _).
  apply pathsinv0.
  apply (bifunctor_rightcomp E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E). 
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_rightcomp E).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_leftcomp E).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
    3 : {
      apply maponpaths.
      apply pathsinv0.
      apply (monoidal_associatorinvnatright E).
    }
    2 : {
      apply cancel_postcomposition.
      refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
      2 : {
        apply cancel_postcomposition.
        apply pathsinv0.
        apply (bifunctor_leftcomp E).
      }
      apply maponpaths.
      apply pathsinv0.
      apply (monoidal_associatorinvnatleftright E).
    }
    apply maponpaths.
    apply (bifunctor_rightcomp E).
  }
  refine (_ @ assoc' _ _ _).
  apply map_on_two_paths.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    apply pathsinv0.
    refine (_ @ _).
    apply sym_mon_tensor_rassociator.
    do 2 refine (assoc' _ _ _ @ _).
    unfold monoidal_cat_tensor_mor;
      now rewrite (when_bifunctor_becomes_leftwhiskering E).
  }
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  rewrite 2 assoc.
  apply sym_mon_tensor_lassociator.
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  refine (_ @ map_on_two_paths (compose (C:=E)) (functor_comp K _ _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right C).  
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      refine (assoc _ _ _ @ _ @ assoc' _ _ _).
      apply cancel_postcomposition.
      refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
      apply maponpaths.
      apply (monoidal_braiding_naturality_left C).
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (bifunctor_leftcomp C).
    }
    apply maponpaths.
    refine (assoc _ _ _ @ _).
    apply pathsinv0.
    apply fmonoidal_preservesassociativity.
  }
  do 2 refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  rewrite <- (monoidal_braiding_naturality_left C).
  refine (sym_mon_tensor_rassociator C _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering C), (when_bifunctor_becomes_leftwhiskering C).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (sym_mon_tensor_lassociator1 C _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  apply (monoidal_associatorisolaw C).
Qed.

Lemma double_glued_total_bang_preserves_leftunitality {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  preserves_leftunitality (fmonoidal_preservestensordata
                             (double_glued_total_bang_preserves_tensor pb L k,,
                                double_glued_total_bang_preserves_unit pb L k))
    (fmonoidal_preservesunit
       (double_glued_total_bang_preserves_tensor pb L k,,
          double_glued_total_bang_preserves_unit pb L k)).
Proof.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k);
    split3; try apply fmonoidal_preservesleftunitality.
  apply doublePullbackArrowUnique.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  apply maponpaths.
  apply internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt, postcompose;
    rewrite (when_bifunctor_becomes_rightwhiskering E).  
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply (pr2 (pr222 L)). (* κ^{L} is monoidal *)
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (natural_contraction_extranatural k).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _).
  refine (_ @ maponpaths (compose _) (natural_contraction_unit k _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ sym_mon_braiding_lunitor E _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ id_left _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_leftid E _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths (compose (C:=E)) (! functor_comp K _ _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _ @ functor_id K _).
  apply maponpaths.
  refine (_ @ pr2 (monoidal_leftunitorisolaw C _)).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @_ ).
  apply fmonoidal_preservesleftunitality. (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _ @ ! id_left _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (assoc _ _ _ @  _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply fmonoidal_preservesleftunitality. (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply internal_lam_postcomp.
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt, postcompose;
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (pr12 k).
  refine (internal_lam_natural _ _ @ _ @ ! id_left _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  do 2 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  do 2 refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  apply cancel_postcomposition.
  apply (monoidal_braiding_naturality_left E).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_equalwhiskers E _ _ _ _ _ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_rightcomp E).
  apply maponpaths.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (map_on_two_paths (compose (C:=E)) (! functor_comp K _ _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) _ @ _).
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left C).
  refine (_ @ sym_mon_braiding_lunitor C _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply fmonoidal_preservesleftunitality.
Qed.

Lemma double_glued_total_bang_preserves_rightunitality {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  preserves_rightunitality (fmonoidal_preservestensordata
                             (double_glued_total_bang_preserves_tensor pb L k,,
                                double_glued_total_bang_preserves_unit pb L k))
    (fmonoidal_preservesunit
       (double_glued_total_bang_preserves_tensor pb L k,,
          double_glued_total_bang_preserves_unit pb L k)).
Proof.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k);
    split3; try apply fmonoidal_preservesrightunitality.
  apply doublePullbackArrowUnique.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  refine (maponpaths (compose _) _ @ _).
  apply internal_lam_postcomp.
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt, postcompose;
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (pr12 k).
  refine (internal_lam_natural _ _ @ _ @ ! id_left _).
  rewrite internal_lam_precomp.
  refine (_ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  do 2 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  do 2 refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  apply cancel_postcomposition.
  apply (monoidal_braiding_naturality_left E).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (bifunctor_equalwhiskers E).
  apply cancel_postcomposition.
  refine (_ @ ! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (bifunctor_rightcomp E).
  apply maponpaths.
  refine (_ @ ! functor_comp K _ _ @ _).
  apply (cancel_postcomposition (C:=E)).
  apply pathsinv0.
  apply (functor_comp K).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply fmonoidal_preservesrightunitality. (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _ @ ! id_left _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (assoc _ _ _ @  _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply fmonoidal_preservesrightunitality. (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (_ @ internal_lam_natural _ _ @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply internal_lam_precomp.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt, postcompose;
    rewrite (when_bifunctor_becomes_rightwhiskering E).  
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  apply (pr22 (pr222 L)). (* κ^{L} is monoidal *)
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (natural_contraction_extranatural k).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc _ _ _ @ _).
  refine (_ @ maponpaths (compose _) (natural_contraction_unit k _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  refine (_ @ sym_mon_braiding_lunitor E _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ id_left _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  refine (_ @ bifunctor_leftid E _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (_ @ ! functor_comp K _ _ @ _).
  apply (map_on_two_paths (compose (C:=E))).
  refine (_ @ ! functor_comp K _ _).
  apply (maponpaths (compose (C:=E) _)).
  apply pathsinv0.
  apply (functor_comp K).
  apply pathsinv0.
  apply (functor_comp K).
  refine (_ @ functor_id K _).
  apply maponpaths.
  refine (_ @ pr2 (monoidal_leftunitorisolaw C _)).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _ ).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right C).
  refine (assoc' _ _ _ @ _).
  refine (_ @ sym_mon_braiding_runitor C _).
  apply maponpaths.
  refine (assoc _ _ _ @_ ).
  apply fmonoidal_preservesrightunitality. (* completes subgoal *)
Qed.

Lemma double_glued_total_bang_laxlaws {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : fmonoidal_laxlaws (double_glued_total_bang_preserves_tensor pb L k,, double_glued_total_bang_preserves_unit pb L k).
Proof.
  split5.
  exact (double_glued_total_bang_preserves_tensor_nat_left pb L k).
  exact (double_glued_total_bang_preserves_tensor_nat_right pb L k).
  exact (double_glued_total_bang_preserves_associativity pb L k).
  exact (double_glued_total_bang_preserves_leftunitality pb L k).
  exact (double_glued_total_bang_preserves_rightunitality pb L k).
Qed.

Lemma double_glued_total_bang_is_symmetric_monoidal_functor {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  is_symmetric_monoidal_functor (double_glued_total_symmetric pb L K k) (double_glued_total_symmetric pb L K k)
    ((double_glued_total_bang_preserves_tensor pb L k,, double_glued_total_bang_preserves_unit pb L k),, double_glued_total_bang_laxlaws pb L k).
Proof.
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact (pr221 (linear_category_bang C) R1 R2).
  exact (pr221 (linear_category_bang E) _ _).
  set (dpb := tensor_doublePullback pb k
                  (((pr111 (linear_category_bang E)) U1,, # (pr111 (linear_category_bang E)) l1 · (pr121 L) R1),,
                   K ((pr111 (linear_category_bang C)) R1),, identity (K ((pr111 (linear_category_bang C)) R1)))
                  (((pr111 (linear_category_bang E)) U2,, # (pr111 (linear_category_bang E)) l2 · (pr121 L) R2),,
                   K ((pr111 (linear_category_bang C)) R2),, identity (K ((pr111 (linear_category_bang C)) R2)))).
  refine (doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _  @ ! doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply internal_lam.
    apply (compose (_ ⊗^{E}_{l} (# _ l1 · pr1 κ^{L} R1))).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{l} (# K _)) _).
    refine (compose _ (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _)).
    exact (sym_mon_braiding C _ _).
    apply (pr1 k).
  }
  9 : {
    apply (# K).
    apply (compose (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _)).
    apply (# _).
    apply (sym_mon_braiding C).
  }
  9 : {
    apply internal_lam.
    unfold monoidal_cat_tensor_pt; simpl.
    apply (compose (_ ⊗^{E}_{l} (# _ l2 · pr1 κ^{L} R2))).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose (_ ⊗^{E}_{l} (# K (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _)))).
    apply (pr1 k).
  }
  rewrite internal_lam_precomp.
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
  rewrite id_right.
  simpl.
  refine ( _ @ functor_comp _ _ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  do 2 apply maponpaths.
  exact (pr221 (linear_category_bang C) R1 R2).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id _ _)).
  rewrite id_right.
  rewrite assoc.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  rewrite internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (compose _)).
  do 2 apply maponpaths.
  rewrite assoc'.
  refine (! maponpaths (compose _) (pr221 (linear_category_bang C) R1 R2) @ _).
  rewrite assoc.
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  exact (pr1 (monoidal_braiding_inverses C _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _ @ _).
  unfold postcompose.
  rewrite assoc.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  do 2 rewrite assoc'.
  apply maponpaths.
  exact (! bifunctor_equalwhiskers E _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  exact (pr221 (linear_category_bang C) R1 R2).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _ @ _).
  unfold postcompose.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  do 2 rewrite assoc'.
  apply maponpaths.
  exact (! bifunctor_equalwhiskers E _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold postcompose.
  rewrite assoc.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  do 2 rewrite assoc'.
  apply maponpaths.
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (compose _)).
  do 2 apply maponpaths.
  exact (! pr221 (linear_category_bang C) _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  unfold double_glued_total_bang_functor; simpl.
  refine (! functor_comp K _ _ @ _).
  reflexivity.
  simpl.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  unfold postcompose.
  rewrite assoc.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  rewrite assoc'.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (compose _)).
  do 2 apply maponpaths.
  rewrite assoc'.
  refine (! maponpaths (compose _) (pr221 (linear_category_bang C) R1 R2) @ _).
  rewrite assoc.
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  exact (pr1 (monoidal_braiding_inverses C _ _)).
Qed. 
 
