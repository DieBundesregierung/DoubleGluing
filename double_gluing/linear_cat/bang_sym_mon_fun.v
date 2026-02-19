Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalAdjunction.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.Monics.
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
  exact (pr1 (pr222 L) R1 R2).
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
  exact (pr2 (pr222 L)).
  use tpair.
  apply (# K).
  exact (fmonoidal_preservesunit (linear_category_bang_functor C)).
  simpl.
  refine (id_left _ @ _).
  exact (! id_right _).
Defined.

Lemma double_glued_total_bang_laxlaws {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : fmonoidal_laxlaws (double_glued_total_bang_preserves_tensor pb L k,, double_glued_total_bang_preserves_unit pb L k).
Proof.
  split5.
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
  13 : {
  apply internal_lam.
  apply (compose (sym_mon_braiding E _ _)).
  apply (compose ((# _ l1 · pr1 κ^{L} R1)⊗^{E}_{r} _)).
  apply (compose (_ ⊗^{E}_{l} # K (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R3))).
  apply (compose (pr1 k _ _)).
  apply (# K).
  exact (# _ f23).
  }
  13 : {
  apply (# K).
  apply (compose (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R2)).
  apply (# _).
  exact (R1 ⊗^{C}_{l} f23).
  }
  13 : {
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
  set (keq := pr122 k (pr111 (linear_category_bang C) R1) _ _ (# (pr111 (linear_category_bang C)) f23));
    unfold rightwhiskering_on_morphisms, leftwhiskering_on_morphisms in keq; generalize keq; simpl; clear keq.
  do 2 rewrite id_right; intros keq.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) keq).
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
  assert (is_symmetric_monoidal_functor C C (lax_monoidal_from_symmetric_monoidal_comonad _ (linear_category_bang C))) as issymbang.
  admit. (* needs to be in the data somehow I assume *)
  refine (_ @ maponpaths (compose _) (issymbang _ _)).
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
  set ((pr222 (linear_category_bang C))).
  admit. (* this is the condition of !-bang respecting the symmetric structure *)
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
  set (keq := pr122 k (pr111 (linear_category_bang C) R1) _ _ (# (pr111 (linear_category_bang C)) f23));
    unfold rightwhiskering_on_morphisms, leftwhiskering_on_morphisms in keq; generalize keq; simpl; clear keq.
  do 2 rewrite id_right; intros keq.
  refine (_ @ maponpaths (compose _) keq); clear keq.
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
  admit. (* that's symmetry of the bang functor*) (* completes "preserves_tensor_nat_right" *)
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
  12 : {
    apply internal_lam.
    apply (compose (_ ⊗^{E}_{l} (# _ (l1 · # L f12) · pr1 κ^{L} _)) ).
    apply (compose (# K (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R2 R3) ⊗^{E}_{r} _) ).
    apply (compose (sym_mon_braiding E _ _)).
    unfold monoidal_cat_tensor_pt; simpl.
    exact (pr1 k _ _).
  }
  12 : {
    apply (# K).
    apply (compose (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R3)).
    apply (# _).
    exact (f12 ⊗^{C}_{r} R3).
  }
  12 : {
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
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))) (R3, ((U3, l3), (X3, l3'))).
  apply (double_glued_total_mor_eq_transp k); split3.
  apply fmonoidal_preservesassociativity. (* completes subgoal *)
  apply fmonoidal_preservesassociativity. (* completes subgoal *)
  (*
  set (dpb12 := tensor_doublePullback pb k
                             (((pr111 (linear_category_bang E)) U1,, # (pr111 (linear_category_bang E)) l1 · (pr121 L) R1),,
                              K ((pr111 (linear_category_bang C)) R1),, identity (K ((pr111 (linear_category_bang C)) R1)))
                             (((pr111 (linear_category_bang E)) U2,, # (pr111 (linear_category_bang E)) l2 · (pr121 L) R2),,
                                K ((pr111 (linear_category_bang C)) R2),, identity (K ((pr111 (linear_category_bang C)) R2)))).
  set (dpb12_3 := tensor_doublePullback pb k
                    (((pr111 (linear_category_bang E)) U1 ⊗_{ E} (pr111 (linear_category_bang E)) U2,,
                      (# (pr111 (linear_category_bang E)) l1 · (pr121 L) R1) ⊗^{ E} (# (pr111 (linear_category_bang E)) l2 · (pr121 L) R2)
                      · (pr112 L) ((pr111 (linear_category_bang C)) R1) ((pr111 (linear_category_bang C)) R2)),,
                     pr11 dpb12,,
                     doublePullbackPrM dpb12)
                    (((pr111 (linear_category_bang E)) U3,, # (pr111 (linear_category_bang E)) l3 · (pr121 L) R3),,
                     K ((pr111 (linear_category_bang C)) R3),, identity (K ((pr111 (linear_category_bang C)) R3)))). *)
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _  @ ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  11 : {
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
  11 :{
    apply (# K).
    apply (compose ((fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _) ⊗^{C}_{r} _)).
    apply (compose (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) _ _)).
    exact (# _ α^{C}_{_,_,_}).
  }
  11 : {
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
    simpl.
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
    admit.
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
    (* move #K's to the top : *)
    do 6 refine (assoc _ _ _ @ _ ).
    refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
    refine (maponpaths (compose _) _ @ _).
    refine (assoc' _ _ _ @ _ ).
    admit.
    admit.
    admit.
    admit.
  }
  simpl.
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
  admit.
  refine (assoc (C:=E) _ _ _ @ _).
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  simpl.
  rewrite internal_lam_precomp.
  unfold internal_lam.
  rewrite 2 hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  (*
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
  admit.
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
  14 : {
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
  14 : {
    apply (compose (_ ⊗^{E}_{l} (# _ l3 · pr1 κ^{L} R3))).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{l} (# K _)) _).
    refine (compose _ (# (linear_category_bang_functor C) α^{C}_{R1,R2,R3})).
    exact (sym_mon_braiding C _ _ · fmonoidal_preservestensordata (linear_category_bang_functor C) _ _).
    apply (compose (pr1 k _ _)).
    exact (# K (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _)).
  }
  14 : {
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
  simpl.
  admit.
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
  simpl.
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
  refine (maponpaths (λ f, compose (C:=E) (_ ⊗^{E}_{l} f) _) (assoc' _ _ _) @ _).
  admit.
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
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  unfold postcompose, internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  repeat rewrite assoc.
  admit.
  admit.
  admit.
*)
Admitted.

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
