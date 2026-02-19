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
Require Import double_gluing.linear_cat.bang_sym_mon_fun.



Lemma double_glued_total_bang_comonad_comult_eq1 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E){K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R):
  (pr111 (pr12 (linear_category_bang E))) (pr11 dr)
  · (# (pr111 (linear_category_bang E)) (# (pr111 (linear_category_bang E)) (pr21 dr) · (pr121 L) R) · (pr121 L) ((pr111 (linear_category_bang C)) R)) =
    # (pr111 (linear_category_bang E)) (pr21 dr) · (pr121 L) R · # L ((pr111 (pr12 (linear_category_bang C))) R).
Proof.
  destruct dr as ((U, l), (X, l')).
  simpl.
  refine (maponpaths (λ f, _ · (f · _)) (functor_comp _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) ((pr211 (pr12 (linear_category_bang E))) _ _ l) @ _).
  repeat rewrite assoc'.
  apply maponpaths.
  admit.
Admitted.

Lemma double_glued_total_bang_comonad_comult_is_nat_trans {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  is_nat_trans (double_glued_total_bang_functor_data pb L k)
    (functor_composite_data (double_glued_total_bang_functor_data pb L k) (double_glued_total_bang_functor_data pb L k))
    (λ x : ∑ x : C, double_glued_ob L K x,
          (pr111 (pr12 (linear_category_bang C))) (pr1 x),,
     ((pr111 (pr12 (linear_category_bang E))) (pr112 x),, double_glued_total_bang_comonad_comult_eq1 pb L k (pr2 x)),,
     # K ((pr111 (pr12 (linear_category_bang C))) (pr1 x)),,
     id_right (# K ((pr111 (pr12 (linear_category_bang C))) (pr1 x))) @ ! id_left (# K ((pr111 (pr12 (linear_category_bang C))) (pr1 x)))).
Proof.
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))).
  intros (f, ((ϕ, eqphi), (ψ, eqpsi))).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact ((pr211 (pr12 (linear_category_bang C))) _ _ f).
  exact ((pr211 (pr12 (linear_category_bang E))) _ _ ϕ).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  exact ((pr211 (pr12 (linear_category_bang C))) _ _ f).
Qed.

Definition double_glued_total_bang_comonad_comult {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) :
  double_glued_total_bang_functor pb L k ⟹ double_glued_total_bang_functor pb L k ∙ double_glued_total_bang_functor pb L k.
Proof.
  use tpair.
  intros (R, dr).
  use tpair.
  apply (linear_category_bang C).
  split; use tpair.
  apply (linear_category_bang E).
  exact (double_glued_total_bang_comonad_comult_eq1 pb L k dr).
  unfold double_glued_mor_comp2; simpl.
  apply (# K).
  apply (linear_category_bang C).
  exact (id_right _ @ ! id_left _).
  exact (double_glued_total_bang_comonad_comult_is_nat_trans pb L k).
Defined.

Lemma double_glued_total_bang_comonad_counit_eq1 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R):
  (pr121 (pr12 (linear_category_bang E))) (pr11 dr) · (pr21 dr) =
    # (pr111 (linear_category_bang E)) (pr21 dr) · (pr121 L) R · # L ((pr121 (pr12 (linear_category_bang C))) R).
Proof.
  refine (! (pr221 (pr12 (linear_category_bang E))) _ _ _ @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
Admitted.

Lemma double_glued_total_bang_comonad_counit_is_nat_trans {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K):
  is_nat_trans (double_glued_total_bang_functor_data pb L k) (functor_identity_data (total_category_data (double_glued_data L K)))
    (λ x : ∑ x : C, double_glued_ob L K x,
     (pr121 (pr12 (linear_category_bang C))) (pr1 x),,
     ((pr121 (pr12 (linear_category_bang E))) (pr112 x),, double_glued_total_bang_comonad_counit_eq1 pb L k (pr2 x)),,
     compose (C:=E) (pr222 x) (# K ((pr121 (pr12 (linear_category_bang C))) (pr1 x))),, ! id_left (# K ((pr121 (pr12 (linear_category_bang C))) (pr1 x)) · pr222 x)).
Proof.
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))).
  intros (f, ((ϕ, eqphi), (ψ, eqpsi))).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact ((pr221 (pr12 (linear_category_bang C))) _ _ f).
  exact ((pr221 (pr12 (linear_category_bang E))) _ _ ϕ).
  revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  refine (assoc' (C:=E) _ _ _ @ _ @ assoc' (C:=E) _ _ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) eqpsi).
  refine (_ @ assoc (C:=E) _ _ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  exact ((pr221 (pr12 (linear_category_bang C))) _ _ f).
Qed.

Definition double_glued_total_bang_comonad_counit {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : double_glued_total_bang_functor pb L k ⟹ functor_identity (double_glued_total_sym_mon_closed_cat pb k).
Proof.
  use tpair.
  intros (R, dr).
  use tpair.
  apply (linear_category_bang C).
  split; use tpair.
  apply (linear_category_bang E).
  exact (double_glued_total_bang_comonad_counit_eq1 pb L k dr).
  unfold double_glued_mor_comp2.
  apply (compose (C:=E) (pr22 dr)).
  apply (# K).
  apply (linear_category_bang C).
  exact (! id_left _).
  exact (double_glued_total_bang_comonad_counit_is_nat_trans pb L k).
Defined.


Definition double_glued_total_bang_disp_Comonad_data {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E){K : functor C (E^opp)}
  (k : natural_contraction C E L K) : disp_Comonad_data (double_glued_total_bang_functor pb L k).
Proof.
  exists (double_glued_total_bang_comonad_comult pb L k).
  exact (double_glued_total_bang_comonad_counit pb L k).
Defined.

Lemma double_glued_total_bang_disp_Comonad_laws {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E){K : functor C (E^opp)}
  (k : natural_contraction C E L K) : disp_Comonad_laws (double_glued_total_bang_disp_Comonad_data pb L k).
Proof.
  split.
  split.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact (Comonad_law1 (T:= linear_category_bang C) R).
  exact (Comonad_law1 (T:= linear_category_bang E) (pr11 dr)).
  simpl.
  rewrite id_left.
  rewrite <- (functor_comp K).
  rewrite <- (functor_id K).
  apply maponpaths.
  exact (Comonad_law1 (T:= linear_category_bang C) R).
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact (Comonad_law2 (T:= linear_category_bang C) R).
  exact (Comonad_law2 (T:= linear_category_bang E) (pr11 dr)).
  simpl.
  rewrite <- (functor_comp K).
  rewrite <- (functor_id K).
  apply maponpaths.
  exact (Comonad_law2 (T:= linear_category_bang C) R).
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact (Comonad_law3 (T:= linear_category_bang C) R).
  exact (Comonad_law3 (T:= linear_category_bang E) (pr11 dr)).
  simpl.
  do 2 rewrite <- (functor_comp K).
  apply maponpaths.
  exact (Comonad_law3 (T:= linear_category_bang C) R).
Qed.

Lemma double_glued_total_bang_symmetric_monoidal_comonad_extra_laws {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  symmetric_monoidal_comonads_extra_laws
    ((double_glued_total_bang_preserves_tensor pb L k,, double_glued_total_bang_preserves_unit pb L k),, double_glued_total_bang_laxlaws pb L k)
    (double_glued_total_bang_comonad_comult pb L k) (double_glued_total_bang_comonad_counit pb L k).
Proof.
  split; split.
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))).
  apply (double_glued_total_mor_eq_transp k); split3.
  apply (pr122 (linear_category_bang C)).
  apply (pr122 (linear_category_bang E)).
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
    refine (compose (_ ⊗^{E}_{l} # K _ ) _).
    refine (compose _ (δ (linear_category_bang C) _)).
    exact (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _).
    exact (pr1 k _ _).
  }
  12 : {
    apply (# K).
    apply (compose (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _)).
    exact (δ (linear_category_bang C) _).
  }
  12 : {
    apply internal_lam.
    apply (compose (_ ⊗^{E}_{l} (# _ l2 · pr1 κ^{L} R2))).
    apply (compose (sym_mon_braiding E _ _)).
    refine (compose (_ ⊗^{E}_{l} # K _ ) _).
    refine (compose _ (δ (linear_category_bang C) _)).
    refine (compose _ (fmonoidal_preservestensordata (linear_category_bang_functor C) _ _)).
    exact (sym_mon_braiding C _ _).
    exact (pr1 k _ _).
  }
  rewrite internal_lam_precomp.
  refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
  rewrite id_right.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, compose (C:=E) f _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _)).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  simpl.
  refine (_ @ functor_comp _ _ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (! bifunctor_equalwhiskers E _ _ _ _ _ _).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id _ _)).
  rewrite id_right.
  rewrite assoc.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  rewrite internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
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
  exact (bifunctor_equalwhiskers E _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  unfold postcompose.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose (C:=E) _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite assoc'.
  refine (maponpaths (compose (C:=E) _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (bifunctor_equalwhiskers E _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  exact (! functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  unfold postcompose.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose (C:=E) _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite assoc'.
  refine (maponpaths (compose (C:=E) _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (bifunctor_equalwhiskers E _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold postcompose; simpl.
  refine (! maponpaths (compose (C:=E) _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite internal_lam_precomp.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, compose (C:=E) f _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  simpl.
  refine (maponpaths (compose _) (! functor_comp _ _ _) @ _).
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  do 2 refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite 2 assoc'.
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _ )@ _).
  refine (! maponpaths (compose _) (pr12 k _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _ ) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (pr1 (pr122 (linear_category_bang C)) R1 R2)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_comp K _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k ((pr111 (linear_category_bang C)) R2) _ _ ((pr111 (pr2 (linear_category_bang C))) R1)); simpl. rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (compose _) keq); clear keq.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  apply map_on_two_paths; apply maponpaths.
  rewrite assoc'.
  rewrite functor_comp.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) ((pr211 (pr12 (linear_category_bang E))) _ _ l1) @ _).
  rewrite assoc'.
  apply maponpaths.
  admit. (* One of the axioms that needs to be added : L is a morphisms of comonads *)
  exact (! functor_comp K _ _ ).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  unfold postcompose; simpl.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (! maponpaths (compose (C:=E) _) (functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  exact (! (pr1 (pr122 (linear_category_bang C)) R1 R2)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  unfold postcompose; simpl.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, compose (C:=E) f _ · _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, compose (C:=E) f _ · _) (functor_comp K _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite internal_lam_precomp.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, compose (C:=E) f _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  simpl.
  refine (maponpaths (compose _) (! functor_comp _ _ _) @ _).
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  do 2 refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite 2 assoc'.
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _ )@ _).
  refine (! maponpaths (compose _) (pr12 k _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _ ) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K (_ · f) · _)) (pr1 (pr122 (linear_category_bang C)) R1 R2)).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (assoc' _ _ _)).
  rewrite (bifunctor_equalwhiskers C).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K (f · _) · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K (f · _ · _) · _)) (monoidal_braiding_naturality_right C _ _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_comp K _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k ((pr111 (linear_category_bang C)) R1) _ _ ((pr111 (pr2 (linear_category_bang C))) R2)); simpl. rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (compose _) keq); clear keq.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  apply map_on_two_paths; apply maponpaths.
  rewrite assoc'.
  rewrite functor_comp.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) ((pr211 (pr12 (linear_category_bang E))) _ _ l2) @ _).
  rewrite assoc'.
  apply maponpaths.
  admit. (* One of the axioms that needs to be added : L is a morphisms of comonads *)
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).
  rewrite assoc'.
  reflexivity.
  apply (double_glued_total_mor_eq_transp k); split3.
  simpl.
  apply (pr2 (pr122 (linear_category_bang C))).
  apply (pr2 (pr122 (linear_category_bang E))).
  simpl.
  do 2 rewrite <- (functor_comp K).
  apply maponpaths.
  apply (pr2 (pr122 (linear_category_bang C))). (* completes subgoal *)
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))).
  apply (double_glued_total_mor_eq_transp k); split3.
  apply (pr1 (pr222 (linear_category_bang C))).
  apply (pr1 (pr222 (linear_category_bang E))).
  refine (_ @ ! id_right _).
  set (dpb := tensor_doublePullback pb k
                    (((pr111 (linear_category_bang E)) U1,, # (pr111 (linear_category_bang E)) l1 · (pr121 L) R1),,
                     K ((pr111 (linear_category_bang C)) R1),, identity (K ((pr111 (linear_category_bang C)) R1)))
                    (((pr111 (linear_category_bang E)) U2,, # (pr111 (linear_category_bang E)) l2 · (pr121 L) R2),,
                       K ((pr111 (linear_category_bang C)) R2),, identity (K ((pr111 (linear_category_bang C)) R2)))).
  refine (doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _  @ ! doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  10 : {
    apply (compose (doublePullbackPrL _)).
    apply (compose (internal_postcomp _ (compose (C:=E) l2' (# K (ε (linear_category_bang C) _))))).
    apply (internal_precomp (ε (linear_category_bang E) U1) _).
  }
  10 : {
    apply (compose (doublePullbackPrM _)).
    apply (# K).
    exact ((ε (linear_category_bang C) _) ⊗^{C} (ε (linear_category_bang C) _)).
  }
  10 : {
    apply (compose (doublePullbackPrR _)).
    apply (compose (internal_postcomp _ (compose (C:=E) l1' (# K (ε (linear_category_bang C) _))))).
    apply (internal_precomp (ε (linear_category_bang E) _)).
  }
  simpl.
  refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
  rewrite id_right.
  rewrite internal_postcomp_comp.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _ ) (doublePullbackSqrLCommutes (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite 2 internal_lam_precomp.
  refine (! maponpaths (compose (C:=E) _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  rewrite assoc.
  rewrite internal_lam_precomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _)).
  rewrite assoc'.
  refine (assoc' _ _ _  @ _).
  apply maponpaths.
  simpl.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
  apply maponpaths.
  rewrite assoc.
  rewrite <- (bifunctor_leftcomp E).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _ · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  do 2 rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! maponpaths (compose _) (pr12 k R1 _ _ _) @ _).
  rewrite 2 assoc.
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  unfold functoronmorphisms1.
  rewrite (functor_comp K).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k (linear_category_bang_functor C R2) _ _ (ε (linear_category_bang C) R1)); rewrite 2 id_right; simpl; intros keq.
  refine (_ @ ! maponpaths (compose _) keq); clear keq.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (bifunctor_rightcomp E).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (! pr2 (ε (linear_category_bang E)) _ _ l1 @ _).
  rewrite assoc'.
  apply maponpaths.
  admit. (* that's one of the axioms that need to be added : L is a comonad-morphism *)
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id _ _)).
  rewrite id_right.
  rewrite internal_postcomp_comp.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  set (sqr := doublePullbackSqrRCommutes (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))).
  refine (_ @ maponpaths (λ f, f · _) sqr); clear sqr.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _ ).
  rewrite assoc.
  rewrite 2 internal_lam_precomp.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite internal_lam_precomp.
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! functor_comp  _ _ _ @ _ @ maponpaths (compose _) (functor_comp _ _ _)).
  refine (_ @ functor_comp _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  do 2 refine (_ @ maponpaths (λ f, _ · f) (assoc _ _ _)).
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
  refine (_ @ maponpaths (compose _) (pr12 k R2 _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  rewrite (bifunctor_equalwhiskers C).
  refine (maponpaths (λ f, _  ⊗^{E}_{l} (# K f)· _) (assoc _ _ _) @ _).
  rewrite (monoidal_braiding_naturality_right C).
  refine (maponpaths (λ f, _  ⊗^{E}_{l} (# K f)· _) (assoc' _ _ _) @ _).
  rewrite (functor_comp K).
  refine (maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  generalize (pr122 k (linear_category_bang_functor C R1) _ _ (pr1 (ε (linear_category_bang C)) R2));
    rewrite 2 id_right; simpl; intros keq.
  refine (maponpaths (compose _) keq @ _); clear keq.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (! maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply map_on_two_paths; apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  exact (monoidal_braiding_naturality_left C _ _ _ _).
  refine (_ @ pr2 (ε (linear_category_bang E)) _ _ l2).
  rewrite assoc'.
  apply maponpaths.
  admit. (* again one of the things that needs to be added as axiom *)
  simpl; unfold postcompose.
  refine (assoc' (C:=E) _ _ _ @ _).
  rewrite (doublePullbackArrow_PrL dpb).
  generalize (doublePullbackSqrLCommutes (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))); simpl;
    intros sqr.
  rewrite internal_postcomp_comp.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) sqr); clear.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  rewrite (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _ ).
  refine (_ @ assoc' _ _ _).
  rewrite 2 internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  simpl.
  refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (pr12 k R1 _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  set (laws := symmetric_monoidal_comonad_extra_laws C (linear_category_bang C)).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} (# K f) · _) (pr12 laws R1 R2) @ _).
  simpl.
  rewrite id_right.
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f · _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  generalize (pr122 k ((pr111 (linear_category_bang C)) R2) _ _ (ε (linear_category_bang C) R1)); rewrite 2 id_right; simpl; intros keq.
  refine (maponpaths (compose _) keq @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (_ @ pr2 (ε (linear_category_bang E)) _ _ l1).
  rewrite assoc'.
  apply maponpaths.
  admit. (* one of the axioms again *)
  simpl; unfold postcompose.
  refine (assoc' (C:=E) _ _ _ @ _).
  rewrite (doublePullbackArrow_PrM dpb).
  rewrite assoc'.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (pr12 (symmetric_monoidal_comonad_extra_laws C (linear_category_bang C)) R1 R2 @ _).
  exact (id_right _).
  simpl; unfold postcompose.
  refine (assoc' (C:=E) _ _ _ @ _).
  rewrite (doublePullbackArrow_PrR dpb).
  generalize (doublePullbackSqrRCommutes (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))); simpl;
    intros sqr.
  rewrite internal_postcomp_comp.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) sqr); clear.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  rewrite (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _ ).
  refine (_ @ assoc' _ _ _).
  rewrite internal_lam_precomp.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite internal_lam_precomp.
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _)).
  rewrite assoc'.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  simpl.
  refine (! functor_comp _ _ _ @ _ @ maponpaths (compose _) (functor_comp _ _ _)).
  refine (_ @ functor_comp _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f) (assoc _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f) (assoc' _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).  
  refine (_ @ maponpaths (compose _) (pr12 k R2 _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ assoc' _ _ _).
  set (laws := symmetric_monoidal_comonad_extra_laws C (linear_category_bang C)).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} (# K (_ · f)) · _) (pr12 laws R1 R2) @ _).
  simpl.
  rewrite id_right.
  rewrite (bifunctor_equalwhiskers C).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} (# K f) · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} (# K (f · _)) · _) (monoidal_braiding_naturality_right C _ _ _ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} (# K f) · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f · _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f · _) (functor_comp K _ _)).
  refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} (# K f) · _) (monoidal_braiding_naturality_left C _ _ _ _)).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  generalize (pr122 k ((pr111 (linear_category_bang C)) R1) _ _ (ε (linear_category_bang C) R2)); rewrite 2 id_right; simpl; intros keq.
  refine (maponpaths (compose _) keq @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (_ @ pr2 (ε (linear_category_bang E)) _ _ l2).
  rewrite assoc'.
  apply maponpaths.
  admit. (* one of the axioms again *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL dpb _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  reflexivity.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM dpb _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  exact (! functor_comp K _ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR dpb _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  apply pathsinv0.
  exact (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _ ).
  apply (double_glued_total_mor_eq_transp k); split3.
  apply (pr2 (pr222 (linear_category_bang C))).
  apply (pr2 (pr222 (linear_category_bang E))).
  simpl.
  rewrite id_left.
  refine (! functor_comp K _ _ @ _).
  rewrite <- (functor_id K).
  apply maponpaths.
  apply (pr2 (pr222 (linear_category_bang C))).
Admitted.

Definition double_glued_total_bang {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : sym_monoidal_cmd (double_glued_total_sym_mon_closed_cat pb k).
Proof.
  use tpair.
  exists (double_glued_total_bang_functor pb L k).
  use tpair.
  use tpair.
  exists (double_glued_total_bang_preserves_tensor pb L k).
  exact (double_glued_total_bang_preserves_unit pb L k).
  exact (double_glued_total_bang_laxlaws pb L k).
  exact (double_glued_total_bang_is_symmetric_monoidal_functor pb L k).
  use tpair.
  exists (double_glued_total_bang_disp_Comonad_data pb L k).
  exact (double_glued_total_bang_disp_Comonad_laws pb L k).
  exact (double_glued_total_bang_symmetric_monoidal_comonad_extra_laws pb L k).
Defined.

