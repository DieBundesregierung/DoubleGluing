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
Require Import double_gluing.linear_cat.bang_comonad.

Lemma double_glued_total_linear_category_comult_eq1 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R) :
  double_glued_mor_eq1 L K (pr1 (double_glued_total_bang pb L k (R,, dr)))
    (pr1 (monoidal_cat_tensor_pt (double_glued_total_bang pb L k (R,, dr)) (double_glued_total_bang pb L k (R,, dr))))
    (pr2 (double_glued_total_bang pb L k (R,, dr)))
    (pr2 (monoidal_cat_tensor_pt (double_glued_total_bang pb L k (R,, dr)) (double_glued_total_bang pb L k (R,, dr))))
    (linear_category_comult C R) (linear_category_comult E (pr11 dr)).
Proof.
  destruct dr as ((U, l), (X, l')).
  simpl.
  rewrite assoc.
  unfold functoronmorphisms1.
  rewrite (bifunctor_leftcomp E).
  rewrite (bifunctor_rightcomp E).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f) · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · (f · _)) · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f) · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  rewrite assoc.
  rewrite assoc'.
  refine (! maponpaths (λ f, f · _) (linear_category_comult_nat l) @ _).
  rewrite assoc'.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  exact (! pr122 L R).
Qed.

Definition double_glued_total_linear_category_comult {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  ∏ x : double_glued_total_sym_mon_closed_cat pb k,
      pr1 (double_glued_total_sym_mon_closed_cat pb k) ⟦ double_glued_total_bang pb L k x,
          monoidal_cat_tensor_pt (double_glued_total_bang pb L k x) (double_glued_total_bang pb L k x) ⟧.
Proof.
  intros (R, dr).
  exists (linear_category_comult C R).
  use tpair.
  exists (linear_category_comult E (pr11 dr)).
  exact (double_glued_total_linear_category_comult_eq1 pb L k dr).
  use tpair.
  unfold double_glued_mor_comp2; simpl.
  apply (compose (doublePullbackPrM _)).
  apply (# K).
  exact (linear_category_comult C R).
  simpl.
  exact (! id_right _).
Defined.

Lemma double_glued_total_linear_category_counit_eq1 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R) :
  double_glued_mor_eq1 L K (pr1 (double_glued_total_bang pb L k (R,, dr))) (pr1 I_{ double_glued_total_sym_mon_closed_cat pb k})
    (pr2 (double_glued_total_bang pb L k (R,, dr))) (pr2 I_{ double_glued_total_sym_mon_closed_cat pb k}) (linear_category_counit C R)
    (linear_category_counit E (pr11 dr)).
Proof.
  simpl.
  destruct dr as ((U, l), (X, l')).
  simpl.
  show_id_type.
  rewrite <- (linear_category_counit_nat l).
  rewrite 2 assoc'.
  apply maponpaths.
  exact (! (pr12 L) R).
Qed.

Definition double_glued_total_linear_category_counit {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E)
  {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  ∏ x : double_glued_total_sym_mon_closed_cat pb k,
      pr1 (double_glued_total_sym_mon_closed_cat pb k) ⟦ double_glued_total_bang pb L k x, I_{ double_glued_total_sym_mon_closed_cat pb k} ⟧.
Proof.
  intros (R, dr).
  exists (linear_category_counit C R).
  use tpair.
  exists (linear_category_counit E (pr11 dr)).
  exact (double_glued_total_linear_category_counit_eq1 pb L k dr).
  use tpair.
  unfold double_glued_mor_comp2; simpl.
  apply (# K).
  exact (linear_category_counit C R).
  exact (id_left (C:=E) _ @ ! id_right (C:=E) _).
Defined.

Definition double_glued_total_linear_category_data {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : linear_category_data.
Proof.
  exists (double_glued_total_sym_mon_closed_cat pb k).
  exists (double_glued_total_bang pb L k).
  exists (double_glued_total_linear_category_comult pb L k).
  exact (double_glued_total_linear_category_counit pb L k).
Defined.

Lemma double_glued_total_linear_category_laws {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : linear_category_laws (double_glued_total_linear_category_data pb L k).
Proof.
  split13.
  intros (R1, dr1) (R2, dr2) (f, df).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_comult_nat.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (_ @ assoc (C:=E) _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  rewrite assoc'.
  apply linear_category_comult_nat.
  intros (R1, dr1) (R2, dr2) (f, df).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_counit_nat.
  refine (! functor_comp K _ _ @ _).
  apply (maponpaths (# K)).
  apply linear_category_counit_nat.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_comult_coalgebra_mor.
  refine (assoc (C:=E) _ _ _ @ _ @ functor_comp K _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (assoc' (C:=E) _ _ _) @ _).
  simpl.
  unfold double_glued_rightwhiskering_comp2, double_glued_leftwhiskering_comp2, postcompose; simpl.
  do 2 refine (maponpaths (compose _) (assoc (C:=E) _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (assoc' (C:=E) _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, _ · (_ · f) · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (compose (C:=E) f _)) (! functor_comp K _ _) @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply linear_category_comult_coalgebra_mor.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_counit_coalgebra_mor.
  simpl.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  apply linear_category_counit_coalgebra_mor.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_counit_comonoid_mor_counit.
  simpl.
  (*
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply linear_category_counit_comonoid_mor_counit.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_counit_comonoid_mor_comult.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (_ @ assoc (C:=E) _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' (C:=E) _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (_ @ maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (_ @ functor_comp K _ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite assoc'.
  apply linear_category_counit_comonoid_mor_comult.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_coassoc.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (assoc (C:=E) _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose (C:=E) _) (assoc' (C:=E) _ _ _) @ _).
  refine (assoc (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  do 2 refine (_ @ assoc' (C:=E) _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, compose (C:=E) _ f · _) (assoc (C:=E) _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f) · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, compose (C:=E) _ f · _) (assoc' (C:=E) _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _) · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, compose (C:=E) _ f · _) (assoc (C:=E) _ _ _)).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  repeat rewrite assoc'.  
  apply maponpaths.
  refine (_ @ maponpaths (λ f, _ · (compose (C:=E) _ f)) (functor_comp K _ _)).
  refine (_ @ maponpaths (compose (C:=E) _) (functor_comp K _ _)).
  refine (! maponpaths (compose (C:=E) _) (functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  rewrite assoc'.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  apply linear_category_coassoc.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_counitality.
  do 2 refine (assoc (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' (C:=E) _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' (C:=E) _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f) · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc (C:=E) _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc (C:=E) _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose (C:=E) _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc (C:=E) _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose (C:=E) _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite id_left.
  refine (! functor_comp K _ _ @ _).
  refine (_ @ functor_id K _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  apply linear_category_counitality.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_cocommutative.
  refine (assoc (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply linear_category_cocommutative.
  intros (R1, ((U1, l1),(X1, l1'))) (R2, ((U2, l2),(X2, l2'))).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_comult_preserves_tensor.
  set (dpb := tensor_doublePullback pb k
                    (((pr111 (linear_category_bang E)) U1,, # (pr111 (linear_category_bang E)) l1 · (pr121 L) R1),,
                     K ((pr111 (linear_category_bang C)) R1),, identity (K ((pr111 (linear_category_bang C)) R1)))
                    (((pr111 (linear_category_bang E)) U2,, # (pr111 (linear_category_bang E)) l2 · (pr121 L) R2),,
                     K ((pr111 (linear_category_bang C)) R2),, identity (K ((pr111 (linear_category_bang C)) R2)))).
  refine (doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _  @ ! doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  12 : {
    apply (compose (C:=E) (doublePullbackPrM _)).
    apply (compose (C:=E) (# K (linear_category_comult C (R1 ⊗_{ C} R2)))).
    apply internal_lam.
    apply (compose (_ ⊗^{E}_{l} (# _ l1 · pr1 κ^{L} R1))).
    apply (compose ((# K (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R2)) ⊗^{E}_{r} _ )).
    apply (compose (sym_mon_braiding E _ _)).
    apply (pr1 k).
  }
  12 : {
    apply (compose (C:=E) (doublePullbackPrM _)).
    apply (# K).
    apply (compose (fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R2)).
    exact (linear_category_comult C (R1 ⊗_{ C} R2)).
  }
  12 : {
    apply (compose (C:=E) (doublePullbackPrM _)).
    apply (compose (C:=E) (# K (linear_category_comult C (R1 ⊗_{ C} R2)))).
    apply internal_lam.
    apply (compose (_ ⊗^{E}_{l} (# _ l2 · pr1 κ^{L} R2))).
    apply (compose ((# K (sym_mon_braiding C _ _ · fmonoidal_preservestensordata (linear_category_bang_functor C) R1 R2)) ⊗^{E}_{r} _ )).
    apply (compose (sym_mon_braiding E _ _)).
    apply (pr1 k).
  }
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite (functor_comp K).
  refine (_ @ assoc (C:=E) _ _ _).
  apply maponpaths.
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
  repeat rewrite assoc.
  do 2 apply (maponpaths (postcompose _)).
  exact (! bifunctor_equalwhiskers E _ _ _ _ _ _).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite (functor_comp K).
  refine (assoc' (C:=E) _ _ _ @ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id _ _)).
  rewrite id_right.
  rewrite internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  do 2 apply (maponpaths (postcompose _)).
  exact (bifunctor_equalwhiskers E _ _ _ _ _ _).
  do 2 refine (assoc' (C:=E) _ _ _ @ _).
  do 2 apply maponpaths.
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _ @ _).
  refine (assoc (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  unfold postcompose.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (bifunctor_equalwhiskers E _ _ _ _ _ _).
  do 2 refine (assoc' (C:=E) _ _ _ @ _).
  apply maponpaths.
  rewrite (functor_comp K).
  apply (maponpaths (compose (C:=E) _)).
  apply (doublePullbackArrow_PrM). (* completes subgoal *)
  do 2 refine (assoc' (C:=E) _ _ _ @ _).
  do 2 apply maponpaths.
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _ @ _).
  rewrite assoc.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (assoc (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  unfold postcompose.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (bifunctor_equalwhiskers E _ _ _ _ _ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' (C:=E) _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc (C:=E) _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' (C:=E) _ _ _) @ _).
  refine (assoc (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f) · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f · _) · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _) · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  
  (_ (_ pr11)) _
  (* refine (! maponpaths (λ f, _ · (_ · f) · _) (internal_postcomp_comp _ _ _) @ _). *)
  admit.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  admit.
  admit.
  (* apply linear_category_comult_preserves_tensor. *)
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_comult_preserves_unit.
  refine (assoc' (C:=E) _ _ _ @ _ @ assoc (C:=E) _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrL _ _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (id_right _)).
  rewrite <- internal_postcomp_id.
  refine (_ @ ! maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  rewrite internal_lam_precomp.
  refine (_ @ maponpaths (compose (C:=E) _) (assoc' _ _ _)).
  rewrite <- internal_pre_post_comp_as_post_pre_comp.
  rewrite internal_pre_post_comp_as_pre_post_comp.
  refine (_ @ maponpaths (compose (C:=E) _) (assoc _ _ _)).
  rewrite assoc.
  rewrite internal_lam_precomp.
  unfold internal_lam.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (functor_comp (pr1 (pr211 E I_{ E})) _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_rightunitorinvnat E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr211 E I_{ E}))) _ _ _)).
  simpl.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f · _)) (id_right _)).
  rewrite <- (pr1 (monoidal_rightunitorisolaw E _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f · _)) (pr2 (counit_from_are_adjoints (pr2 (pr211 E I_{ E}))) _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  simpl.
  rewrite (monoidal_rightunitorinvnat E).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (rightunitors_eval_expand2 _)).
  rewrite id_left.
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f) (assoc _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (λ f, _ · f) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite sym_mon_braiding_rinvunitor.
  refine (_ @ ! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (pr2 (pr222 L))).
  rewrite (bifunctor_rightcomp E).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc _ _ _)).
  generalize (pr122 k (linear_category_bang_functor C I_{C}) _ _ (fmonoidal_preservesunit (linear_category_bang_functor C)));
    simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (λ f, _ · (_ · f · _)) keq); clear keq.
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _ · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · (f · _) · _)) (id_right _)).
  rewrite <- (bifunctor_leftid E).
  refine (_ @ maponpaths (λ f, _ · (_ · (_ · _ ⊗^{E}_{l} f · _) · _)) (functor_id K _)).
  rewrite <- (pr1 (monoidal_leftunitorisolaw C _)).
  rewrite (functor_comp K lu^{ C }_{_}).
  refine (_ @ ! maponpaths (λ f, _ · (_ · (_ · f · _) · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · (f · _) · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · (f · _ · _) · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · (f · _) · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f · _)) (pr1 (pr222 k) _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _ · _)) (functor_comp K _ _)).
  rewrite (monoidal_leftunitornat E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (monoidal_leftunitorisolaw E _))).
  rewrite id_left.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  rewrite assoc.
  rewrite <- (monoidal_leftunitorinvnat C).
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (bifunctor_equalwhiskers C _ _ _ _ _ _)). 
  apply linear_category_comult_preserves_unit.
  intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))).
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_counit_preserves_tensor.
  set (dpb := tensor_doublePullback pb k
                    (((pr111 (linear_category_bang E)) U1,, # (pr111 (linear_category_bang E)) l1 · (pr121 L) R1),,
                     K ((pr111 (linear_category_bang C)) R1),, identity (K ((pr111 (linear_category_bang C)) R1)))
                    (((pr111 (linear_category_bang E)) U2,, # (pr111 (linear_category_bang E)) l2 · (pr121 L) R2),,
                     K ((pr111 (linear_category_bang C)) R2),, identity (K ((pr111 (linear_category_bang C)) R2)))).
  refine (doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _  @ ! doublePullbackArrowUnique dpb _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  10 : {
    apply internal_lam.
    
    apply (compose (_ ⊗^{E}_{l} (# _ l1 · pr1 κ^{L} R1))).
    refine (compose ((# K _) ⊗^{E}_{r} _) _).
    refine (compose _ (ru^{C}_{ I_{C} } )).
    exact (linear_category_counit C R1 ⊗^{C}_{r} _).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose (pr1 k _ _)).
    apply (# K).
    exact (linear_category_counit C _).

    (*
    refine (compose (_ ⊗^{E}_{l} _) _).
    apply (compose (# _ l1)).
    exact (linear_category_counit E _).
    apply (compose (ru^{E}_{_})).
    apply (# K).
    exact (linear_category_counit C _).*)
  }
  10 : {
    apply (# K).
    apply (compose (linear_category_counit C _ ⊗^{C} linear_category_counit C _)).
    apply (ru^{C}_{_}).
  }
  10 : {
    apply internal_lam.
    
    apply (compose (_ ⊗^{E}_{l} (# _ l2 · pr1 κ^{L} R2))).
    refine (compose ((# K _) ⊗^{E}_{r} _) _).
    refine (compose _ (ru^{C}_{ I_{C} } )).
    exact (linear_category_counit C R2 ⊗^{C}_{r} _).
    apply (compose (sym_mon_braiding E _ _)).
    apply (compose (pr1 k _ _)).
    apply (# K).
    exact (linear_category_counit C _).

    (*
    refine (compose (_ ⊗^{E}_{l} _) _).
    apply (compose (# _ l2)).
    exact (linear_category_counit E _).
    apply (compose (ru^{E}_{_})).
    apply (# K).
    exact (linear_category_counit C _).*)    
  }
  rewrite internal_lam_precomp.
  refine (maponpaths (compose _) (internal_postcomp_id _ _) @ _).
  rewrite id_right.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _)).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  simpl.
  refine (_ @ functor_comp _ _ _).
  apply maponpaths.
  rewrite 2 assoc.
  refine (! maponpaths (compose _) (pr12 k _ _ _ _) @ _).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  rewrite <- (bifunctor_rightcomp E).
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  rewrite (bifunctor_equalwhiskers C).
  reflexivity.
  rewrite internal_lam_precomp.
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id _ _)).
  rewrite id_right.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr211 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply (maponpaths (compose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _).
  apply maponpaths.
  do 2 refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (pr12 k _ _ _ _)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  rewrite <- (bifunctor_rightcomp E).
  refine (_ @ bifunctor_equalwhiskers E _ _ _ _ _ _).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  rewrite assoc.
  rewrite (bifunctor_equalwhiskers C).
  apply (maponpaths (postcompose _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_right C _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ bifunctor_equalwhiskers C _ _ _ _ _ _).
  apply (maponpaths (compose _)).
  refine (monoidal_braiding_naturality_left C _ _ _ _ @ _).
  refine (_ @ id_right _).
  apply maponpaths.
  exact (sym_mon_braiding_id C).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL dpb _ _ _ _ _ _) @ _).
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
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (pr12 k _ _ _ _)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (compose _)).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  rewrite assoc.
  refine (linear_category_counit_preserves_tensor _ _ @ _).
  apply map_on_two_paths.
  apply (bifunctor_equalwhiskers C).
  rewrite <- id_left.
  refine (_ @ maponpaths (λ f, f · _) (sym_mon_braiding_id C)).
  apply pathsinv0.
  apply sym_mon_braiding_runitor. (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM dpb _ _ _ _ _ _) @ _).
  unfold postcompose.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (linear_category_counit_preserves_tensor _ _ @ _).
  apply maponpaths.
  rewrite <- id_left.
  refine (_ @ maponpaths (λ f, f · _) (sym_mon_braiding_id C)).
  apply pathsinv0.
  apply sym_mon_braiding_runitor. (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR dpb _ _ _ _ _ _) @ _).
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
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (pr12 k _ _ _ _)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (compose _)).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  rewrite assoc'.
  refine (maponpaths (compose _) (linear_category_counit_preserves_tensor _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _ · _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_right C _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  apply sym_mon_braiding_lunitor. (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrL dpb _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite <- internal_pre_post_comp_as_post_pre_comp.
  rewrite internal_pre_post_comp_as_pre_post_comp.
  rewrite assoc.
  rewrite internal_lam_precomp.
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! functor_comp (pr1 (pr211 E _)) _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite (functor_comp K).
  refine (_ @ ! maponpaths (λ f, _ · f · _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc' _ _ _)).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k (I_{C}) _ _ (linear_category_counit C R1)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (compose _) keq); clear keq.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · (_ ⊗^{E}_{l} # K f · _)) (sym_mon_braiding_lunitor C (I_{C}))).
  rewrite (sym_mon_braiding_id C).
  rewrite id_left.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f ⊗^{E}_{r} _) · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · (_ · f) ⊗^{E}_{r} _) · _) (pr12 L R1)).
  refine (_ @ maponpaths (λ f, (_ · f ⊗^{E}_{r} _) · _) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (pr1 (pr222 k) (I_{C}))).
  rewrite (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply map_on_two_paths.
  apply maponpaths.
  apply pathsinv0.
  apply linear_category_counit_nat.
  apply pathsinv0.
  apply (sym_mon_braiding_lunitor E). (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrM dpb _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (id_left _ @ _).
  do 2 apply maponpaths.
  rewrite <- id_left.
  refine (_ @ maponpaths (λ f, f · _) (sym_mon_braiding_id C)).
  apply pathsinv0.
  apply (sym_mon_braiding_runitor C). (* completes subgoal *)
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (doublePullbackArrow_PrR dpb _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  simpl.
  rewrite id_left.
  rewrite assoc.
  rewrite internal_lam_precomp.
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! functor_comp (pr1 (pr211 E _)) _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite (functor_comp K).
  refine (_ @ ! maponpaths (λ f, _ · f · _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc' _ _ _)).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k (I_{C}) _ _ (linear_category_counit C R2)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (compose _) keq); clear keq.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  do 2 rewrite <- (bifunctor_leftcomp E).
  apply maponpaths.
  rewrite assoc'.
  refine (_ @ ! maponpaths (compose _) (pr12 L R2)).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply linear_category_counit_nat. (* completes subgoal *)
  apply (double_glued_total_mor_eq_transp k); split3; try apply linear_category_counit_preserves_unit.
  refine (! functor_comp K _ _ @ _).
  refine (_ @ functor_id K _).
  apply maponpaths.
  apply linear_category_counit_preserves_unit.
*)
Admitted.

Definition double_glued_total_linear_category {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : linear_category.
Proof.
  exists (double_glued_total_linear_category_data pb L k).
  exact (double_glued_total_linear_category_laws pb L k).
Defined.





