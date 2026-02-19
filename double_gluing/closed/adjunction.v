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


Local Lemma double_glued_hom_adjunction_unit_comp1_lemma1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  unit_from_are_adjoints (pr2 (pr2 E (pr11 dr))) (pr11 ds) · internal_postcomp (pr11 dr) (pr21 (double_glued_tensor_product pb L K k S R ds dr)) =
    (pr21 ds) · # L (unit_from_are_adjoints (pr2 (pr2 C R)) S) ·
      (internal_lam ((fmonoidal_preservestensordata L) (internal_hom R (S ⊗_{ pr211 C} R)) R · # L (internal_eval R (S ⊗_{ pr211 C} R))) ·
         internal_precomp (pr21 dr) (L (S ⊗_{ pr211 C} R))).
Proof.
  destruct dr as ((U, l), (X, l')).
  destruct ds as ((V, m), (Y, m')).
  unfold double_glued_tensor_product, internal_lam, functoronmorphisms1; simpl.
  rewrite (maponpaths (internal_postcomp U) (assoc' _ _ _)).
  rewrite internal_postcomp_comp.
  rewrite assoc.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E U))) _ _ m) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  show_id_type.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  rewrite assoc.
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (L R)))) _ _ _)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp (L R) _ _)).
  refine (_ @ ! maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  rewrite assoc.
  rewrite (maponpaths (internal_postcomp U) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_postcomp U (f · _))) (fmonoidal_preservestensornatright L S _ R (unit_from_are_adjoints (pr2 (pr2 C R)) S))).
  rewrite (maponpaths (internal_postcomp U) (assoc' _ _ _)).
  do 2 rewrite (internal_postcomp_comp U).
  rewrite <- (functor_comp L).
  refine (_ @ ! maponpaths (λ f, _ · (_ · internal_postcomp U (# L f))) (triangle_id_left_ad (pr2 (pr2 C R)) S) ).
  rewrite functor_id.
  rewrite internal_postcomp_id.
  rewrite id_right.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (mon_closed_adj_natural E (L S) _ _ _).
Qed.

Local Lemma double_glued_hom_adjunction_unit_comp1_lemma2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K)  {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  (pr21 ds) · # L (unit_from_are_adjoints (pr2 (pr2 C R)) S) · (internal_lam (L (internal_hom R (S ⊗_{ pr211 C} R)) ⊗^{ E}_{l} # K (internal_eval R (S ⊗_{ pr211 C} R)) · pr1 k (internal_hom R (S ⊗_{ pr211 C} R)) R) · internal_precomp (pr22 (double_glued_tensor_product pb L K k S R ds dr)) (K R)) =
    internal_lam ((pr11 ds) ⊗^{ E}_{l} doublePullbackPrL (tensor_doublePullback pb k ds dr) · (sym_mon_braiding E (pr11 ds) (internal_hom (pr11 ds) (pr12 dr)) · internal_eval (pr11 ds) (pr12 dr))) · internal_postcomp (pr12 (double_glued_tensor_product pb L K k S R ds dr)) (pr22 dr).
Proof.
  set (dpb := tensor_doublePullback pb k ds dr).
  destruct dr as ((U, l), (X, l')).
  destruct ds as ((V, m), (Y, m')).
  unfold internal_lam; simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · (_ · f))) (pr2 (counit_from_are_adjoints (pr2 (pr2 E V))) _ _ _)).
  simpl.
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp _ (_ · (_ · (f ⊗^{E}_{r} V · _)))) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp _ (_ · (f · _))) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (f · _)) (bifunctor_leftcomp E V _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp _ (V ⊗^{E}_{l} f · _)) (doublePullbackSqrLCommutes dpb)).
  unfold internal_lam.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f· _)) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints _) _ _ _) @ _).
  simpl.
  refine (assoc' _ _ _ @ _ ).
  apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ ).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ ).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_leftcomp E V _ _ _ _ _ )).
  refine (_ @ assoc _ _ _ ).
  apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, (V ⊗^{E}_{l} f · _)) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (V ⊗^{E}_{l} (_ · f) · _)) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ maponpaths (λ f, (V ⊗^{E}_{l} f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (V ⊗^{E}_{l} (f · _) · _)) (mon_closed_adj_natural E _ _ _ _)).
  refine (_ @ maponpaths (λ f, (V ⊗^{E}_{l} f · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (V ⊗^{E}_{l} (_ · f) · _)) (internal_postcomp_comp V _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E V _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E V))) _ _ _)).
  simpl.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (triangle_id_left_ad (pr2 (pr2 E V)) _)).
  rewrite id_left.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr1 (monoidal_braiding_inverses E _ _))).
  rewrite id_left.
  simpl.
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  generalize (pr122 k R _ _ (unit_from_are_adjoints (pr2 (pr2 C R)) S)); rewrite 2 id_right; simpl; intros keq.
  refine (! maponpaths (compose _) keq @ _).
  rewrite assoc.
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_leftcomp E (L S) _ _ _ _ _ @ _).
  rewrite <- (bifunctor_leftid E).
  apply maponpaths.
  refine (_ @ functor_id K _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  exact (triangle_id_left_ad (pr2 (pr2 C R)) _).
Qed.


Definition double_glued_hom_adjunction_unit_comp1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  double_glued_mor_comp1 L K S (pr1 (pr2 C R) (S ⊗_{ C} R)) ds (double_glued_disp_internal_hom_ob pb k dr (double_glued_tensor_product pb L K k S R ds dr)).
Proof.
  destruct dr as ((U, l), (X, l')).
  destruct ds as ((V, m), (Y, m')).
  unfold double_glued_mor_comp1, double_glued_disp_internal_hom_ob.
  use doublePullbackArrow.
  exact (unit_from_are_adjoints (pr2 (pr2 E U)) V).
  apply (compose m).
  exact (# L ((unit_from_are_adjoints (pr2 (pr2 C R)) S))).
  apply internal_lam.
  apply (compose (V ⊗^{E}_{l} doublePullbackPrL _)).
  apply (compose (sym_mon_braiding E _ _)).
  exact (internal_eval V X).
  exact (double_glued_hom_adjunction_unit_comp1_lemma1 pb k ((U,, l),, (X,, l')) ((V,, m),, (Y,, m'))).
  exact (double_glued_hom_adjunction_unit_comp1_lemma2 pb k ((U,, l),, (X,, l')) ((V,, m),, (Y,, m'))).
Defined.

Lemma double_glued_hom_adjunction_unit_eq1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  double_glued_mor_eq1 L K _ _ _ _ (unit_from_are_adjoints (pr2 (pr2 C R)) S) (double_glued_hom_adjunction_unit_comp1 pb k dr ds).
Proof.
  unfold double_glued_hom_adjunction_unit_comp1.
  apply doublePullbackArrow_PrM.
Qed.

Lemma double_glued_hom_adjunction_unit_eq2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  # K (unit_from_are_adjoints (pr2 (pr2 C R)) S) · (pr21 dr ⊗^{ E} doublePullbackPrM (tensor_doublePullback pb k ds dr) ·(L R ⊗^{ E}_{l} # K (sym_mon_braiding C R (pr1 (pr2 C R) (S ⊗_{ C} R)) · internal_eval R (S ⊗_{ C} R)) · pr1 k R (pr1 (pr2 C R) (S ⊗_{ C} R)))) =
    pr22 ds · (pr11 dr ⊗^{ E}_{l} doublePullbackPrR (tensor_doublePullback pb k ds dr) · (sym_mon_braiding E (pr11 dr) (internal_hom (pr11 dr) (pr12 ds)) · internal_eval (pr11 dr) (pr12 ds))).
Proof.
  destruct dr as ((U, l), (X, l')).
  destruct ds as ((V, m), (Y, m')).
  simpl.
  rewrite doublePullbackSqrMCommutes.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (_ @ assoc (C:=E) _ _ _).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U))) _ _ m')).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (monoidal_braiding_naturality_left E _ _ _ (internal_postcomp U m'))).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite <- (bifunctor_leftcomp E U).
  refine (_ @ maponpaths (λ f, U ⊗^{E}_{l} f · _) (doublePullbackSqrRCommutes _)).
  rewrite (bifunctor_leftcomp E U).
  refine (_ @ assoc _ _ _).
  rewrite (bifunctor_equalwhiskers E).
  refine (assoc' _ _ _ @ _).
(*
  It stops working from here:

  apply maponpaths.
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, U ⊗^{ E}_{l} (_ · f) · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, U ⊗^{ E}_{l} (_ · (_ · f)) · _)
            (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ maponpaths (λ f, U ⊗^{ E}_{l} (_ · f) · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, U ⊗^{ E}_{l} (_ · (f · _)) · _) (mon_closed_adj_natural E _ _ _ l)).
  refine (_ @ maponpaths (λ f, U ⊗^{ E}_{l} (_ · f) · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, U ⊗^{ E}_{l} (_ · (_ · f)) · _) (internal_postcomp_comp U _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  unfold monoidal_cat_tensor_pt.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ · ( f ⊗^{ E}_{r} U · _)) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E U).
  rewrite <- (hom_onmorphisms_is_postcomp U).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · f) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U))) _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite (bifunctor_rightcomp E U).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (triangle_id_left_ad (pr2 (pr2 E U)) _)).
  rewrite id_left.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc'.
  refine (! maponpaths (compose _) (pr12 k R _ _ _) @ _).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · f) (pr1 (monoidal_braiding_inverses E _ _))).
  rewrite id_right.
  refine (! bifunctor_leftcomp E (L R) _ _ _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  refine (_ @ id_right _).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  exact (triangle_id_left_ad (pr2 (pr2 C R)) _).
Qed.
 *)
Admitted.

Definition double_glued_internal_hom_unit_data {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R : C} (dr : double_glued_cat L K R) :
 nat_trans_data (functor_identity (double_glued_total_sym_monoidal_cat pb L K k))
   (rightwhiskering_functor (double_glued_total_sym_monoidal_cat pb L K k) (R,, dr) ∙ double_glued_total_internal_hom pb k dr).
Proof.
  intros (S, ds).
  exists (unit_from_are_adjoints (pr2 (pr2 C R)) S).
  split.
  exists (double_glued_hom_adjunction_unit_comp1 pb k dr ds).
  exact (double_glued_hom_adjunction_unit_eq1 pb k dr ds).
  use tpair.
  unfold double_glued_mor_comp2; simpl.
  apply (compose (_ ⊗^{E}_{l} doublePullbackPrR _)).
  apply (compose (sym_mon_braiding E _ _)).
  exact (internal_eval _ _).
  exact (double_glued_hom_adjunction_unit_eq2 pb k dr ds).
Defined.

Lemma double_glued_total_mor_eq_transp {C E : sym_mon_closed_cat} {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {x y : ob (double_glued_total_cat L K)} (f g : x --> y) :
  (pr1 f = pr1 g) × (pr112 f = pr112 g) × (pr122 f = pr122 g) → f = g.
Proof.
  intros (eq1, (eq2, eq3)).
  use total2_paths_b.
  assumption.
  unfold transportb.
  About double_glued_mor_eq_transp.
  apply (pr2 (double_glued_mor_eq_transp eq1 (pr2 f) (pr2 g))).
  exact (eq2,, eq3).
Qed.

Lemma double_glued_internal_hom_unit_is_nat_trans {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R : C} (dr : double_glued_cat L K R) :
  is_nat_trans (functor_identity (double_glued_total_sym_monoidal_cat pb L K k))
    (rightwhiskering_functor (double_glued_total_sym_monoidal_cat pb L K k) (R,, dr) ∙ double_glued_total_internal_hom pb k dr)
    (double_glued_internal_hom_unit_data pb k dr).
Proof.
  intros (R1, dr1) (R2, dr2) (f12, df12).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact (pr2 (unit_from_are_adjoints (pr2 (pr2 C R))) _ _ _).
  simpl.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct df12 as ((ϕ12, eqphi), (ψ21, eqpsi)).
  unfold double_glued_hom_adjunction_unit_comp1, double_glued_disp_internal_hom_data_comp1;
    revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  unfold double_glued_mor_comp1, double_glued_disp_internal_hom_ob in *.
  set (hom_dpb := internal_hom_doublePullback pb k dr (double_glued_tensor_product pb L K k R2 R ((U2,, l2),, X2,, l2') dr)).
  set (tens_dpb := tensor_doublePullback pb k ((U2,, l2),, X2,, l2') dr).
  set (arr1 := ϕ12 · (unit_from_are_adjoints (pr2 (pr2 E (pr11 dr))) U2)).
  set (arr2 := l1 · (# L (f12 · unit_from_are_adjoints (pr2 (pr2 C R)) R2))).
  set (arr3 := internal_lam (ϕ12 ⊗^{E} doublePullbackPrL tens_dpb · sym_mon_braiding E _ _ · internal_eval U2 _)).
  refine (pathscomp0 (b:= doublePullbackArrow hom_dpb U1 arr1 arr2 arr3 _ _) _ _); [ | apply pathsinv0];
    apply (doublePullbackArrowUnique hom_dpb U1).
  rewrite assoc'.
  apply maponpaths.
  apply doublePullbackArrow_PrL. (* completes subgoal *)
  unfold arr2.
  rewrite (functor_comp L).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) eqphi).
  do 2 rewrite assoc'.
  apply maponpaths.
  apply doublePullbackArrow_PrM. (* completes subgoal *)
  unfold arr3.
  unfold internal_lam.
  rewrite assoc'.
  refine (maponpaths (compose _) (doublePullbackArrow_PrR hom_dpb _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! functor_comp (pr1 (pr2 E (doublePullbackObject tens_dpb))) _ _ @ _).
  apply maponpaths.
  do 2 refine (_ @ assoc _ _ _).
  exact (idpath _).
  unfold arr1.
  refine (assoc' _ _ _ @ _).
  rewrite doublePullbackArrow_PrL.
  rewrite assoc.
  rewrite doublePullbackArrow_PrL.
  refine (_ @ ! pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply hom_onmorphisms_is_postcomp. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  rewrite doublePullbackArrow_PrM.
  rewrite assoc.
  rewrite doublePullbackArrow_PrM.
  rewrite assoc'.
  apply maponpaths.
  rewrite <- (functor_comp L).
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  apply pathsinv0.
  apply (pr2 (unit_from_are_adjoints (pr2 (pr2 C R)))). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  rewrite doublePullbackArrow_PrR.
  rewrite assoc.
  rewrite doublePullbackArrow_PrR.
  unfold arr3, double_glued_rightwhiskering_comp2; simpl.
  refine (assoc' _ _ _ @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, _ · internal_postcomp _ (f · _)) (bifunctor_leftcomp E U1 _ _ _ _ _) @ _).
  rewrite doublePullbackArrow_PrL.
  unfold internal_lam.
  apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  apply maponpaths.
  rewrite (bifunctor_equalwhiskers E).
  rewrite (bifunctor_leftcomp E U1).
  unfold functoronmorphisms2.
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite 2 assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite 2 assoc'.
  apply maponpaths.
  exact (mon_closed_adj_natural_co E (pr12 dr) _ _ ϕ12).
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct df12 as ((ϕ12, eqphi), (ψ21, eqpsi)).
  simpl.
  change (compose (C:=E) (pr11 dr ⊗^{ E}_{l} doublePullbackPrR (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') dr)
                                      · (sym_mon_braiding E (pr11 dr) (internal_hom (pr11 dr) X2) · internal_eval (pr11 dr) X2)) ψ21 =
            compose (C:=E) (pr11 dr ⊗^{ E}_{l} double_glued_rightwhiskering_comp2 pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') dr ((ϕ12,, eqphi),, ψ21,, eqpsi)) (pr11 dr ⊗^{ E}_{l} doublePullbackPrR (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') dr)
                        · (sym_mon_braiding E (pr11 dr) (internal_hom (pr11 dr) X1) · internal_eval (pr11 dr) X1))).
  unfold double_glued_rightwhiskering_comp2; simpl.
  refine (_ @ assoc' _ _ _).
  rewrite <- (bifunctor_leftcomp E).
  rewrite doublePullbackArrow_PrR.
  rewrite (bifunctor_leftcomp E).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  exact (! pr2 (counit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ ψ21).
  Unshelve.
  unfold arr1, arr2, postcompose, double_glued_tensor_product.
  rewrite (functor_comp L).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) eqphi).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite (internal_postcomp_comp (pr11 dr)).
  unfold functoronmorphisms1.
  rewrite (internal_postcomp_comp (pr11 dr)).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ l2) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite <- (internal_postcomp_comp (pr11 dr)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f)) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (mon_closed_adj_natural E _ _ _ (pr21 dr))).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (internal_postcomp_comp (pr11 dr) _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _)).
  repeat rewrite assoc'.
  apply maponpaths.
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ internal_postcomp_comp (pr11 dr) _ _).
  apply maponpaths.
  rewrite assoc.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (_ @ ! maponpaths (λ f, f · _) (fmonoidal_preservestensornatright L _ _ _ _)).
  rewrite assoc'.
  refine (! id_right _ @ _).
  apply maponpaths.
  rewrite <- (functor_comp L).
  rewrite <- (functor_id L).
  apply maponpaths.
  exact (! triangle_id_left_ad (pr2 (pr2 C R)) _).
  unfold arr2, arr3, postcompose, double_glued_tensor_product; simpl.
  rewrite (functor_comp L).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite <- eqphi.
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U2))) _ _ _)).
  simpl.
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp _ (_ · (f ⊗^{E}_{r} _ · _))) (hom_onmorphisms_is_postcomp _ _)).
  unfold functoronmorphisms1.
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (f · _)) (assoc _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · (f · _))) (bifunctor_rightcomp E U2 _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp _ (_ · (f ⊗^{E}_{r} U2 · _))) (doublePullbackSqrLCommutes tens_dpb)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ f) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f) (internal_postcomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _ ).
  refine (_ @ maponpaths (λ f, _ · f · _) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (doublePullbackObject tens_dpb)))) _ _ _)).
  do 2 refine (assoc' _ _ _ @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f)) (internal_postcomp_comp _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  unfold internal_lam.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (bifunctor_leftcomp E U2).
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ · (f  ⊗^{E}_{r} U2 · _)) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · ((_ · f) ⊗^{E}_{r} U2 · _))
            (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ maponpaths (λ f, _ · (f  ⊗^{E}_{r} U2 · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · ((f · _) ⊗^{E}_{r} U2 · _)) (mon_closed_adj_natural E _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f  ⊗^{E}_{r} U2 · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · ((_ · f) ⊗^{E}_{r} U2 · _)) (internal_postcomp_comp U2 _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E U2 _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U2))) _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (triangle_id_left_ad (pr2 (pr2 E U2)) _)).
  rewrite id_left.
  simpl.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (pr2 (monoidal_braiding_inverses E _ _))).
  rewrite id_right.
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  generalize (pr122 k R _ _ (unit_from_are_adjoints (pr2 (pr2 C R)) R2)); repeat rewrite id_left; repeat rewrite id_right; simpl; intros keq.
  refine (! maponpaths (compose _) keq @ _).
  rewrite assoc.
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  rewrite <- (bifunctor_leftid E).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  refine (_ @ functor_id K _).
  apply maponpaths.
  exact (triangle_id_left_ad (pr2 (pr2 C R)) _).
Qed.

Definition double_glued_internal_hom_unit {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R : C} (dr : double_glued_cat L K R) :
  functor_identity (double_glued_total_sym_monoidal_cat pb L K k)
    ⟹ rightwhiskering_functor (double_glued_total_sym_monoidal_cat pb L K k) (R,, dr) ∙ double_glued_total_internal_hom pb k dr.
Proof.
  exists (double_glued_internal_hom_unit_data pb k dr).
  exact (double_glued_internal_hom_unit_is_nat_trans pb k dr).
Defined.

Definition double_glued_internal_hom_counit_data_comp1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  double_glued_mor_comp1 L K (pr1 (pr2 C R) S ⊗_{ C} R) S
    (double_glued_tensor_product pb L K k (pr1 (pr2 C R) S) R (double_glued_disp_internal_hom_ob pb k dr ds) dr) ds.
Proof.
  apply (compose (doublePullbackPrL _ ⊗^{E}_{r} pr11 dr)).
  exact (internal_eval _ _).
Defined.

Lemma double_glued_internal_hom_counit_data_eq1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  double_glued_mor_eq1 L K _ _ _ _
    (counit_from_are_adjoints (pr2 (pr2 C R)) S) (double_glued_internal_hom_counit_data_comp1 pb k dr ds).
Proof.
  unfold double_glued_mor_eq1, double_glued_internal_hom_counit_data_comp1.
  rewrite assoc'.
  refine (! maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ (pr21 ds)) @ _).
  rewrite assoc.
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite <- (bifunctor_rightcomp E (pr11 dr)).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackSqrLCommutes (internal_hom_doublePullback pb k dr ds)) @ _).
  unfold postcompose.
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, f ⊗^{E}_{r} (pr11 dr) · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite assoc.
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _) @ _).
  simpl.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f ⊗^{E}_{r} _ · _) (mon_closed_adj_natural E _ _ (L R) _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  rewrite <- hom_onmorphisms_is_postcomp.  
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _) @ _).
  rewrite assoc.
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  exact (triangle_id_left_ad (pr2 (pr2 E (pr11 dr))) _).
Qed.

Lemma double_glued_internal_hom_counit_data_comp2_lemma1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  internal_lam
    (pr12 ds ⊗^{ E}_{l} doublePullbackPrR (internal_hom_doublePullback pb k dr ds)
                 · (sym_mon_braiding E (pr12 ds) (internal_hom (pr12 ds) (pr12 dr)) · internal_eval (pr12 ds) (pr12 dr)))
    · internal_postcomp (pr11 (internal_hom_doublePullback pb k dr ds)) (pr22 dr) =
    compose (C:=E) (pr22 ds) (# K (internal_eval R S))
      · (internal_lam (sym_mon_braiding E (K (pr1 (pr2 C R) S ⊗_{ C} R)) (L (pr1 (pr2 C R) S)) · pr1 k (pr1 (pr2 C R) S) R)
           · internal_precomp (doublePullbackPrM (internal_hom_doublePullback pb k dr ds)) (K R)).
Proof.
  unfold internal_lam.
  refine (maponpaths (λ f, _ · f · _) (hom_onmorphisms_is_postcomp _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, _ · internal_postcomp _ f) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E (pr12 ds)))) _ _ _) @ _).
  simpl.
  refine (maponpaths (λ f, _ · internal_postcomp _ (_ · (f ⊗^{E}_{r} pr12 ds · _))) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp _ (f · _)) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, _ · internal_postcomp _ (f · _)) (assoc' _ _ _) @ _).
  rewrite <- (bifunctor_rightcomp E).
  refine (! maponpaths (λ f, _ · internal_postcomp _ (_ · f ⊗^{E}_{r} _ · _)) (doublePullbackSqrRCommutes (internal_hom_doublePullback pb k dr ds)) @ _).
  unfold postcompose, internal_lam; simpl.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (L (pr1 (pr2 C R) S))))) _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (functor_comp (pr1 (pr2 E (L (pr1 (pr2 C R) S)))) _ _)).
  simpl.
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ ! maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  rewrite (monoidal_braiding_naturality_left E).
  rewrite (bifunctor_leftcomp E).
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc'.
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_postcomp_comp (pr12 ds) _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E (pr12 ds)))) _ _ _) @ _).
  simpl.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _ · _) (triangle_id_left_ad (pr2 (pr2 E (pr12 ds))) _) @  _).
  rewrite id_left.
  exact (! bifunctor_leftcomp E _ _ _ _ _ _).
Qed.

Lemma double_glued_internal_hom_counit_data_comp2_lemma2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  compose (C:=E) (pr22 ds) (# K (internal_eval R S)) · (compose (C:=E) (# K (sym_mon_braiding C R (pr1 (pr2 C R) S)))
     (internal_lam ((pr121 E) (K (R ⊗_{ C} pr1 (pr2 C R) S)) (L R) · pr1 k R (pr1 (pr2 C R) S)) · internal_precomp (pr21 dr) (K (pr1 (pr2 C R) S)))) =
    internal_lam (sym_mon_braiding E (pr12 ds) (pr11 dr))
      · internal_postcomp (pr11 dr)
      (pr21 dr ⊗^{ E} pr22 ds · (L R ⊗^{ E}_{l} # K (sym_mon_braiding C R (pr1 (pr2 C R) S) · internal_eval R S) · pr1 k R (pr1 (pr2 C R) S))).
Proof.
  unfold internal_lam, functoronmorphisms1.
  rewrite 2 hom_onmorphisms_is_postcomp.
  rewrite assoc.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ internal_postcomp_comp _ _ _).
  refine (! maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite <- (bifunctor_leftcomp E (L R)).
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  unfold functoronmorphisms1.
  do 2 apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  exact (! functor_comp K _ _).
Qed.

Definition double_glued_internal_hom_counit_data_comp2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  double_glued_mor_comp2 L K (pr1 (pr2 C R) S ⊗_{ C} R) S
    (double_glued_tensor_product pb L K k (pr1 (pr2 C R) S) R (double_glued_disp_internal_hom_ob pb k dr ds) dr) ds.
Proof.
  use doublePullbackArrow.
  simpl.
  apply internal_lam.
  unfold monoidal_cat_tensor_pt.
  apply (compose (_ ⊗^{E}_{l} doublePullbackPrR _)).
  apply (compose (sym_mon_braiding E _ _)).
  exact (internal_eval _ _).
  apply (compose (C:=E) (pr22 ds)).
  apply (# K).
  exact (internal_eval _ _).
  apply internal_lam.
  exact (sym_mon_braiding E _ _).
  exact (double_glued_internal_hom_counit_data_comp2_lemma1 pb k dr ds).
  exact (double_glued_internal_hom_counit_data_comp2_lemma2 pb k dr ds).
Defined.

Lemma double_glued_internal_hom_counit_data_eq2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) :
  double_glued_mor_eq2 L K _ _ _ _
    (counit_from_are_adjoints (pr2 (pr2 C R)) S) (double_glued_internal_hom_counit_data_comp2 pb k dr ds).
Proof.
  exact (! doublePullbackArrow_PrM (C:=E) _ _ _ _ _ _ _).
Qed.

Definition double_glued_internal_hom_counit_data {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R : C} (dr : double_glued_cat L K R) :
  nat_trans_data (double_glued_total_internal_hom pb k dr ∙ rightwhiskering_functor (double_glued_total_sym_monoidal_cat pb L K k) (R,, dr))
    (functor_identity (double_glued_total_sym_monoidal_cat pb L K k)).
Proof.
  intros (S, ds).
  exists (counit_from_are_adjoints (pr2 (pr2 C R)) S).
  split.
  exists (double_glued_internal_hom_counit_data_comp1 pb k dr ds).
  exact (double_glued_internal_hom_counit_data_eq1 pb k dr ds).
  exists (double_glued_internal_hom_counit_data_comp2 pb k dr ds).
  exact (double_glued_internal_hom_counit_data_eq2 pb k dr ds).
Defined.


Lemma double_glued_internal_hom_counit_is_nat_trans {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R : C} (dr : double_glued_cat L K R) :
  is_nat_trans (double_glued_total_internal_hom pb k dr ∙ rightwhiskering_functor (double_glued_total_sym_monoidal_cat pb L K k) (R,, dr))
    (functor_identity (double_glued_total_sym_monoidal_cat pb L K k)) (double_glued_internal_hom_counit_data pb k dr).
Proof.
  intros (R1, dr1) (R2, dr2) (f12, df12).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact (pr2 (counit_from_are_adjoints (pr2 (pr2 C R))) _ _ _).
  simpl.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct df12 as ((ϕ12, eqphi), (ψ21, eqpsi)).
  unfold double_glued_internal_hom_counit_data_comp1, double_glued_disp_internal_hom_data_comp1;
    revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  unfold double_glued_mor_comp1, double_glued_disp_internal_hom_ob in *.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E (pr11 dr) _ _ _ _ _) @ _).
  rewrite doublePullbackArrow_PrL.
  rewrite (bifunctor_rightcomp E).
  rewrite 2 assoc'.
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  exact (pr2 (counit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _).
  show_id_type.
  unfold double_glued_mor_comp2, double_glued_tensor_product in *.
  set (tens_dpb := tensor_doublePullback pb k (double_glued_disp_internal_hom_ob pb k dr dr1) dr).
  set (hom_dpb := internal_hom_doublePullback pb k dr dr1).
  set (arr1 := compose (C:=E) (pr12 df12) (internal_lam ((pr12 dr1) ⊗^{E}_{l} doublePullbackPrR hom_dpb · sym_mon_braiding E _ _ · internal_eval _ _))).
  set (arr2 := compose (C:=E) (pr12 df12) (pr22 dr1) · # K (internal_eval R R1)).
  set (arr3 := compose (C:=E) (pr12 df12) (internal_lam (sym_mon_braiding E (pr12 dr1) (pr11 dr)))).
  refine (pathscomp0 (b:= doublePullbackArrow tens_dpb _ arr1 arr2 arr3 _ _) _ _); [ | apply pathsinv0];
    apply (doublePullbackArrowUnique tens_dpb _).
  simpl.
  refine (assoc' _ _ _ @ _).
  unfold arr1, double_glued_rightwhiskering_comp2.
  rewrite doublePullbackArrow_PrL.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold internal_lam.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (doublePullbackObject hom_dpb)))) _ _ _)).
  repeat rewrite assoc'.
  refine (maponpaths (λ f, _ · (f · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (λ f, _ · f) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp _ _ _ @ _).
  refine (_ @ functor_comp _ _ _).
  refine (_ @ ! hom_onmorphisms_is_postcomp _ _).
  apply maponpaths.
  simpl.
  unfold double_glued_disp_internal_hom_data_comp1.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_leftcomp E (pr12 dr2) _ _ _ _ _) @ _).
  rewrite doublePullbackArrow_PrR.
  refine (maponpaths (λ f, f · _) (bifunctor_leftcomp E (pr12 dr2) _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  exact (mon_closed_adj_natural_co E _ _ _ _).
  refine (assoc' _ _ _ @ _).
  simpl.
  unfold arr2, double_glued_rightwhiskering_comp2, double_glued_internal_hom_counit_data_comp2.
  rewrite doublePullbackArrow_PrM.
  rewrite assoc.
  rewrite doublePullbackArrow_PrM.
  rewrite assoc'.
  refine (! maponpaths (compose (C:=E) _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) _ (# K f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 C R))) _ _ _) @ _).
  refine (maponpaths (compose (C:=E) _) (functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  exact (pr22 df12).
  simpl.
  unfold arr3, double_glued_rightwhiskering_comp2, double_glued_internal_hom_counit_data_comp2.
  refine (assoc' _ _ _ @ _).
  rewrite doublePullbackArrow_PrR.
  rewrite assoc.
  rewrite doublePullbackArrow_PrR.
  unfold internal_lam.
  rewrite assoc'.
  rewrite 2 hom_onmorphisms_is_postcomp.
  refine (! maponpaths (λ f, _ · f) (internal_postcomp_comp (pr11 dr) _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp _ f) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite internal_postcomp_comp.
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  exact (! pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _).
  simpl.
  unfold arr1, double_glued_rightwhiskering_comp2, double_glued_internal_hom_counit_data_comp2.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite doublePullbackArrow_PrL.
  rewrite assoc.
  reflexivity.
  simpl.
  unfold arr2, double_glued_rightwhiskering_comp2, double_glued_internal_hom_counit_data_comp2.
  refine (assoc' _ _ _ @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite doublePullbackArrow_PrM.
  reflexivity.
  simpl.
  unfold arr3, double_glued_rightwhiskering_comp2, double_glued_internal_hom_counit_data_comp2.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite doublePullbackArrow_PrR.
  reflexivity.
  Unshelve.
  unfold arr1, arr2.
  rewrite assoc'.
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  unfold internal_lam.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f · _)) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · (_ · f))) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · (f · _))) (mon_closed_adj_natural E _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · (_ · f))) (internal_postcomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  refine (maponpaths (λ f, f · _) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _) (hom_onmorphisms_is_postcomp _ _)).
  refine (! internal_postcomp_comp _ _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (! maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E (pr12 dr1)))) _ _ _) @ _).
  rewrite assoc.
  simpl.
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackSqrRCommutes hom_dpb) @ _).
  rewrite (bifunctor_rightcomp E).
  unfold postcompose.
  refine ( _ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite assoc'.
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (! internal_postcomp_comp _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E (pr12 dr1)))) _ _ _) @ _).
  simpl.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E (pr12 dr1))) _) @  _).
  rewrite id_left.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (! bifunctor_leftcomp E _ _ _ _ _ _).
  unfold arr2, arr3.
  repeat rewrite assoc'.
  apply maponpaths.
  simpl.
  unfold internal_lam, postcompose.
  rewrite 2 hom_onmorphisms_is_postcomp.
  do 2 rewrite assoc.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (internal_postcomp_comp _ _ _) @ _).
  do 2 rewrite assoc.
  refine (_ @ maponpaths (λ f, _ · internal_postcomp (pr11 dr) f) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  refine (! maponpaths (λ f, _ · f · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc'.
  apply maponpaths.
  unfold functoronmorphisms1.
  rewrite assoc'.
  rewrite <- (bifunctor_leftcomp E _ _ _ _ _).
  refine (_ @ ! bifunctor_equalwhiskers E _ _ _ _ _ _).
  unfold functoronmorphisms2.
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  exact (! functor_comp K _ _).
Qed.

Definition double_glued_internal_hom_counit {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R : C} (dr : double_glued_cat L K R) :
  double_glued_total_internal_hom pb k dr ∙ rightwhiskering_functor (double_glued_total_sym_monoidal_cat pb L K k) (R,, dr)
    ⟹ functor_identity (double_glued_total_sym_monoidal_cat pb L K k).
Proof.
  exists (double_glued_internal_hom_counit_data pb k dr).
  exact (double_glued_internal_hom_counit_is_nat_trans pb k dr).
Defined.

Lemma double_glued_internal_hom_form_adjunction {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R : C} (dr : double_glued_cat L K R) :
  form_adjunction (rightwhiskering_functor (double_glued_total_monoidal pb L K k) (R,, dr)) (double_glued_total_internal_hom pb k dr)
    (double_glued_internal_hom_unit pb k dr) (double_glued_internal_hom_counit pb k dr).
Proof.
  split.
  intros (S, ds).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact (triangle_id_left_ad (pr2 (pr2 C R)) _).
  simpl.
  unfold double_glued_hom_adjunction_unit_comp1, double_glued_internal_hom_counit_data_comp1; simpl.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  rewrite doublePullbackArrow_PrL.
  exact (triangle_id_left_ad (pr2 (pr2 E (pr11 dr))) _).
  set (tens_dpb := tensor_doublePullback pb k ds dr).
  refine (pathscomp0 (b:= doublePullbackArrow tens_dpb _ (doublePullbackPrL tens_dpb) (doublePullbackPrM tens_dpb) (doublePullbackPrR tens_dpb)
                            (doublePullbackSqrLCommutes tens_dpb) _) _ _);
    [ | apply pathsinv0]; apply (doublePullbackArrowUnique tens_dpb _).
  simpl.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  generalize (doublePullbackSqrRCommutes (internal_hom_doublePullback pb k dr (double_glued_tensor_product pb L K k S R ds dr)));
    unfold postcompose; simpl; intros sqr.
  unfold double_glued_hom_adjunction_unit_comp1; simpl.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · (f · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp _ f) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp _ (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp _ (_ ⊗^{E}_{l} f · _)) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  change (unit_from_are_adjoints (pr2 (pr2 E (pr11 ds))) (pr11 tens_dpb)
  · internal_postcomp (pr11 ds)
      (pr11 tens_dpb
       ⊗^{ E}_{l} internal_lam
                    (pr11 ds ⊗^{ E}_{l} doublePullbackPrL tens_dpb
                     · (sym_mon_braiding E (pr11 ds) (internal_hom (pr11 ds) (pr12 dr)) · internal_eval (pr11 ds) (pr12 dr)))
       · (sym_mon_braiding E (pr11 tens_dpb) (internal_hom (pr11 tens_dpb) (pr12 dr)) · internal_eval (pr11 tens_dpb) (pr12 dr))) =
            doublePullbackPrL tens_dpb).
  unfold internal_lam.
  refine (maponpaths (λ f, _ · internal_postcomp _ (_ ⊗^{ E}_{l} (_ · f) · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  destruct dr as ((U, l), (X, l')).
  destruct ds as ((V, m), (Y, m')).
  simpl.
  show_id_type.
  etrans.
  Unshelve.
  10 : {
    apply (compose (unit_from_are_adjoints (pr2 (pr2 E V)) _)).
    apply (internal_postcomp V).
    apply (compose (doublePullbackPrL _ ⊗^{E}_{r} _)).
    exact (internal_eval V X).
  }
  do 2 apply maponpaths.
  refine (maponpaths (λ f, _ ⊗^{ E}_{l} (_ · internal_postcomp _ f) · _) (assoc _ _ _) @ _).
  rewrite internal_postcomp_comp.
  refine (maponpaths (λ f, _ ⊗^{ E}_{l} f · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_leftcomp E).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  do 2 rewrite <- (monoidal_braiding_naturality_left E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (λ f, _ · f) (pr2 (counit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite assoc'.
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (! maponpaths (λ f, _ · (_ · (f ⊗^{E}_{r} _ · _))) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  simpl.
  repeat rewrite assoc.
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_right.
  exact (pr1 (monoidal_braiding_inverses E _ _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  rewrite functor_comp.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  exact (triangle_id_right_ad (pr2 (pr2 E _)) _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply (maponpaths (compose _)).
  refine (_ @ functor_id K _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  exact (triangle_id_left_ad (pr2 (pr2 C _)) _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ ).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! maponpaths (compose _) (internal_postcomp_comp (pr11 dr) _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp (pr11 dr) f) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp (pr11 dr) (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp (pr11 dr) f) (assoc' _ _ _) @ _).
  rewrite internal_postcomp_comp.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, _ · f · _) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply (maponpaths (compose _)).
  rewrite assoc.
  refine (maponpaths (λ f, _ · internal_postcomp (pr11 dr) (f · _)) (pr1 (monoidal_braiding_inverses E _ _)) @ _).
  rewrite id_left.
  rewrite <- hom_onmorphisms_is_postcomp.
  exact (triangle_id_right_ad (pr2 (pr2 E _)) _).
  exact (id_left _).
  exact (id_left _).
  exact (id_left _).
  intros (S, ds).
  apply (double_glued_total_mor_eq_transp k); split3.
  exact (triangle_id_right_ad (pr2 (pr2 C _)) _).
  set (hom_dpb := internal_hom_doublePullback pb k dr ds).
  refine (pathscomp0 (b:= doublePullbackArrow hom_dpb _ (doublePullbackPrL hom_dpb) (doublePullbackPrM hom_dpb) (doublePullbackPrR hom_dpb)
                            (doublePullbackSqrLCommutes hom_dpb) _) _ _);
    [ | apply pathsinv0]; apply (doublePullbackArrowUnique hom_dpb _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  simpl.
  unfold double_glued_internal_hom_counit_data_comp1.
  refine (! maponpaths (compose _) (hom_onmorphisms_is_postcomp _ _) @ _).
  rewrite functor_comp.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr11 dr)))) _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  exact (triangle_id_right_ad (pr2 (pr2 E _)) _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  simpl.
  rewrite assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  rewrite <- (functor_comp L).
  rewrite <- (functor_id L).
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  exact (triangle_id_right_ad (pr2 (pr2 C _)) _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  simpl.
  unfold double_glued_internal_hom_counit_data_comp2.
  refine (assoc' _ _ _ @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp _ f) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp _ (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp _ (_ ⊗^{E}_{l} f · _)) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold internal_lam.
  show_id_type.
  etrans.
  Unshelve.
  9: {
    apply (compose (unit_from_are_adjoints (pr2 (pr2 E (pr12 ds))) (pr11 hom_dpb))).
    apply (internal_postcomp _).
    apply (compose (doublePullbackPrR _ ⊗^{E}_{r} _)).
    exact (internal_eval _ _).
  }
  repeat rewrite assoc'.
  do 2 apply maponpaths.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc'.
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  simpl.
  repeat refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (! maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc.
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_right.
  exact (pr1 (monoidal_braiding_inverses E _ _)).
  rewrite <- hom_onmorphisms_is_postcomp.
  rewrite functor_comp.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  rewrite assoc'.
  refine (_ @ id_right _).
  apply (maponpaths (compose _)).
  exact (triangle_id_right_ad (pr2 (pr2 E _)) _).
  exact (id_left _).
  exact (id_left _).
  exact (id_left _).
  simpl.
  unfold double_glued_internal_hom_counit_data_comp2.
  refine (assoc (C:=E) _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, pr11 dr ⊗^{ E}_{l} f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc'.
  unfold internal_lam.
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E _))) _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (triangle_id_left_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_left.
  exact (pr1 (monoidal_braiding_inverses E _ _)).
  exact (doublePullbackSqrRCommutes tens_dpb).
  exact (doublePullbackSqrRCommutes hom_dpb).  
Qed.

Definition double_glued_internal_hom_isadjoint {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K)  {R : C} (dr : double_glued_cat L K R) :
  are_adjoints (rightwhiskering_functor (double_glued_total_sym_monoidal_cat pb L K k) (R,, dr)) (double_glued_total_internal_hom pb k dr).
Proof.
  use tpair.
  exists (double_glued_internal_hom_unit pb k dr).
  exact (double_glued_internal_hom_counit pb k dr).
  exact (double_glued_internal_hom_form_adjunction pb k dr).
Defined.

