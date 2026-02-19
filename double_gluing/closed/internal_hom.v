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


Definition internal_hom_doublePullback_statement {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) : UU.
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  use (doublePullback pb).
  exact (internal_hom U1 U2).
  exact (internal_hom U1 (L R2)).
  exact (L (internal_hom R1 R2)).
  exact (internal_hom X2 (K R1)).
  exact (internal_hom X2 X1).
  exact (internal_postcomp U1 l2).
  apply (postcompose (internal_precomp l1 _)).
  apply internal_lam.
  apply (compose (fmonoidal_preservestensordata L _ R1)).
  apply (# L).
  exact (internal_eval R1 R2).
  apply (postcompose (internal_precomp l2' _)).
  apply internal_lam.
  apply (postcompose (pr1 k (internal_hom R1 R2) _)).
  apply (λ f, _ ⊗^{E}_{l} # K f).
  exact (internal_eval R1 R2).
  exact (internal_postcomp X2 l1').
Defined.
                                                                                                                                
Definition internal_hom_doublePullback {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) :
  internal_hom_doublePullback_statement pb k dr1 dr2.
Proof.
  apply doublePullback_exists.
Defined.

Definition double_glued_disp_internal_hom_ob {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R S : C} (dr : double_glued_cat L K R) (ds : double_glued_cat L K S) : double_glued_cat L K (pr1 (pr2 C R) S).
Proof.
  use tpair.
  set (dpb := internal_hom_doublePullback pb k dr ds).
  exists (pr11 dpb).
  apply (compose (pr121 dpb)).
  exact (pr221 (pb _ _ _ _ _)).
  destruct dr as ((U, l), (X, l')).
  destruct ds as ((V, m), (Y, m')).
  exists (U ⊗_{E} Y).
  apply (compose (C:=E) (l ⊗^{E} m')).
  apply (postcompose (pr1 k R _)).
  apply (λ f, L R ⊗^{E}_{l} # K f).
  apply (compose (sym_mon_braiding C _ _)).
  exact (internal_eval R S).
Defined.


Local Lemma double_glued_disp_internal_hom_lemma1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R S1 S2: C} (dr : double_glued_cat L K R) {ds1 : double_glued_cat L K S1} {ds2 : double_glued_cat L K S2}
  {f : pr1 C ⟦ S1, S2 ⟧} (df : ds1 -->[ f] ds2):
  doublePullbackPrL (internal_hom_doublePullback pb k dr ds1) · internal_postcomp (pr11 dr) (pr11 df) · internal_postcomp (pr11 dr) (pr21 ds2) =
  doublePullbackPrM (internal_hom_doublePullback pb k dr ds1) · # L (internal_postcomp R f)
  · postcompose (internal_precomp (pr21 dr) (L S2)) (internal_lam ((fmonoidal_preservestensordata L) (internal_hom R S2) R · # L (internal_eval R S2))).
Proof.
  destruct dr as ((U, l), (X, l')).
  destruct ds1 as ((V1, m1), (Y1, m1')).
  destruct ds2 as ((V2, m2), (Y2, m2')).
  destruct df as ((ϕ, eqphi), (ψ, eqpsi)); simpl.
  refine (assoc' _ _ _ @ _ ).
  refine (! maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  rewrite eqphi.
  refine (maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  refine (assoc _ _ _ @ _ ).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes (internal_hom_doublePullback pb k _ _)) @ _).
  unfold postcompose.
  rewrite 3 assoc'.
  apply maponpaths.
  refine (! maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  unfold internal_lam.
  rewrite 2 hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr1 L R)))) _ _ (# L (internal_postcomp R f)))).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! internal_postcomp_comp (pr1 L R) _ _ @ _ @ internal_postcomp_comp (pr1 L R) _ _).
  apply maponpaths.
  rewrite assoc'.
  rewrite <- (functor_comp L).
  refine (! maponpaths (λ f, _ · # L f) (pr2 (counit_from_are_adjoints (pr2 (pr2 C R))) _ _ f) @ _).
  rewrite (functor_comp L).
  do 2 rewrite assoc.
  apply (maponpaths (postcompose _)).
  unfold rightwhiskering_functor; simpl.
  rewrite (hom_onmorphisms_is_postcomp (E:=C)).
  exact (! pr1 (pr222 L) _ _ R (internal_postcomp R f)).
Qed.

Lemma double_glued_disp_internal_hom_lemma2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R S1 S2: C} (dr : double_glued_cat L K R) {ds1 : double_glued_cat L K S1} {ds2 : double_glued_cat L K S2}
  {f : pr1 C ⟦ S1, S2 ⟧} (df : ds1 -->[ f] ds2) :
  doublePullbackPrM (internal_hom_doublePullback pb k dr ds1) · # L (internal_postcomp R f)
    · (internal_lam (L (internal_hom R S2) ⊗^{ E}_{l} # K (internal_eval R S2) · pr1 k (internal_hom R S2) R) · internal_precomp (pr22 ds2) (K R)) =
    doublePullbackPrR (internal_hom_doublePullback pb k dr ds1) · internal_precomp (pr12 df) (pr12 dr) · internal_postcomp (pr12 ds2) (pr22 dr).
Proof.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _ ) (doublePullbackSqrRCommutes _)).
  unfold postcompose.
  rewrite 2 assoc'.
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (internal_precomp_comp _ _ _)).
  destruct ds1 as ((V1, m1), (Y1, m1')).
  destruct ds2 as ((V2, m2), (Y2, m2')).
  destruct df as ((ϕ, eqphi), (ψ, eqpsi)).
  revert eqphi; unfold double_glued_mor_eq1; simpl; intros eqphi.
  revert eqpsi; unfold double_glued_mor_eq2; simpl; intros eqpsi.
  refine (_ @ maponpaths (λ f, _ · internal_precomp f _) eqpsi).
  refine (_ @ ! maponpaths (compose _) (internal_precomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  unfold internal_lam; simpl.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (K S2)))) _ _ (# L (internal_postcomp R f))) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  unfold rightwhiskering_functor; simpl.
  do 3 rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (mon_closed_adj_natural E (L (internal_hom R S1)) (K S2) (K S1) (# K f))).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp (K S2) _ _ @ _ @ internal_postcomp_comp (K S2) _ _).
  apply maponpaths.
  do 2 rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers (monoidal_tensor E) _ _ _ _ _ _) @ _).
  unfold functoronmorphisms2.
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f · _) (functor_comp K _ _)).
  refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} (# K f) · _) (pr2 (counit_from_are_adjoints (pr2 (pr2 C R))) _ _ f)).
  unfold rightwhiskering_functor; simpl.
  rewrite (functor_comp K).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  do 2 rewrite assoc'.
  apply maponpaths.  
  rewrite hom_onmorphisms_is_postcomp.
  generalize (pr122 k R _ _ (internal_postcomp R f)).
  do 2 rewrite id_right.
  exact pathsinv0.
Qed.

Definition double_glued_disp_internal_hom_data_comp1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R S1 S2: C} (dr : double_glued_cat L K R) {ds1 : double_glued_cat L K S1} {ds2 : double_glued_cat L K S2}
  {f : pr1 C ⟦ S1, S2 ⟧} (df : ds1 -->[ f] ds2) :
  double_glued_mor_comp1 L K (pr1 (pr2 C R) S1) (pr1 (pr2 C R) S2) (double_glued_disp_internal_hom_ob pb k dr ds1)
    (double_glued_disp_internal_hom_ob pb k dr ds2).
Proof.
  unfold double_glued_mor_comp1, double_glued_disp_internal_hom_ob.
  use doublePullbackArrow.
  apply (compose (doublePullbackPrL _)).
  exact (internal_postcomp _ (pr11 df)).
  apply (compose (doublePullbackPrM _)).
  exact (# L (internal_postcomp _ f)).
  apply (compose (doublePullbackPrR _)).
  exact (internal_precomp (pr12 df) _).
  exact (double_glued_disp_internal_hom_lemma1 pb k dr df).
  exact (double_glued_disp_internal_hom_lemma2 pb k dr df).
Defined.

Lemma double_glued_disp_internal_hom_data_eq1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R S1 S2: C} (dr : double_glued_cat L K R) {ds1 : double_glued_cat L K S1} {ds2 : double_glued_cat L K S2}
  {f : pr1 C ⟦ S1, S2 ⟧} (df : ds1 -->[ f] ds2) :
  double_glued_mor_eq1 L K (pr1 (pr2 C R) S1) (pr1 (pr2 C R) S2) (double_glued_disp_internal_hom_ob pb k dr ds1)
    (double_glued_disp_internal_hom_ob pb k dr ds2) (# (pr1 (pr2 C R)) f) (double_glued_disp_internal_hom_data_comp1 pb k dr df).
Proof.
  unfold double_glued_mor_eq1, double_glued_disp_internal_hom_data_comp1; simpl.
  rewrite hom_onmorphisms_is_postcomp.
  apply doublePullbackArrow_PrM.
Qed.

Lemma double_glued_disp_internal_hom_data_eq2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R S1 S2: C} (dr : double_glued_cat L K R) {ds1 : double_glued_cat L K S1} {ds2 : double_glued_cat L K S2}
  {f : pr1 C ⟦ S1, S2 ⟧} (df : ds1 -->[ f] ds2) :
double_glued_mor_eq2 L K (pr1 (pr2 C R) S1) (pr1 (pr2 C R) S2) (double_glued_disp_internal_hom_ob pb k dr ds1)
     (double_glued_disp_internal_hom_ob pb k dr ds2) (# (pr1 (pr2 C R)) f) (pr11 dr ⊗^{ E}_{l} pr12 df).
Proof.
  unfold double_glued_mor_eq2; simpl.
  unfold postcompose.
  destruct dr as ((U, l), (X, l')).
  destruct ds1 as ((V1, m1), (Y1, m1')).
  destruct ds2 as ((V2, m2), (Y2, m2')).
  destruct df as ((ϕ, eqphi), (ψ, eqpsi)).
  unfold double_glued_mor_comp1, double_glued_mor_comp2 in *.
  revert eqphi; unfold double_glued_mor_eq1; simpl; intros eqphi.
  revert eqpsi; unfold double_glued_mor_eq2; simpl; intros eqpsi.
  change ((l ⊗^{ E}_{r} Y2 · L R ⊗^{ E}_{l} m2'
     · (L R ⊗^{ E}_{l} # K (sym_mon_braiding C R (pr1 (pr2 C R) S2) · internal_eval R S2) · pr1 k R (pr1 (pr2 C R) S2))) · # K (# (pr1 (pr2 C R)) f) =
  compose (C:=E) (U ⊗^{ E}_{l} ψ) (l ⊗^{ E} m1' · (L R ⊗^{ E}_{l} # K (sym_mon_braiding C R (pr1 (pr2 C R) S1) · internal_eval R S1) · pr1 k R (pr1 (pr2 C R) S1)))).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers (monoidal_tensor E) _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, U ⊗^{ E}_{l} f · _) eqpsi).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers (monoidal_tensor E) _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  do 2 rewrite assoc'.
  apply maponpaths.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  show_id_type.
  rewrite assoc'.
  refine (! maponpaths (compose _) (pr12 k R _ _ (# (pr1 (pr2 C R)) f)) @ _).
  do 2 rewrite assoc.
  apply (maponpaths (postcompose _)).
  unfold contraction_left_functor_data; simpl.
  do 2 rewrite <- (bifunctor_leftcomp E (L R)).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).
  do 2 rewrite assoc'.
  apply maponpaths.
  exact (pr2 (counit_from_are_adjoints (pr2 (pr2 C R))) _ _ f).
Qed.

Definition double_glued_disp_internal_hom_data {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : C} (dr : double_glued_cat L K R) : disp_functor_data (pr1 (pr2 C R)) (double_glued_cat L K) (double_glued_cat L K).
Proof.
  use tpair.
  intros S ds.
  exact (double_glued_disp_internal_hom_ob pb k dr ds).
  intros R1 R2 dr1 dr2 f12 df12.
  use tpair.
  exists (double_glued_disp_internal_hom_data_comp1 pb k dr df12).
  exact (double_glued_disp_internal_hom_data_eq1 pb k dr df12).
  use tpair.
  exact ( _ ⊗^{E}_{l} (pr12 df12)).
  exact (double_glued_disp_internal_hom_data_eq2 pb k dr df12).
Defined.

Lemma double_glued_disp_internal_hom_axioms {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : C} (dr : double_glued_cat L K R) :
  disp_functor_axioms (double_glued_disp_internal_hom_data pb k dr).
Proof.
  split.
  intros S ds.
  apply double_glued_mor_eq.
  split;
    unfold transportb, transportf;
    induction (! functor_id (pr1 (pr2 C R)) S);
    simpl.
  unfold double_glued_disp_internal_hom_data_comp1; simpl.
  unfold postcompose.
  apply pathsinv0.
  apply doublePullbackArrowUnique;
    rewrite (id_left _).
  rewrite (internal_postcomp_id _).
  rewrite (id_right _).
  exact (idpath _).
  rewrite (internal_postcomp_id R).
  rewrite (functor_id L).
  rewrite (id_right _).
  exact (idpath _).
  refine (_ @ ! maponpaths (compose _) (internal_precomp_id (pr12 ds) (pr12 dr))).
  rewrite (id_right _).
  exact (idpath _).
  exact (bifunctor_leftid E _ _).
  intros S1 S2 S3 ds1 ds2 ds3 f12 f23 df12 df23.
  apply double_glued_mor_eq.
  split;
    unfold transportb, transportf;
    induction (! functor_comp (pr1 (pr2 C R)) f12 f23);
    simpl.
  unfold double_glued_disp_internal_hom_data_comp1; simpl.
  apply pathsinv0.
  apply doublePullbackArrowUnique;
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL (internal_hom_doublePullback pb k dr ds3) _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL (internal_hom_doublePullback pb k dr ds2) _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_postcomp_comp. (* subgoal done *)
  refine (maponpaths (compose _) (doublePullbackArrow_PrM (internal_hom_doublePullback pb k dr ds3) _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM (internal_hom_doublePullback pb k dr ds2) _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp L _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_postcomp_comp. (* subgoal done *)
  refine (maponpaths (compose _) (doublePullbackArrow_PrR (internal_hom_doublePullback pb k dr ds3) _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR (internal_hom_doublePullback pb k dr ds2) _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_precomp_comp. (* subgoal done *)
  exact (bifunctor_leftcomp E _ _ _ _ _ _).
Qed.

Definition double_glued_disp_internal_hom {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : C} (dr : double_glued_cat L K R) : disp_functor (pr1 (pr2 C R)) (double_glued_cat L K) (double_glued_cat L K).
Proof.
  exists (double_glued_disp_internal_hom_data pb k dr).
  exact (double_glued_disp_internal_hom_axioms pb k dr).
Defined.

Definition double_glued_total_internal_hom {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : C} (dr : double_glued_cat L K R) :
  double_glued_total_sym_monoidal_cat pb L K k ⟶ double_glued_total_sym_monoidal_cat pb L K k.
Proof.
  use total_functor.
  exact (pr1 (pr2 C R)).
  exact (double_glued_disp_internal_hom pb k dr).  
Defined.

