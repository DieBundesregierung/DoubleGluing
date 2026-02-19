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

Definition double_glued_braiding_data_eq1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) :
  sym_mon_braiding E (pr11 dr1) (pr11 dr2) · (pr21 dr2 ⊗^{ E} pr21 dr1 · (fmonoidal_preservestensordata L) R2 R1) =
    pr21 dr1 ⊗^{ E} pr21 dr2 · (fmonoidal_preservestensordata L) R1 R2 · # L (sym_mon_braiding C R1 R2).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  simpl.
  unfold functoronmorphisms1.
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  do 3 rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  assert (is_symmetric_monoidal_functor C E L) as issymL.
  admit.
  exact (issymL _ _).
Admitted.

Local Lemma double_glued_braiding_data_lemma1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 : ob C} {U1 U2 X1 X2 : ob E} (l1 : E⟦U1, L R1⟧) (l1' : E⟦X1, K R1⟧) (l2 : E⟦U2, L R2⟧) (l2' : E⟦X2, K R2⟧) :
  doublePullbackPrR (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U1,, l1),, X1,, l1')) · internal_postcomp U1 l2' =
  doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U1,, l1),, X1,, l1')) · # K (sym_mon_braiding C R1 R2)
  · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2)).
Proof.
(*  rewrite doublePullbackSqrMCommutes. *)
  rewrite assoc'.
  exact (! doublePullbackSqrRCommutes (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U1,, l1),, X1,, l1'))).
Qed.

Local Lemma double_glued_braiding_data_lemma2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 : ob C} {U1 U2 X1 X2 : ob E} (l1 : E⟦U1, L R1⟧) (l1' : E⟦X1, K R1⟧) (l2 : E⟦U2, L R2⟧) (l2' : E⟦X2, K R2⟧) :
  doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U1,, l1),, X1,, l1')) · # K (sym_mon_braiding C R1 R2)
    · (compose (C:=E) (# K (sym_mon_braiding C R2 R1)) (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1) · internal_precomp l2 (K R1))) =
    doublePullbackPrL (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U1,, l1),, X1,, l1')) · internal_postcomp U2 l1'.
Proof.
  refine (_ @ ! doublePullbackSqrLCommutes (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U1,, l1),, X1,, l1'))).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  do 2 refine (assoc _ _ _ @ _ ).
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (postcompose (C:=E) _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, postcompose (C:=E) _ (# K f)) (pr1 (monoidal_braiding_inverses C R2 R1)) @ _).
  rewrite (functor_id K).
  exact (id_left _).
Qed.

Definition double_glued_braiding_data_comp2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) :
   double_glued_mor_comp2 L K (R1 ⊗_{ C} R2) (R2 ⊗_{ C} R1) (disp_bifunctor_on_objects (double_glued_monoidal pb L K k) R1 R2 dr1 dr2)
        (disp_bifunctor_on_objects (double_glued_monoidal pb L K k) R2 R1 dr2 dr1).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  unfold double_glued_mor_comp2, disp_bifunctor_on_objects; simpl.
  use doublePullbackArrow.
  exact (doublePullbackPrR _).
  apply (compose (doublePullbackPrM _)).
  exact (# K (sym_mon_braiding C R1 R2)).
  exact (doublePullbackPrL _).
  exact (double_glued_braiding_data_lemma1 pb k l1 l1' l2 l2').
  exact (double_glued_braiding_data_lemma2 pb k l1 l1' l2 l2').
Defined.

Lemma double_glued_braiding_data_eq2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) :
   double_glued_mor_eq2 L K (R1 ⊗_{ C} R2) (R2 ⊗_{ C} R1) (disp_bifunctor_on_objects (double_glued_monoidal pb L K k) R1 R2 dr1 dr2)
     (disp_bifunctor_on_objects (double_glued_monoidal pb L K k) R2 R1 dr2 dr1) (sym_mon_braiding C R1 R2)
     (double_glued_braiding_data_comp2 pb k dr1 dr2).
Proof.
  unfold double_glued_mor_eq2; simpl.
  exact (! doublePullbackArrow_PrM _ _ _ _ _ _ _).  
Qed.

Definition double_glued_braiding_data {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) : disp_braiding_data (double_glued_monoidal pb L K k) (sym_mon_braiding C).
Proof.
  intros R1 R2 dr1 dr2.
  split.
  use tpair.
  exact (sym_mon_braiding E _ _).
  exact (double_glued_braiding_data_eq1 pb k dr1 dr2).
  exists (double_glued_braiding_data_comp2 pb k dr1 dr2).
  exact (double_glued_braiding_data_eq2 pb k dr1 dr2).
Defined.

Lemma double_glued_mor_eq_transpb {C E E': category} {L : functor C E} {K : functor C E'} {R1 R2 : ob C} {f g: C⟦R1, R2⟧} {dr1 : double_glued_cat L K R1}
  {dr2 : double_glued_cat L K R2} (eqfg : f = g) (df : dr1 -->[f] dr2) (dg : dr1 -->[g] dr2) :
  df = transportb (mor_disp dr1 dr2) eqfg dg <-> (pr11 df = pr11 dg) × (pr12 df = pr12 dg).
Proof.
  unfold transportb, transportf; induction (! eqfg); simpl.
  exact (double_glued_mor_eq df dg).
Qed.

Lemma double_glued_mor_eq_transp' {C E E': category} {L : functor C E} {K : functor C E'} {R1 R2 : ob C} {f g: C⟦R1, R2⟧} {dr1 : double_glued_cat L K R1}
  {dr2 : double_glued_cat L K R2} (eqfg : g = f) (df : dr1 -->[f] dr2) (dg : dr1 -->[g] dr2) :
  df = transportf (mor_disp dr1 dr2) eqfg dg <-> (pr11 df = pr11 dg) × (pr12 df = pr12 dg).
Proof.
  unfold transportf; induction (eqfg); simpl.
  exact (double_glued_mor_eq df dg).
Qed.

Local Lemma double_glued_braiding_laws_lemma1 {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  (dpb31 := tensor_doublePullback pb k dr3 dr1)
  (dpb231 := tensor_doublePullback pb k dr2 ((pr11 dr3 ⊗_{ E} pr11 dr1,, pr21 dr3 ⊗^{ E} pr21 dr1 · (fmonoidal_preservestensordata L) R3 R1),,
                                               pr11 dpb31,, doublePullbackPrM dpb31)):
  internal_lam
    (((doublePullbackPrR dpb231
       · internal_curry (pr11 dr3) (pr11 dr1) (pr12 dr2)) ⊗^{ E}_{r} pr11 dr3 · internal_eval (pr11 dr3) (internal_hom (pr11 dr1) (pr12 dr2)))
     ⊗^{ E}_{r} pr11 dr1 · internal_eval (pr11 dr1) (pr12 dr2)) · internal_postcomp (pr11 dr1) (pr22 dr2) =
  doublePullbackPrM dpb231 ⊗^{ E}_{r} pr11 dr3
  · (# K (αinv^{ C }_{ R3, R1, R2} · sym_mon_braiding C (R3 ⊗_{ C} R1) R2) ⊗^{ E} pr21 dr3
     · (sym_mon_braiding E (K (R3 ⊗_{ C} (R1 ⊗_{ C} R2))) (L R3) · pr1 k R3 (R1 ⊗_{ C} R2)))
  · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp (pr21 dr1) (K R2)).
Proof.
  refine (_ @ maponpaths (compose _) (! internal_lam_precomp _ _)).
  refine (internal_lam_postcomp _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _ @ _) @ _).
  now rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _ @ _) @ _).
  now rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! curry_nat3 _ _ _) @ _).
  refine (assoc _ _ _ @ _).
(*  It stop working here:

  refine (maponpaths (λ f, f · _) (! doublePullbackSqrRCommutes dpb231 @ _) @ _). 
  now rewrite <- doublePullbackSqrMCommutes.
  apply assoc'.
  apply (bifunctor_rightcomp E).
  apply assoc'.
  apply (bifunctor_rightcomp E).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite internal_lam_precomp.
  rewrite internal_lam_natural.
  rewrite internal_lam_curry.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (internal_lam_tensor_eval _) @ _).
  refine (internal_lam_tensor_eval _ @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (_ @ assoc _ _ _)).
    apply maponpaths.
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
      2 : {
        apply maponpaths.
        apply pathsinv0.
        apply (functor_comp K).
      }
      apply assoc.
    }.
    apply idpath.
  }
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_left E _ _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftid E _ _ @ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{ E}_{l} f) (! functor_id K _ @ _) @ _).
  refine (maponpaths (# K) (! pr1 (monoidal_associatorisolaw C _ _ _)) @ _).
  apply (functor_comp K).
  apply (bifunctor_leftcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ pr2 (pr222 k) R3 R1 R2) @ _).
  unfold postcompose.
  apply assoc.
  apply assoc.
  refine (assoc _ _ _ @ _).
  do 2 refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (_ @ assoc' _ _ _)).
      2 : {
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) _).
        2 : {
          refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
          refine (_ @ assoc _ _ _).
          refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
          apply assoc'.
        }
        apply assoc.
      }
      apply pathsinv0.
      apply (bifunctor_rightcomp E).
    }
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    refine (assoc' _ _ _).
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_associatornatleft E _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    refine (assoc' _ _ _).
  }
  refine (_ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleftright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (monoidal_associatornatleft E _ _ _ _ _) @ _).
  apply assoc.
  apply assoc'.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_pt.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator0 E _ _ _) @ _).
  refine (_ @ monoidal_braiding_naturality_right E _ _ _ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  repeat rewrite assoc.
  apply pathsinv0.
  apply sym_mon_tensor_rassociator.
Qed.
 *)
Admitted.

Local Lemma double_glued_braiding_laws_lemma2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  (dpb31 := tensor_doublePullback pb k dr3 dr1)
  (dpb231 := tensor_doublePullback pb k dr2 ((pr11 dr3 ⊗_{ E} pr11 dr1,, pr21 dr3 ⊗^{ E} pr21 dr1 · (fmonoidal_preservestensordata L) R3 R1),,
                                               pr11 dpb31,, doublePullbackPrM dpb31)):
  doublePullbackPrM dpb231 ⊗^{ E}_{r} pr11 dr3 · (# K (αinv^{ C }_{ R3, R1, R2} · sym_mon_braiding C (R3 ⊗_{ C} R1) R2) ⊗^{ E} pr21 dr3
     · (sym_mon_braiding E (K (R3 ⊗_{ C} (R1 ⊗_{ C} R2))) (L R3) · pr1 k R3 (R1 ⊗_{ C} R2)))
                                · (compose (C:=E) (# K (sym_mon_braiding C R2 R1))
                                     (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1) · internal_precomp (pr21 dr2) (K R1))) =
  internal_lam
    (((doublePullbackPrL dpb231 · internal_postcomp (pr11 dr2) (doublePullbackPrL dpb31))  ⊗^{ E}_{r} pr11 dr3) ⊗^{ E}_{r} pr11 dr2
     · (α^{ E }_{ internal_hom (pr11 dr2) (internal_hom (pr11 dr3) (pr12 dr1)), pr11 dr3, pr11 dr2}
        · (internal_hom (pr11 dr2) (internal_hom (pr11 dr3) (pr12 dr1)) ⊗^{ E}_{l} sym_mon_braiding E (pr11 dr3) (pr11 dr2)
           · (αinv^{ E }_{ internal_hom (pr11 dr2) (internal_hom (pr11 dr3) (pr12 dr1)), pr11 dr2, pr11 dr3}
              · (internal_eval (pr11 dr2) (internal_hom (pr11 dr3) (pr12 dr1)) ⊗^{ E}_{r} pr11 dr3 · internal_eval (pr11 dr3) (pr12 dr1))))))
    · internal_postcomp (pr11 dr2) (pr22 dr1).
Proof.
  refine (assoc _ _ _ @ _ @ ! internal_lam_postcomp _ _).
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _)).
  2 : {
    refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _)).
    2 : {
      refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _)).
      2 : {
        refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _)).
        2 : {
          refine (_ @ maponpaths (compose _) (! internal_eval_nat _ _ _ _)).
          rewrite hom_onmorphisms_is_postcomp.
          refine (_ @ assoc' _ _ _).
          refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
          2 : {
            refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (! internal_eval_nat _ _ _ _)).
            rewrite hom_onmorphisms_is_postcomp.
            apply pathsinv0.
            apply (bifunctor_rightcomp E (pr11 dr3)).
          }
          apply assoc.
        }
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) (monoidal_associatorinvnatright E _ _ _ _ _)).
        apply assoc.
      }
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
      refine (assoc _ _ _).
    }
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatornatright E _ _ _ _ _)).
    apply assoc.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (_ @ assoc _ _ _)).
      2 : {
          refine (_ @ maponpaths (compose _) (_ @ internal_postcomp_comp _ _ _)).
          2 : {
            refine (_ @ maponpaths (internal_postcomp _) (_ @ ! doublePullbackSqrLCommutes dpb31)).
            2 : {
              refine (maponpaths (compose _) (! internal_lam_precomp _ _)).
            }
            apply pathsinv0.
            apply internal_postcomp_comp.
          }
          refine (_ @ assoc' _ _ _).
          refine (_ @ maponpaths (λ f, f · _) (_ @ ! doublePullbackSqrLCommutes dpb231)).
          2 : {
            refine (maponpaths (compose _) (! internal_lam_precomp _ _)).            
          }
          refine (_ @ assoc _ _ _).
          refine (maponpaths (compose _) (_ @ ! internal_lam_postcomp _ _)).  
          refine (maponpaths internal_lam (_ @ ! internal_lam_natural _ _)).
          unfold monoidal_cat_tensor_mor.
          now rewrite (when_bifunctor_becomes_rightwhiskering E).
      }
      apply pathsinv0.
      apply (bifunctor_rightcomp E).
    }
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  refine (_ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! pr12 k R3 _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (! functor_comp K _ _)).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct dr3 as ((U3, l3), (X3, l3')).
  simpl.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatorinvnatright E _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
        2 : {
          refine (maponpaths (λ f, f ⊗^{E}_{r} _) (! internal_lam_tensor_eval _)).
          
        }
        refine (_ @ ! internal_lam_tensor_eval _).
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
        refine (_ @ assoc _ _ _).
        refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
          refine (_ @ assoc _ _ _).
          refine (_ @ maponpaths (compose _) (assoc _ _ _ @ _)).
          2 : {
            refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _ @ _)).
            refine (maponpaths (λ f, _ ⊗^{ E}_{l} f) (assoc' _ _ _)).
          }
          apply assoc'.
        }
        apply assoc'.
      }
      apply assoc'.
    }
    apply assoc'.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ id_left _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (pr2 (monoidal_associatorisolaw E _ _ _))).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ id_left _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightid E _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (pr1 (monoidal_braiding_inverses E _ _))).
        apply pathsinv0.
        apply (bifunctor_rightcomp E).
      }
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _ @ assoc' _ _ _)).
      2 : {
        refine (_ @ (pr2 (pr222 k) R2 R3 R1)).
        refine (_ @ maponpaths (compose _) (_ @ id_left _)).
        2 : {
          refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_leftid E _ _)).
          2 : {
            refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f) (_ @ functor_id K _)).
            2 : {
              refine (_ @ maponpaths (# K) (_ @ bifunctor_rightid C _ _)).
              2 : {
                refine (_ @ maponpaths (λ f, f ⊗^{C}_{r} _) (pr2 (monoidal_braiding_inverses C _ _))).
                apply pathsinv0.
                apply (bifunctor_rightcomp C).
              }
              apply pathsinv0.
              apply (functor_comp K).
            }
            apply pathsinv0.
            apply (bifunctor_leftcomp E).
          }
          refine (_ @ assoc _ _ _).
          generalize (pr122 k R1 _ _ (sym_mon_braiding C R2 R3)); simpl; rewrite 2 id_right; intros keq.
          refine (_ @ maponpaths (compose _) (! keq)).
          apply assoc'.
        }
        refine (_ @ assoc' _ _ _).
        refine (maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
        refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
        2 : {
          refine (_ @ maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
          apply assoc'.
        }
        refine (_ @ assoc _ _ _).
        refine (map_on_two_paths compose _ _).
        apply (bifunctor_leftcomp E).
        refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
        assert (is_symmetric_monoidal_functor C E L) as issymL.
        admit.
        rewrite <- issymL.
        apply pathsinv0.
        apply (bifunctor_rightcomp E).
      }
      apply assoc'.
    }
    apply assoc'.
  }
  refine (_ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (maponpaths (λ f, f ⊗^{ E}_{r} _) _ @ _).
  refine (maponpaths (λ f, f · _) _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc'.
  refine (bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightid E _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (! pr1 (monoidal_braiding_inverses E _ _)) @ _).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _ ) @ _).
  refine (assoc _ _ _ @ _).
  exact (! pr2 (pr222 k) R3 R2 R1).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _)).
  apply assoc.
  refine (assoc _ _ _ @ _).
  repeat rewrite assoc.
  apply cancel_postcomposition.
  apply cancel_postcomposition.
  apply cancel_postcomposition.
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
    2 : {
      refine (_ @ maponpaths (compose _) (! monoidal_braiding_naturality_right E _ _ _ _)).
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) _).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
        2 : {
          refine (_ @ maponpaths (compose _) (monoidal_associatorinvnatleft E _ _ _ _ _)).
          apply assoc'.
        }
        refine (_ @ assoc _ _ _).
        refine (_ @ maponpaths (compose _) (monoidal_associatorinvnatleftright E _ _ _ _ _)).
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
        2 : {
          refine (_ @ maponpaths (compose _) (_ @ bifunctor_leftcomp E _ _ _ _ _ _)).
          2 : {
            refine (maponpaths (λ f, _ ⊗^{E}_{l} f) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
          }
          refine (_ @ assoc _ _ _).
          refine (_ @ maponpaths (compose _) (_ @ bifunctor_leftcomp E _ _ _ _ _ _)).
          2 : {
            refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f) (_ @ tensor_sym_mon_braiding E _ _)).
            2 : {
              unfold monoidal_cat_tensor_mor; rewrite (bifunctor_equalwhiskers E).
              apply assoc.
            }
            refine (_ @ ! bifunctor_leftcomp E _ _ _ _ _ _).
            refine (_ @ maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
            apply assoc'.
          }
          refine (_ @ assoc' _ _ _).
          refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
          2 : {
            refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatornatleft E _ _ _ _ _)).
            refine (_ @ assoc _ _ _).
            refine (_ @ maponpaths (compose _) (! monoidal_associatornatleftright E _ _ _ _ _)).
            apply assoc'.
          }
          apply assoc.
        }
        apply assoc.
      }
      apply assoc.
    }
    apply assoc.
  }
  refine (_ @ assoc _ _ _).
  do 3 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  apply assoc.
  refine (assoc _ _ _ @ _).
  do 2 refine (_ @ assoc' _ _ _).
  apply map_on_two_paths.
  apply (pathscomp0 (b:= α^{ E }_{_, _, _} · _ ⊗^{ E}_{l} sym_mon_braiding E (L R3) (L R2) · sym_mon_braiding E _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (compose _) (! sym_mon_tensor_lassociator E _ _ _)).
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt; rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  do 2 rewrite assoc.
  apply sym_mon_tensor_rassociator.
  do 4 refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _)).
    apply assoc.
  }
  refine (sym_mon_tensor_lassociator E _ _ _ @ _).
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt;
    rewrite (when_bifunctor_becomes_rightwhiskering E), (when_bifunctor_becomes_leftwhiskering E).
  do 3 refine (assoc' _ _ _ @ _).
  do 2 apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply pathsinv0.
  apply sym_mon_hexagon_rassociator1.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (sym_mon_tensor_rassociator C _ _ _) @ _).
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt;
    rewrite (when_bifunctor_becomes_rightwhiskering C), (when_bifunctor_becomes_leftwhiskering C).
  refine (_ @ assoc' _ _ _ @ id_left _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (pr2 (monoidal_associatorisolaw C _ _ _)) @ _).
  exact (id_left _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp C _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{C}_{l} f) (pr1 (monoidal_braiding_inverses C _ _)) @ _).
  apply (bifunctor_leftid C).
  apply id_left.
  apply (monoidal_associatorisolaw C).
Admitted.


Local Lemma double_glued_braiding_laws_lemma3 {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  (dpb31 := tensor_doublePullback pb k dr3 dr1)
  (dpb312 := tensor_doublePullback pb k
               ((pr11 dr3 ⊗_{ E} pr11 dr1,, pr21 dr3 ⊗^{ E} pr21 dr1 · (fmonoidal_preservestensordata L) R3 R1),, pr11 dpb31,, doublePullbackPrM dpb31) dr2):
  (doublePullbackPrR dpb312
   · (internal_postcomp (pr11 dr2)
        (doublePullbackPrR dpb31)
      · internal_swap_arg (pr11 dr2) (pr12 dr3) (pr11 dr1))) ⊗^{ E}_{r} pr11 dr1 · internal_eval (pr11 dr1) (internal_hom (pr11 dr2) (pr12 dr3))
  · internal_postcomp (pr11 dr2) (pr22 dr3) =
  (doublePullbackPrM dpb312 · # K (αinv^{ C }_{ R1, R2, R3} · sym_mon_braiding C (R1 ⊗_{ C} R2) R3 · αinv^{ C }_{ R3, R1, R2}))
  ⊗^{ E} pr21 dr1 · (sym_mon_braiding E (K (R1 ⊗_{ C} (R2 ⊗_{ C} R3))) (L R1) · pr1 k R1 (R2 ⊗_{ C} R3))
  · (internal_lam (sym_mon_braiding E (K (R2 ⊗_{ C} R3)) (L R2) · pr1 k R2 R3) · internal_precomp (pr21 dr2) (K R3)).
Proof.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _ @ _) @ _).
  now rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! internal_postcomp_comp _ _ _ @ _) @ _).
  refine (maponpaths (internal_postcomp _) (! doublePullbackSqrRCommutes _ @ _) @ _).
  refine (maponpaths (compose _) _).
  rewrite internal_lam_precomp.
  rewrite internal_lam_natural.
  refine (maponpaths (λ f, internal_lam (f · _)) (when_bifunctor_becomes_rightwhiskering E _ _)).
  apply internal_postcomp_comp.
  apply assoc'.
  refine (assoc _ _ _ @ _).
(*  rewrite <- doublePullbackSqrMCommutes. *)
  refine (maponpaths (λ f, f · _) (! doublePullbackSqrRCommutes _ @ _) @ _).
  refine (maponpaths (compose _) _ @ _).
  rewrite internal_lam_precomp.
  rewrite internal_lam_natural.
  refine (maponpaths (λ f, internal_lam (f · _)) (when_bifunctor_becomes_rightwhiskering E _ _)).
  rewrite internal_lam_natural.
  refine (maponpaths (λ f, internal_lam (f · _)) (when_bifunctor_becomes_rightwhiskering E _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (internal_lam_postcomp _ _ @ _).
  refine (maponpaths internal_lam _).
  refine (internal_lam_natural _ _ @ _).
  refine (maponpaths (λ f, internal_lam (f · _)) (when_bifunctor_becomes_rightwhiskering E _ _)).
  refine (internal_lam_lam_swap _).
  refine (internal_lam_tensor_eval _ @ _).
  refine (_ @ maponpaths (compose _) (! internal_lam_precomp _ _)).
  refine (_ @ ! internal_lam_natural _ _).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, f · _) (! when_bifunctor_becomes_rightwhiskering E _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (compose _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _ @ assoc _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _).
  refine (assoc' _ _ _).
  refine (assoc' _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  2 : {
    apply maponpaths.
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
    refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (maponpaths (compose _) (assoc' _ _ _)).
  }
  refine (_ @ assoc _ _ _).
(*  rewrite <- doublePullbackSqrMCommutes. *)
  apply maponpaths.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct dr3 as ((U3, l3), (X3, l3')).
  simpl.
  refine (maponpaths (λ f, f · _) (_ @ assoc _ _ _) @ _).
  refine (maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (! pr12 k _ _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _).
  apply assoc.
  apply assoc.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (natural_contraction_composed k _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
      apply assoc.
    }
    apply assoc'.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (! natural_contraction_composed k _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ id_left _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_leftid E _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f) (_ @ functor_id K _)).
      2 : {
        refine (_ @ maponpaths (# K) (_ @ bifunctor_rightid C _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, f ⊗^{C}_{r} _) (pr2 (monoidal_braiding_inverses C _ _))).
          apply pathsinv0.
          apply (bifunctor_rightcomp C).
        }
        apply pathsinv0.
        apply (functor_comp K).
      }
      apply pathsinv0.
      apply (bifunctor_leftcomp E).
    }
    refine (_ @ assoc _ _ _).
    generalize (pr122 k R3 _ _ (sym_mon_braiding C R1 R2)); simpl; rewrite 2 id_right; intros keq.
    refine (_ @ maponpaths (compose _) (! keq)).
    apply assoc'.
  }
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _)).
  2 : {
    refine (maponpaths (compose _) (_ @ assoc' _ _ _)).
    refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (maponpaths (compose _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
    assert (is_symmetric_monoidal_functor C E L) as issymL.
    admit.
    rewrite <- issymL.
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  do 3 refine (_ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _ ).
  apply cancel_postcomposition.
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ ).
  refine (maponpaths (compose _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _ ).
  refine (maponpaths (compose _) (_ @ assoc _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _)).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ )).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (_ @ assoc _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _)).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  refine (assoc _ _ _ @ _).
  do 3 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  2 : {
    apply maponpaths.
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
    apply assoc'.
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _ @ _)).
  3 : {
    refine (maponpaths (compose _) (assoc _ _ _)).
  }
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _ @ _)).
      3 : {
        refine (maponpaths (compose _) (assoc _ _ _ @ assoc _ _ _)).
      }
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatorinvnatleft E _ _ _ _ _)).
        refine (_ @ assoc _ _ _).
        refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
          refine (_ @ assoc _ _ _).
          refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
          2 : {
            refine (_ @ maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
            refine (_ @ assoc' _ _ _).
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
  refine (_ @ assoc' _ _ _).
  apply map_on_two_paths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (_ @ assoc _ _ _) @ _).
  refine (maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  apply (bifunctor_leftcomp E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleft E _ _ _ _ _) @ _).
  apply assoc'.
  apply assoc'.
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ ! bifunctor_equalwhiskers E _ _ _ _ _ _)).
  2 : {
    unfold functoronmorphisms2.
    refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  }
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply (bifunctor_leftcomp E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleftright E _ _ _ _ _) @ _).
  apply assoc'.
  apply assoc'.
  apply assoc'.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply cancel_postcomposition.
  apply (pathscomp0 (b:= sym_mon_braiding E _ _ ⊗^{E}_{r} _ · α^{E}_{_,_,_} · _ ⊗^{E}_{l} sym_mon_braiding E _ _ · αinv^{E}_{_,_,_})).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! id_left _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightid E _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (! pr2 (monoidal_braiding_inverses E _ _)) @ _).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc' _ _ _ @ assoc' _ _ _) @ _).
  do 2 refine (assoc _ _ _ @ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E), <- (when_bifunctor_becomes_leftwhiskering E).
  refine (maponpaths (λ f, f · _) (! sym_mon_hexagon_lassociator E _ _ _) @ _).
  refine (_ @ id_right _).
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (pr1 (monoidal_associatorisolaw E _ _ _)) @ _).
  apply id_left.
  apply (monoidal_braiding_inverses E).
  repeat rewrite assoc'.
  apply maponpaths.
  repeat rewrite assoc.
  rewrite <- (when_bifunctor_becomes_rightwhiskering E), <- (when_bifunctor_becomes_leftwhiskering E).
  refine (_ @ maponpaths (compose _) (! sym_mon_tensor_lassociator' E _ _ _)).
  refine (! id_left _ @ _).
  repeat rewrite assoc.
  repeat apply cancel_postcomposition.
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
  apply pathsinv0.
  apply (monoidal_braiding_inverses E).
  refine (! id_right _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorisolaw E).
  apply maponpaths.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
    refine (_ @ maponpaths (λ f, f · _) (! pr1 (monoidal_associatorisolaw C _ _ _))).
    apply pathsinv0.
    apply id_left.
  }
  rewrite <- (when_bifunctor_becomes_rightwhiskering C), <- (when_bifunctor_becomes_leftwhiskering C).
  refine (_ @ maponpaths (λ f, f · _) (! sym_mon_tensor_lassociator' C _ _ _)).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (tensor_sym_mon_braiding C _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  refine (_ @ maponpaths (λ f, _ · f · _) (! sym_mon_tensor_rassociator C _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (! pr1 (monoidal_associatorisolaw C _ _ _))).
  rewrite id_right.
  refine (! id_left _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _ @ _)).
  3 : {
    refine (maponpaths (compose _) (assoc _ _ _)).
  }
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! pr2 (monoidal_associatorisolaw C _ _ _))).
    now rewrite id_left.
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  apply pathsinv0.
  apply (monoidal_associatorisolaw C).
  refine (! id_left _ @ _).
  apply cancel_postcomposition.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_leftwhiskering C).
  refine (! bifunctor_leftid C _ _ @ _ @ bifunctor_leftcomp C _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_inverses C).
Admitted.

Local Lemma double_glued_braiding_laws_lemma4 {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  (dpb31 := tensor_doublePullback pb k dr3 dr1)
  (dpb312 := tensor_doublePullback pb k
               ((pr11 dr3 ⊗_{ E} pr11 dr1,, pr21 dr3 ⊗^{ E} pr21 dr1 · (fmonoidal_preservestensordata L) R3 R1),, pr11 dpb31,, doublePullbackPrM dpb31) dr2):
  (doublePullbackPrM dpb312 · # K (αinv^{ C }_{ R1, R2, R3} · sym_mon_braiding C (R1 ⊗_{ C} R2) R3 · αinv^{ C }_{ R3, R1, R2}))
  ⊗^{ E} pr21 dr1 · (sym_mon_braiding E (K (R1 ⊗_{ C} (R2 ⊗_{ C} R3))) (L R1) · pr1 k R1 (R2 ⊗_{ C} R3))
  · (compose (C:=E) (# K (sym_mon_braiding C R3 R2)) ((internal_lam ((pr121 E) (K (R3 ⊗_{ C} R2)) (L R3) · pr1 k R3 R2) · internal_precomp (pr21 dr3) (K R2)))) =
  (doublePullbackPrL dpb312
   · (internal_precomp (sym_mon_braiding E (pr11 dr1) (pr11 dr3)) (pr12 dr2) · internal_curry (pr11 dr1) (pr11 dr3) (pr12 dr2))) ⊗^{ E}_{r} pr11 dr1
                                                                                                                                     · internal_eval (pr11 dr1) (internal_hom (pr11 dr3) (pr12 dr2)) · internal_postcomp (pr11 dr3) (pr22 dr2).
Proof.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ ! internal_eval_nat _ _ _ _)).
  2 : {
    now rewrite hom_onmorphisms_is_postcomp.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (_ @ assoc _ _ _ @ _)).
    3 : {
      refine (maponpaths (λ f, f · _) (assoc' _ _ _)).
    }
    2 : {
      refine (_ @ maponpaths (compose _) (curry_nat3 _ _ _)).
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
      2 : {
        rewrite <- internal_pre_post_comp_as_pre_post_comp.
        rewrite internal_pre_post_comp_as_post_pre_comp.
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) (_ @ ! doublePullbackSqrLCommutes dpb312)).
        2 : {
          exact (maponpaths (compose _) (! internal_lam_precomp _ _)).
        }
        refine (_ @ assoc _ _ _).
        exact (maponpaths (compose _) (! internal_lam_precomp _ _)).        
      }
      refine (_ @ assoc _ _ _).
      exact (maponpaths (compose _) (! internal_lam_curry _)).
    }
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! internal_lam_tensor_eval _).
  do 3 refine (assoc _ _ _ @ _).
  rewrite internal_lam_precomp.
  rewrite internal_lam_natural.
  apply maponpaths.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct dr3 as ((U3, l3), (X3, l3')).
  simpl.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _ @ _) @ _).
  unfold functoronmorphisms2.
  refine (maponpaths (compose _) _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! pr12 k _ _ _ _) @ _).
  apply assoc.
  apply assoc.
  apply (bifunctor_rightcomp E).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (natural_contraction_composed k R1 R3 R2) @ _).
  do 3 refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ id_left _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_leftid E _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f) (_ @ functor_id K _)).
      2 : {
        refine (_ @ maponpaths (# K) (_ @ bifunctor_rightid C _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, f ⊗^{C}_{r} _) (pr2 (monoidal_braiding_inverses C _ _))).
          apply pathsinv0.
          apply (bifunctor_rightcomp C).
        }
        apply pathsinv0.
        apply (functor_comp K).
      }
      apply pathsinv0.
      apply (bifunctor_leftcomp E).
    }
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (! natural_contraction_extranatural k _ _ _ _)).
    apply assoc'.
  }
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ bifunctor_leftcomp E _ _ _ _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, _ ⊗^{E}_{l} f) (_ @ assoc' _ _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (tensor_sym_mon_braiding E l1 l3)).
        refine (_ @ assoc _ _ _).
        assert (is_symmetric_monoidal_functor C E L) as issymL.
        admit.
        refine (_ @ maponpaths (compose _) (! issymL _ _)).
        unfold  monoidal_cat_tensor_mor.
        now rewrite (bifunctor_equalwhiskers E).
      }
      apply pathsinv0.
      apply (bifunctor_leftcomp E).
    }
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (_ @ maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatornatleft E _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (! monoidal_associatornatleftright E _ _ _ _ _)).
      apply assoc'.
    }
    do 2 refine (_ @ assoc _ _ _).
    reflexivity.
  }
  refine (_ @ assoc _ _ _).
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc'.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (maponpaths (compose _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
      refine (maponpaths (λ f, f ⊗^{E}_{r} _) (_ @ assoc _ _ _)).
      refine (_ @ maponpaths (compose _) (_ @ functor_comp L _ _)).
      2 : {
        refine (_ @ maponpaths (# L) (! pr1 (monoidal_braiding_inverses C _ _))).
        now rewrite (functor_id L).
      }
      now rewrite id_right.
    }
    refine (_ @ assoc' _ _ _).
    refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _)).
  }
  do 2 refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatornatright E _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _ ) @ _).
  apply (monoidal_braiding_naturality_right E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  apply (bifunctor_rightcomp E).
  apply assoc'.
  refine (assoc' _ _ _ @ _).
  apply map_on_two_paths.
  do 2 apply maponpaths.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (sym_mon_hexagon_rassociator C _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering C), (when_bifunctor_becomes_rightwhiskering C).
  refine (assoc _ _ _ @ _ @ id_left _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp C _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{C}_{l} f) (pr1 (monoidal_braiding_inverses C _ _)) @ _).
  apply (bifunctor_leftid C).
  apply id_left.
  apply (monoidal_associatorisolaw C).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E), <- (when_bifunctor_becomes_rightwhiskering E).
  apply pathsinv0.
  apply sym_mon_hexagon_rassociator.
  refine (maponpaths (compose _) (assoc' _ _ _ ) @ _).
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! sym_mon_braiding_tensor_associator E _ _ _) @ _).
  refine (_ @ id_right _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply (monoidal_associatorisolaw E).
Admitted.

Lemma double_glued_braiding_laws {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) : disp_braiding_laws (double_glued_monoidal pb L K k) (double_glued_braiding_data pb L K k) (double_glued_braiding_data pb L K k).
Proof.
  split3.
  split.
  intros R1 R2 R3 dr1 dr2 dr3.
  intros f23 df23.
  set (rightarr := disp_leftwhiskering_on_morphisms (double_glued_monoidal pb L K k) R1 R2 R3 f23 dr1 dr2 dr3 df23 ;; double_glued_braiding_data pb L K k R1 R3 dr1 dr3).
  generalize (λ larr, pr2 (double_glued_mor_eq_transp (! monoidal_braiding_naturality_left C R1 R2 R3 f23) rightarr larr)).
  rewrite pathsinv0inv0.
  intros transpeq.
  refine (! transpeq _ _); clear transpeq.
  unfold rightarr;
  unfold double_glued_braiding_data, double_glued_braiding_data_comp2, disp_rightwhiskering_on_morphisms, double_glued_disp_bifunctor_data , double_glued_rightwhiskering, disp_leftwhiskering_on_morphisms, double_glued_leftwhiskering; split; simpl.
  exact (! monoidal_braiding_naturality_left E _ _ _ _).
  clear rightarr.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct dr3 as ((U3, l3), (X3, l3')).
  destruct df23 as ((ϕ23, eqphi), (ψ32, eqpsi)).
  unfold double_glued_leftwhiskering_comp2, double_glued_rightwhiskering_comp2; simpl.
  set (dpb12 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')).
  set (dpb31 := tensor_doublePullback pb k ((U3,, l3),, X3,, l3') ((U1,, l1),, X1,, l1')).
  set (arr1 := doublePullbackPrR dpb31 · internal_postcomp _ ψ32).
  set (arr2 := compose (C:=E) (doublePullbackPrM dpb31) (# K (sym_mon_braiding C R1 R3)) · # K (R1 ⊗^{C}_{l} f23)).
  set (arr3 := doublePullbackPrL dpb31 · internal_precomp ϕ23 X1).
  refine (doublePullbackArrowUnique dpb12 _ arr1 arr2 arr3 _ _ _ _ _ _ @ ! doublePullbackArrowUnique dpb12 _ _ _ _ _ _ _ _ _ _).
  unfold arr1, arr2.
(*  rewrite doublePullbackSqrMCommutes. *)
  rewrite assoc'.
  refine (! maponpaths (compose _) (internal_postcomp_comp U1 _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp U1 f) eqpsi @ _).
  refine (maponpaths (compose _) (internal_postcomp_comp U1 _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (doublePullbackSqrRCommutes dpb31) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite assoc'.
  refine (! maponpaths (λ f, _ · f) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  do 2 rewrite assoc.
  apply (maponpaths (postcompose _)).
  unfold internal_lam.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (L R1)))) _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! functor_comp (pr1 (pr2 E (L R1))) _ _ @ _ @ functor_comp (pr1 (pr2 E (L R1))) _ _).
  apply maponpaths.
  rewrite assoc'.
  refine (! maponpaths (compose _) (pr12 k R1 _ _ _) @ _).
  do 2 rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (monoidal_braiding_naturality_right E _ _ _ _).
  unfold arr2, arr3.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (doublePullbackSqrLCommutes dpb31)).
  do 3 rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (! maponpaths (λ f, compose (C:=E) (# K f) _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, compose (C:=E) _ (f · _)) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, _ · (compose (C:=E) (# K f) _)) (pr1 (monoidal_braiding_inverses C R2 R1)) @ _).
  rewrite (functor_id K).
  refine (maponpaths (compose (C:=E) _) (id_left _) @ _).
  refine (_ @ assoc _ _ _).
  rewrite <- (internal_precomp_comp _ _ (K R1)).
  rewrite eqphi.
  rewrite internal_precomp_comp.
  do 2 rewrite assoc.
  apply (maponpaths (postcompose _)).
  unfold internal_lam.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (L R2)))) _ _ _) @ _).
  do 2 rewrite assoc'.
  simpl.
  do 3 rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ (# L f23))).
  rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp _ _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  do 2 rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _)).
  rewrite 2 assoc'.
  apply maponpaths.
  generalize (pr122 k R1 _ _ f23); simpl.
  unfold leftwhiskering_on_morphisms, rightwhiskering_on_morphisms; simpl.
  rewrite 2 id_right.
  exact (idfun _).
  unfold arr1.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL dpb12 _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  unfold arr2.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM dpb12 _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  exact (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  unfold arr3.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR dpb12 _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  exact (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  unfold arr1.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL dpb12 _ _ _ _ _ _) @ _).
  exact (doublePullbackArrow_PrR _ _ _ _ _ _ _ ).
  unfold arr2.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM dpb12 _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite 2 assoc'.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  exact (monoidal_braiding_naturality_left C _ _ _ _).
  unfold arr3.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR dpb12 _ _ _ _ _ _) @ _).
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  (* braiding naturality right : *)
  intros R1 R2 R3 dr1 dr2 dr3.
  intros f12 df12.
  set (rightarr := disp_rightwhiskering_on_morphisms (double_glued_monoidal pb L K k) R1 R2 R3 f12 dr1 dr2 dr3 df12 ;; double_glued_braiding_data pb L K k R2 R3 dr2 dr3).
  generalize (λ larr, pr2 (double_glued_mor_eq_transp (! monoidal_braiding_naturality_right C R1 R2 R3 f12) rightarr larr)).
  rewrite pathsinv0inv0.
  intros transpeq.
  refine (! transpeq _ _); clear transpeq.
  unfold rightarr;
  unfold double_glued_braiding_data, double_glued_braiding_data_comp2, disp_rightwhiskering_on_morphisms, double_glued_disp_bifunctor_data , double_glued_rightwhiskering, disp_leftwhiskering_on_morphisms, double_glued_leftwhiskering; split; simpl.
  exact (! monoidal_braiding_naturality_right E _ _ _ _).
  clear rightarr.
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  11 : {
    apply (compose (doublePullbackPrR _)).
    exact (internal_precomp (pr11 df12) _).
  }
  11 : {
    apply (compose (doublePullbackPrM _)).
    apply (# K).
    exact (f12 ⊗^{C}_{r} _ · sym_mon_braiding C _ _).
  }
  11 : {
    apply (compose (doublePullbackPrL _)).
    exact (internal_postcomp _ (pr12 df12)).
  }
(*  rewrite doublePullbackSqrMCommutes. *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ _) @ _).
  apply internal_pre_post_comp_as_post_pre_comp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! doublePullbackSqrRCommutes (tensor_doublePullback pb k dr3 dr2)) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite 3 internal_lam_precomp.
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt;
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
    refine (_ @ assoc _ _ _).
    generalize (pr122 k R3 _ _ f12); simpl; rewrite 2 id_right; intros keq.
    refine (_ @ maponpaths (compose _) (! keq)); clear keq.
    refine (_ @ assoc' _ _ _).
    refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_left E _ _ _ _)).
  }
  do 2 refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  exact (pr21 df12).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ internal_postcomp_comp _ _ _)).
  2 : {
    refine (_ @ maponpaths (internal_postcomp _) (pr22 df12)).
    apply pathsinv0.
    apply internal_postcomp_comp.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! doublePullbackSqrLCommutes (tensor_doublePullback pb k dr3 dr2))).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _ @ _) @ _).
  refine (maponpaths (# K) (_ @ id_left _)).
  refine (maponpaths (compose _) (! monoidal_braiding_naturality_right C _ _ _ _) @ _).
  rewrite assoc.
  apply cancel_postcomposition.
  apply (monoidal_braiding_inverses C).
  rewrite 2 internal_lam_precomp.
  rewrite internal_lam_postcomp.
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ assoc' _ _ _ @ _).
  apply maponpaths.
  apply (pr12 k). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _ @ maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  apply cancel_postcomposition.
  exact (doublePullbackArrow_PrM _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  exact (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  exact (doublePullbackArrow_PrR _ _ _ _ _ _ _). 
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right C). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  (* braiding iso law: *)
  intros R1 R2 dr1 dr2.
  split;
    apply double_glued_mor_eq_transpb; split.
  apply (monoidal_braiding_inverses E).
  refine (doublePullbackArrowUnique _ _ (doublePullbackPrL _) (doublePullbackPrM _) (doublePullbackPrR _) _ _ _ _ _ _ @
            ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _); try exact (id_left _).
  exact (doublePullbackSqrLCommutes _).
(*  rewrite doublePullbackSqrMCommutes. *)
  exact (doublePullbackSqrRCommutes _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  exact (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_id K _).
  apply maponpaths.
  apply (monoidal_braiding_inverses C). (*completes subgoal*)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  apply (monoidal_braiding_inverses E).
  refine (doublePullbackArrowUnique _ _ (doublePullbackPrL _) (doublePullbackPrM _) (doublePullbackPrR _) _ _ _ _ _ _ @
            ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _); try exact (id_left _).
  exact (doublePullbackSqrLCommutes _).
(*  rewrite doublePullbackSqrMCommutes. *)
  exact (doublePullbackSqrRCommutes _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  exact (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_id K _).
  apply maponpaths.
  apply (monoidal_braiding_inverses C). (*completes subgoal*)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  exact (doublePullbackArrow_PrL _ _ _ _ _ _ _).
  (* hexagon laws *)
  split;
    intros R1 R2 R3 dr1 dr2 dr3; apply pathsinv0; apply double_glued_mor_eq_transp'; split.
  simpl.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  apply pathsinv0.
  apply sym_mon_hexagon_lassociator.
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  11 : {
    apply internal_lam.
    refine (compose ( _ ⊗^{E}_{r} _) _).
    apply (compose (doublePullbackPrL _)).
    apply (internal_postcomp _ (doublePullbackPrR _)).
    apply (compose ( _ ⊗^{E}_{l} sym_mon_braiding E _ _)).
    apply (compose (αinv^{E}_{_,_,_})).
    apply (compose (internal_eval _ _ ⊗^{E}_{r} _)).
    exact (internal_eval _ _).
  }
  11 : {
    apply (compose (doublePullbackPrM _)).
    apply (# K).
    apply (compose (α^{C}_{_,_,_})).
    apply (compose (sym_mon_braiding C _ _)).
    apply ((α^{C}_{_,_,_})).
  }
  11 : {
    apply internal_lam.
    use doublePullbackArrow.
    apply internal_lam.
    refine (compose ((_ ⊗^{E}_{r} _ · _) ⊗^{E}_{r} _) _).
    apply (compose (doublePullbackPrR _ )).
    apply internal_curry.
    apply internal_eval.
    apply internal_eval. (* completes subgoal *)
    apply (compose (doublePullbackPrM _ ⊗^{E}_{r} _)).
    refine (compose (# K _ ⊗^{E} (pr21 dr3)) _).
    refine (αinv^{C}_{_,_,_} · sym_mon_braiding C _ _).
    apply (compose (sym_mon_braiding E _ _)).
    apply (pr1 k). (* completes subgoal *)
    apply internal_lam.
    (*
    refine (compose ((doublePullbackPrL _  ⊗^{E}_{r} _) ⊗^{E}_{r} _) _). *)
    refine (compose ((_ ⊗^{E}_{r} _) ⊗^{E}_{r} _) _).
    apply (compose (doublePullbackPrL _ )).
    apply (internal_postcomp _ (doublePullbackPrL _)).
    apply (compose (α^{E}_{_,_,_})).
    apply (compose (_ ⊗^{E}_{l} sym_mon_braiding E _ _ ) ).
    apply (compose (αinv^{E}_{_,_,_})).
    apply (compose (internal_eval _ _ ⊗^{E}_{r} _)).
    apply internal_eval. (* completes subgoal *)
    exact (double_glued_braiding_laws_lemma1 pb L K k dr1 dr2 dr3).
    exact (double_glued_braiding_laws_lemma2 pb L K k dr1 dr2 dr3).
  }
  refine (internal_lam_postcomp _ _ @ _).
  refine (_ @ maponpaths (compose _) (! internal_lam_precomp _ _)).
  refine (_ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  do 3 refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _ @ _) @ _).
  now rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (internal_eval_nat _ _ _ _ @ _) @ _).
  now rewrite hom_onmorphisms_is_postcomp.
  apply (bifunctor_rightcomp E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! internal_postcomp_comp _ _ _ @ _) @ _).
  refine (maponpaths (internal_postcomp _) (! doublePullbackSqrRCommutes _ @ _) @ _).
  refine (maponpaths (compose _) (_ @ internal_lam_natural _ _) @ _).
  exact (maponpaths (compose _) (internal_lam_precomp _ _)).
(* It stops working here:

  now rewrite <- doublePullbackSqrMCommutes.
  apply internal_postcomp_comp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _ @ _) @ _).
  refine (maponpaths (compose _) (internal_lam_precomp _ _)).
  (* apply internal_lam_natural. *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_postcomp _ _ @ _)).
  refine (maponpaths internal_lam (internal_lam_natural _ _) @ _).
  unfold monoidal_cat_tensor_mor;
    now rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (internal_lam_tensor_eval _)).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct dr3 as ((U3, l3), (X3, l3')).
  refine (maponpaths (compose _) (internal_lam_tensor_eval _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply maponpaths.
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (! pr12 k R2 _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (natural_contraction_composed k R2 R1 R3 @ _) @ _).
  refine (maponpaths (compose _) (! id_left _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftid E _ _ @ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f) (! functor_id K _ @ _) @ _).
  refine (maponpaths (# K) (! bifunctor_rightid C _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{C}_{r} _) (! pr2 (monoidal_braiding_inverses C _ _)) @ _).
  apply (bifunctor_rightcomp C).
  apply (functor_comp K).
  apply (bifunctor_leftcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (natural_contraction_extranatural k R3 _ _ (sym_mon_braiding C R2 R1)) @ _).
  apply assoc.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _)).
  refine (! maponpaths (compose _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  assert (is_symmetric_monoidal_functor C E L) as issymL.
  admit.
  rewrite <- issymL.
  apply (bifunctor_rightcomp E).
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  simpl.
  refine (assoc _ _ _ @ _).
  do 2 refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  do 5 refine (assoc _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
    refine (_ @ assoc' _ _ _).
    refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (! monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f) (! tensor_sym_mon_braiding _ _ _) @ _).
  apply (bifunctor_leftcomp E).
  apply assoc'.
  apply assoc'.
  apply assoc'.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (pr1 (monoidal_braiding_inverses E _ _)) @ _).
  apply (bifunctor_rightid E).
  apply id_right.
  apply assoc.
  refine (assoc _ _ _ @ _ ).
  refine (_ @ monoidal_braiding_naturality_right E _ _ _ _).
  apply map_on_two_paths.
  refine (_ @ ! sym_mon_tensor_lassociator E _ _ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E).
  apply cancel_postcomposition.
  refine (maponpaths (compose _) (sym_mon_tensor_rassociator E _ _ _) @ _).
  refine (_ @ id_left _).
  repeat rewrite assoc.
  repeat apply cancel_postcomposition.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering E).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  apply id_right.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _ @ bifunctor_leftid E _ _).
  apply maponpaths.
  apply (monoidal_braiding_inverses E).
  apply maponpaths.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  apply pathsinv0.
  rewrite <- (when_bifunctor_becomes_leftwhiskering C), <- (when_bifunctor_becomes_rightwhiskering C).
  apply (sym_mon_hexagon_lassociator C). (* completes subgoal *)
  refine (_ @ ! internal_lam_postcomp _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  refine (_ @ ! doublePullbackArrow_PrM _ _ _ _ _ _ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply cancel_postcomposition.
  apply maponpaths.
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  apply sym_mon_braiding_tensor_associator.
  refine (_ @ id_left _).
  rewrite 3 assoc.
  do 2 apply cancel_postcomposition.
  apply (monoidal_braiding_inverses C). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (_ @ assoc _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _)).
  refine (maponpaths (λ f, f · _) (! internal_postcomp_comp _ _ _ @ _)).
  refine (maponpaths (internal_postcomp _) (doublePullbackArrow_PrL _ _ _ _ _ _ _)).
  refine (_ @ maponpaths internal_lam _).
  2 : {
    refine (maponpaths (λ f, f · _) (when_bifunctor_becomes_rightwhiskering E _ _)).
  }
  refine (_ @ internal_lam_natural _ _).
  refine (assoc _ _ _ @ _).
  apply maponpaths.
  unfold internal_uncurry.
  refine (internal_lam_precomp _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply maponpaths.
  apply assoc'. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite assoc.
  rewrite <- (when_bifunctor_becomes_leftwhiskering C), <- (when_bifunctor_becomes_rightwhiskering C).
  apply pathsinv0.
  apply sym_mon_hexagon_lassociator. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  apply internal_lam_postcomp.
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  apply doublePullbackArrow_PrR.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  refine (_ @ maponpaths (λ f, internal_lam (f · _)) (when_bifunctor_becomes_rightwhiskering E _ _)).
  refine (_ @ internal_lam_natural _ _).
  refine (_ @ ! maponpaths (compose _) (triangle_id_right_ad (pr2 (pr2 E _)) _)).
  refine (_ @ ! id_right _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ id_left _).
  rewrite 3 assoc.
  do 2 apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightid E _ _).
  apply maponpaths.
  refine (! internal_precomp_comp _ _ _ @ _ @ internal_precomp_id _ _).
  apply (maponpaths (λ f, internal_precomp f _)).
  apply (monoidal_braiding_inverses E). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  simpl; unfold postcompose, monoidal_cat_tensor_pt.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (_ @ ! functor_comp K _ _)).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! pr12 k _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  apply assoc'.
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (maponpaths (λ f, _ · (f · _)) (sym_mon_tensor_lassociator0 C _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_leftwhiskering C).
  refine (maponpaths (compose _) (! bifunctor_leftcomp C _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{C}_{l} f) (pr1 (monoidal_braiding_inverses C _ _)) @ _).
  apply (bifunctor_leftid C).
  apply id_right.
  rewrite <- (when_bifunctor_becomes_leftwhiskering C).
  refine (_ @ maponpaths (compose _) (! sym_mon_tensor_rassociator C _ _ _)).
  refine (! id_left _ @ _).
  repeat rewrite assoc.
  repeat apply cancel_postcomposition.
  apply pathsinv0.
  apply (monoidal_associatorisolaw C). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  apply doublePullbackArrow_PrL.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (! internal_postcomp_comp _ _ _ @ _)).
  refine (maponpaths (internal_postcomp _) (doublePullbackArrow_PrR _ _ _ _ _ _ _)).
  refine (bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (maponpaths (compose _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, internal_lam (f · _)) (when_bifunctor_becomes_rightwhiskering E _ _)).
  refine (_ @ internal_lam_natural _ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (internal_lam_tensor_eval _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E _ _), (when_bifunctor_becomes_leftwhiskering E _ _).
  now rewrite 3 assoc'.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_postcomp _ _ @ _) @ _).
  refine (maponpaths internal_lam (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _)) (! when_bifunctor_becomes_rightwhiskering E _ _) @ _).
  refine (! internal_lam_natural _ _ @ _).
  refine (maponpaths (compose _) (triangle_id_right_ad (pr2 (pr2 E _)) _) @ _).
  apply id_right.
  refine (_ @ maponpaths (λ f, internal_lam (f · _)) (when_bifunctor_becomes_rightwhiskering E _ _)).
  refine (_ @ internal_lam_natural _ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (internal_lam_uncurry _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E _ _), (when_bifunctor_becomes_leftwhiskering E _ _).
  refine (_ @ id_left _).
  repeat rewrite assoc.
  repeat apply cancel_postcomposition.
  apply (monoidal_associatorisolaw E). (* completes subgoal *) 
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply assoc'. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _)).
  simpl. unfold postcompose, monoidal_cat_tensor_pt.
  refine (assoc _ _ _ @ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  unfold double_glued_assoc_data_comp2.
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_postcomp _ _ @ _) @ _).
  refine (maponpaths internal_lam (doublePullbackArrow_PrR _ _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  now rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  refine (! internal_lam_natural _ _ @ _).
  refine (maponpaths (compose _) (triangle_id_right_ad (pr2 (pr2 E _)) _) @ _).
  refine (id_right _).
  apply assoc'.
  refine (_ @ maponpaths internal_lam _).
  2 : {
    now rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  }
  refine (_ @ internal_lam_natural _ _).
  refine (_ @ ! maponpaths (compose _) (triangle_id_right_ad (pr2 (pr2 E _)) _)).
  rewrite id_right.
  apply cancel_postcomposition.
  do 2 apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! curry_swap _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ id_left _).
  apply cancel_postcomposition.
  refine (! internal_precomp_comp _ _ _ @ _ @ internal_precomp_id _ _).
  apply (maponpaths (λ f, internal_precomp f _)).
  apply (monoidal_braiding_inverses E). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, _ · f) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  do 3 apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  apply (sym_mon_braiding_tensor_associator C R1 R2 R3).
  refine (_ @ id_left _).
  repeat rewrite assoc.
  repeat apply cancel_postcomposition.
  apply (monoidal_braiding_inverses C). (*completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (doublePullbackArrow_PrL _ _ _ _ _ _ _ @ _).
  refine (assoc _ _ _).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths internal_lam _).
  2 : {
    now rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  }
  refine (_ @ internal_lam_natural _ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (internal_lam_precomp _ _ @ _) @ _).
  unfold monoidal_cat_tensor_mor.
  now rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (internal_lam_curry _).
  refine (internal_lam_tensor_eval _ @ _).
  repeat apply maponpaths.
  apply assoc'. (* completes subgoal *)
  simpl. (* necessary *)
  rewrite <- (when_bifunctor_becomes_rightwhiskering E), <- (when_bifunctor_becomes_leftwhiskering E).
  apply pathsinv0.
  apply sym_mon_hexagon_rassociator.
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply internal_lam.
    use doublePullbackArrow.
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (doublePullbackPrR _)).
    apply (compose (internal_postcomp _ (doublePullbackPrR _))).
    apply internal_swap_arg.
    apply internal_eval.
    refine (compose (_ ⊗^{E} (pr21 dr1)) _).
    apply (compose (doublePullbackPrM _)).
    use (# K).
    2 : {
      exact (αinv^{C}_{_,_,_} · sym_mon_braiding C _ _ · αinv^{C}_{_,_,_}).
    }
    apply (compose (sym_mon_braiding E _ _)).
    exact (pr1 k R1 _).
    simpl; unfold monoidal_cat_tensor_pt.
    refine (compose (_ ⊗^{E}_{r} _) _).
    apply (compose (doublePullbackPrL _)).
    apply (compose (internal_precomp (sym_mon_braiding E _ _) _)).
    apply internal_curry.
    apply internal_eval.
    exact (double_glued_braiding_laws_lemma3 pb L K k dr1 dr2 dr3).
    exact (double_glued_braiding_laws_lemma4 pb L K k dr1 dr2 dr3).
  }
  9 : {
    apply (compose (doublePullbackPrM _)).
    apply (# K).
    apply (αinv^{C}_{_,_,_} · sym_mon_braiding C _ _ · αinv^{C}_{_,_,_}).
  }
  9 : {
    apply internal_lam.
    refine (compose ( _ ⊗^{E}_{r} _) _).
    apply (compose (doublePullbackPrR _)).
    apply (internal_postcomp _ (doublePullbackPrL _)).
    apply (compose (αinv^{E}_{_,_,_})).
    refine (compose ( _ ⊗^{E}_{r} _) _).
    apply internal_eval.
    apply internal_eval.
  }
  refine (internal_lam_postcomp _ _ @ _).
  refine (_ @ maponpaths (compose _ ) (! internal_lam_precomp _ _)).
  refine (_ @ ! internal_lam_natural _ _).
  apply maponpaths.
  refine (doublePullbackArrow_PrM _ _ _ _ _ _ _ @ _).
  refine (assoc' _ _ _ @ _).
  unfold monoidal_cat_tensor_mor. (* necessary *)
  now rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ ! internal_lam_postcomp _ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _ ) (internal_lam_precomp _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite doublePullbackSqrMCommutes.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _)).
  2 : {
    refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _)).
    2 : {
      refine (_ @ maponpaths (compose _) (_ @ ! internal_eval_nat _ _ _ _)).
      2 : {
        now rewrite hom_onmorphisms_is_postcomp.
      }
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (_ @ ! internal_eval_nat _ _ _ _)).
        2 : {
          now rewrite hom_onmorphisms_is_postcomp.
        }
        apply pathsinv0.
        apply (bifunctor_rightcomp E).
      }
      apply assoc.
    }
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (monoidal_associatorinvnatright E _ _ _ _ _)).
    apply assoc.    
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _) (_ @ assoc _ _ _)).
    2 : {
      refine (_ @ maponpaths (compose _) (_ @ internal_postcomp_comp _ _ _)).
      2 : {
        refine (_ @ maponpaths (internal_postcomp _) (_ @ ! doublePullbackSqrLCommutes (tensor_doublePullback pb k dr3 dr1))).
        2 : {
          refine (maponpaths (compose _) (! internal_lam_precomp _ _)).
        }
        apply pathsinv0.
        apply (internal_postcomp_comp _ _ _).
      }
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (_ @ doublePullbackSqrRCommutes _)).
      2 : {
        refine (maponpaths (compose _) (_ @ ! internal_lam_natural _ _ @ _)).
        unfold monoidal_cat_tensor_mor; now rewrite (when_bifunctor_becomes_rightwhiskering E).
        refine (maponpaths (compose _) (! internal_lam_precomp _ _)).
      }
      refine (_ @ assoc _ _ _).
      refine (maponpaths (compose _) (_ @ ! internal_lam_postcomp _ _)).
      refine (_ @ maponpaths internal_lam (_ @ ! internal_lam_natural _ _)).
      2 : {
        unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
        refine (maponpaths internal_lam (_ @ assoc' _ _ _)).
        refine (_ @ maponpaths (λ f, f · _) (_ @ ! bifunctor_equalwhiskers E _ _ _ _ _ _)).
        2 : {
          unfold functoronmorphisms2, monoidal_cat_tensor_pt.
          refine (_ @ maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
          2 : {
            apply maponpaths.
            do 2 refine (_ @ assoc' _ _ _).
            reflexivity.
          }
          apply assoc'.
        }
        refine (_ @ assoc _ _ _).
        refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
          apply assoc.
        }
        apply assoc'.
      }
      reflexivity.
    }
    apply pathsinv0.
    apply (bifunctor_rightcomp E).
  }
  refine (_ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatorinvnatright E _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose (C:=E) _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
    2 : {
      refine (maponpaths (λ f, f ⊗^{E}_{r} _) (! internal_lam_tensor_eval _)).
    }
    apply pathsinv0.
    apply internal_lam_tensor_eval.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (! natural_contraction_composed k R2 R3 R1)).
  refine (_ @ assoc' _ _ _).
  do 2 refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (compose _) (_ @ assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_braiding_naturality_left E _ _ _ _)).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _ @ _) @ _).
  unfold functoronmorphisms2.
  refine (maponpaths (λ f, f · _) (_ @ bifunctor_leftcomp E _ _ _ _ _ _)).
  apply maponpaths.
  apply (bifunctor_equalwhiskers E).
  do 2 refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _)).
      refine (_ @ maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
      2 : {
        apply maponpaths.
        refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
        apply assoc.
      }
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
      2 : {
        refine (_ @ maponpaths (compose _) (monoidal_associatorinvnatleftright E _ _ _ _ _)).
        apply assoc'.
      }
      apply assoc.
    }
    apply assoc.
  }
  do 2 refine (_ @ assoc _ _ _).
  do 2 apply maponpaths.
  refine (_ @ maponpaths (compose _) (_ @ assoc _ _ _)).
  2 : {
    refine (_ @ maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _)).
    apply assoc.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
  2 : {
    refine (_ @ maponpaths (compose _) (! monoidal_braiding_naturality_right E _ _ _ _)).
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
    2 : {
      refine (_ @ maponpaths (compose _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
      2 : {
        refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
        apply maponpaths.
        refine (_ @ assoc _ _ _).
        refine (_ @ maponpaths (compose _) (! monoidal_braiding_naturality_right E _ _ _ _)).
        refine (_ @ assoc' _ _ _).
        refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
      }
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) (monoidal_associatorinvnatright E _ _ _ _ _)).
      apply assoc.
    }
    apply assoc.
  }
  refine (_ @ assoc _ _ _).
  apply map_on_two_paths.
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! sym_mon_braiding_tensor_associator C _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  apply (monoidal_associatorisolaw C).
  refine (_ @ id_right _).
  refine (_ @ maponpaths (compose _) (pr1 (monoidal_associatorisolaw E _ _ _))).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
    refine (_ @ assoc' _ _ _).
    refine (maponpaths (λ f, f · _) (! sym_mon_hexagon_rassociator0 E _ _ _)).
  }
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! sym_mon_tensor_lassociator1 E _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (! pr1 (monoidal_associatorisolaw E _ _ _))).
    now rewrite id_right.
  }
  refine (! id_left _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp E _ _ _ _ _ _)).
    2 : {
      refine (! bifunctor_rightid E _ _ @ _).
      apply maponpaths.
      apply pathsinv0.
      apply (monoidal_braiding_inverses E).      
    }
    now rewrite id_left.
  }
  apply pathsinv0.
  apply (monoidal_associatorisolaw E). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  apply internal_lam_postcomp.
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrR _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (! internal_postcomp_comp _ _ _ @ _)).
  refine (maponpaths (internal_postcomp _) (doublePullbackArrow_PrL _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  apply assoc'. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  apply (bifunctor_rightcomp E).
  apply assoc'.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  do 2 refine (assoc _ _ _ @ _).
  reflexivity.
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (compose _) (! pr12 k _ _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _ ) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _ ) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_rightwhiskering C), <- (when_bifunctor_becomes_leftwhiskering C).
  apply pathsinv0.
  apply sym_mon_hexagon_rassociator. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrL _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc' _ _ _)). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  rewrite <- (when_bifunctor_becomes_rightwhiskering C), <- (when_bifunctor_becomes_leftwhiskering C).
  apply pathsinv0.
  apply sym_mon_hexagon_rassociator. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _)).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths internal_lam _).
  2 : {
    now rewrite <- (when_bifunctor_becomes_rightwhiskering E).
  }
  refine (_ @ internal_lam_natural _ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  unfold postcompose.
  refine (maponpaths (compose _) (assoc' _ _ _ @ assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! internal_postcomp_comp _ _ _ @ _) @ _).
  refine (maponpaths (internal_postcomp _) (doublePullbackArrow_PrR _ _ _ _ _ _ _)).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_precomp _ _) @ _).
  refine (internal_lam_precomp _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; 
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _ @ _) @ _).
  refine (_ @ bifunctor_leftid E _ _).
  apply maponpaths.
  apply (monoidal_braiding_inverses E).
  rewrite id_left.
  apply assoc'.  (* completes subgoal *)
  simpl.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  apply internal_lam_natural.
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  apply doublePullbackArrowUnique.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_tensor_eval _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrL _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrR _ _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (uncurry_swap _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _)).
  apply (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (internal_lam_natural _ _ @ _).
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths internal_lam (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_associatornatright E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_tensor_eval _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (_ @ id_left _).
  apply map_on_two_paths.
  apply (monoidal_associatorisolaw E).
  reflexivity.
  refine (! internal_lam_natural _ _ @ _).
  refine (_ @ id_right _).
  apply maponpaths.
  apply (triangle_id_right_ad (pr2 (pr2 E _)) _). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrM _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (assoc _ _ _ @ _)).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  do 3 refine (assoc _ _ _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) _).
  refine (assoc' _ _ _ @ _).
  rewrite <- doublePullbackSqrMCommutes.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  now rewrite (assoc (C:=C)). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrR _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (doublePullbackArrow_PrL _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (internal_lam_postcomp _ _ @ _)).
  refine (maponpaths internal_lam (doublePullbackArrow_PrL _ _ _ _ _ _ _ @ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  apply pathsinv0.
  apply (when_bifunctor_becomes_rightwhiskering E).
  refine (! internal_lam_natural _ _ @ _).
  refine (maponpaths (compose _) (triangle_id_right_ad (pr2 (pr2 E _)) _) @ _).
  apply id_right.
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    refine (_ @ maponpaths (compose _) (! curry_swap _ _ _)).
    apply assoc'.
  }
  refine (assoc _ _ _). (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _)  (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose (C:=E) _) (! functor_comp K _ _) @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  apply doublePullbackSqrMCommutes. (* completes subgoal *)
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_postcomp _ _ @ _) @ _).
  refine (_ @ ! internal_lam_natural _ _).
  apply maponpaths.
  refine (doublePullbackArrow_PrR _ _ _ _ _ _ _ @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  apply pathsinv0.
  refine (when_bifunctor_becomes_rightwhiskering E _ _ @ _).
  apply (bifunctor_rightcomp E).
  refine (_ @ internal_lam_natural _ _ @ _).
  2 : {
    apply maponpaths.
    apply cancel_postcomposition.
    apply (when_bifunctor_becomes_rightwhiskering E).
  }
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (monoidal_associatorinvnatright E _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _) (internal_lam_tensor_eval _ @ _)).
  apply internal_lam_tensor_eval.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E), (when_bifunctor_becomes_leftwhiskering E).
  apply internal_lam_tensor_eval.
  refine (_ @ id_left _).
  repeat rewrite assoc.
  do 3 apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  now rewrite id_right.
  refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _ @ bifunctor_leftid E _ _).
  apply maponpaths.
  apply (monoidal_braiding_inverses E).
*)  
Admitted.

Definition double_glued_symmetric {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) : disp_symmetric (double_glued_monoidal pb L K k) C.
Proof.
  exists (double_glued_braiding_data pb L K k).
  exact (double_glued_braiding_laws pb L K k).
Defined.

Definition double_glued_total_symmetric {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) : symmetric (double_glued_total_monoidal_cat pb L K k) :=
  total_symmetric (double_glued_monoidal pb L K k) (double_glued_symmetric pb L K k).

Definition double_glued_total_sym_monoidal_cat {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) : sym_monoidal_cat.
Proof.
  exists (double_glued_total_monoidal_cat pb L K k).
  exact (double_glued_total_symmetric pb L K k).
Defined.

