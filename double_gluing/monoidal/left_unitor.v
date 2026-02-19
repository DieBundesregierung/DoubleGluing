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

Lemma double_glued_leftunitor_data_eq1 {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (R : C) (U X : E) (l : E ⟦ U, L R ⟧) (l' : E ^opp ⟦ K R, X ⟧) :
  lu^{ E }_{ U} · l = pr212 L ⊗^{ E} l · (pr112 L) I_{ pr211 C} R · # L lu^{ pr211 C }_{ R}.
Proof.
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (postcompose _) (pr2 (pr222 (monoidal_tensor_is_bifunctor E)) _ _ _ _ _ _)).
  unfold functoronmorphisms2, postcompose.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (pr122 (pr222 L) R)).
  exact (! pr1 (pr122 (pr211 E)) _ _ _).
Qed.

Local Lemma double_glued_leftunitor_data_lemma1 {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) (R : C) (U X : E) (l : E ⟦ U, L R ⟧) (l' : E ^opp ⟦ K R, X ⟧)
  (arr1 := pr112 (pr2 E (I_{E})) X · # (pr1 (pr2 E I_{ E})) (ru_{E} _)) (arr2 := compose (C:=E) l' (# K (lu_{C} R)))
  (arr3 := compose (C:=E) l' ((pr112 (pr2 E U) _) · (# (pr1 (pr2 E U)) ((K R ⊗^{E}_{l} l) · ((# K (ru_{C} R)) ⊗^{E}_{r} (L R)) · (pr121 E _ _) · pr1 k R (I_{C}))))) :
  arr1 · internal_postcomp I_{ E} l' =
    arr2 · (internal_lam ((pr121 E) (K (I_{ pr211 C} ⊗_{ C} R)) (L I_{ pr211 C}) · pr1 k I_{ pr211 C} R) · internal_precomp (pr212 L) (K R)).
Proof.
  refine (! maponpaths (compose _) (hom_onmorphisms_is_postcomp (I_{E}) l') @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (functor_comp _ _ _)  @ _).
  refine (! maponpaths (λ f, compose _ (# _ f)) (monoidal_rightunitornat E X _ l') @ _).
  refine (maponpaths (compose _) (functor_comp _ _ _)  @ _).
  refine (assoc _ _ _ @ _).
  set (unitnateq := ! pr2 (pr112 (pr2 E (I_{E}))) _ _ l').
  refine (maponpaths (postcompose _) unitnateq @ _); clear unitnateq.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  set (eqrbl := ! sym_mon_braiding_lunitor E (K R)).
  refine (maponpaths (λ f, _ · # _ f) eqrbl @ _); clear eqrbl.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (! hom_onmorphisms_is_postcomp (L I_{C}) ((pr121 E) (K (I_{ pr211 C} ⊗_{ C} R)) (L I_{ pr211 C}) · pr1 k I_{ pr211 C} R))).
  refine (_ @ maponpaths (compose _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose _) (assoc _ _ _)).
  generalize (mon_closed_adj_natural E (K (I_{C} ⊗_{C} R)) _ _ (pr212 L)); simpl; intros natadjeq.
  refine (_ @ maponpaths (λ f, _ · f · _) natadjeq); clear natadjeq.
  refine (_ @ maponpaths (postcompose _) (assoc' _ _ _)).
  refine (maponpaths (compose _) (functor_comp (pr1 (pr2 E I_{ E})) _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  set (uninateq := ! pr2 (unit_from_are_adjoints (pr2 (pr2 E I_{ E}))) _ _ (# K lu^{ C }_{ R})).
  refine (_ @ maponpaths (postcompose _) uninateq); clear uninateq.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  refine (! functor_comp _ _ _ @ _ @ maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  refine (_ @ maponpaths (compose _) (hom_onmorphisms_is_postcomp (I_{E}) _)).
  refine (_ @ functor_comp _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _) ) (pr11 (pr221 E) _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose _) (assoc' _ _ _)); unfold postcompose.
  refine (_ @ maponpaths (λ f, (f · _) · _) (pr21 (pr221 E) _ _ _ _)).
  repeat refine (_ @ assoc _ _ _).
  apply maponpaths.
  generalize (pr1 (pr222 k) R); simpl; intros eq1.
  refine (eq1 @ _); clear eq1.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  unfold functoronmorphisms1.
  exact (pr2 (pr222 (monoidal_tensor_is_bifunctor E)) _ _ _ _ _ _).
Qed.

Local Lemma double_glued_leftunitor_data_lemma2 {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) (R : C) (U X : E) (l : E ⟦ U, L R ⟧) (l' : E ^opp ⟦ K R, X ⟧) :
  (compose (C:=E) l' (# K lu^{ C }_{ R})) · (compose (C:=E) (# K (sym_mon_braiding C R I_{ pr211 C})) (internal_lam ((pr121 E) (K (R ⊗_{ C} I_{ pr211 C})) (L R) · pr1 k R I_{ pr211 C}) · internal_precomp l (K I_{ pr211 C}))) =
    compose (C:=E) l' (internal_lam (K R ⊗^{ E}_{l} l · (# K ru^{ C }_{ R} ⊗^{ E}_{r} L R · (sym_mon_braiding E (K (R ⊗_{ C} I_{ C})) (L R) · pr1 k R I_{ C})))) · internal_postcomp U (identity (K I_{ C})).
Proof.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id U _)).
  refine (_ @ ! pr2 (pr121 (pr111 E)) _ _ _).
  unfold internal_lam.
  do 2 rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _ @ ! maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  do 2 refine (assoc _ _ _ @ _ ).
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (postcompose (C:=E) _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (L R)))) _ _ _) @ _).
  unfold postcompose.
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_comp U _ _)).
  generalize (! mon_closed_adj_natural E (K R) _ _ l); simpl; intros natadjeq.
  refine (_ @ maponpaths (postcompose _) natadjeq); clear natadjeq.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _)).
  apply (maponpaths (postcompose _)).
  repeat apply maponpaths.
  exact (sym_mon_braiding_lunitor C R).
Qed.

Definition double_glued_leftunitor_data_comp2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R) : double_glued_mor_comp2 L K (I_{ pr211 C} ⊗_{ pr211 C} R) R
        (disp_bifunctor_on_objects (double_glued_tensor pb L K k) I_{ pr211 C} R (double_glued_monoidal_unit L K) dr) dr.
Proof.
  destruct dr as ((U, l), (X, l')); simpl.
  use (doublePullbackArrow _).
  exact (internal_lam ru^{E}_{X}).
  exact (compose (C:=E) l' (# K lu^{C}_{R})).
  apply (compose (C:=E) l').
  apply internal_lam.
  apply (compose (C:=E) (K R ⊗^{E}_{l} l)).
  apply (compose (C:=E) ((# K (ru_{C} R)) ⊗^{E}_{r} (L R))).
  apply (compose (sym_mon_braiding E _ _)).
  exact (pr1 k R _).
  exact (double_glued_leftunitor_data_lemma1 k R U X l l').
  exact (double_glued_leftunitor_data_lemma2 k R U X l l').
Defined.

Definition double_glued_leftunitor_data_eq2 {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R) :
  double_glued_mor_eq2 L K (I_{ pr211 C} ⊗_{ pr211 C} R) R (disp_bifunctor_on_objects (double_glued_tensor pb L K k) I_{ pr211 C} R (double_glued_monoidal_unit L K) dr) dr lu^{ pr211 C }_{ R} (double_glued_leftunitor_data_comp2 pb k dr).
Proof.
  unfold double_glued_mor_eq2; simpl.
  change (compose (C:=E) (pr22 dr) (# K lu^{ pr211 C }_{ R}) =
            compose (C:=E) (double_glued_leftunitor_data_comp2 pb k dr)
              (doublePullbackPrM (tensor_doublePullback pb k ((I_{ E},, pr212 L),, K I_{ C},, identity (K I_{ C})) dr))).
  unfold double_glued_leftunitor_data_comp2; simpl.
  refine (_ @ ! doublePullbackArrow_PrM _ _ _ _ _ _ _).
  exact (idpath _).
Qed.

Definition double_glued_leftunitor_data {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) :
  disp_leftunitor_data (double_glued_tensor pb L K k) (double_glued_monoidal_unit L K).
Proof.
  intros R dr.
  split.
  destruct dr as ((U, l), (X, l')).
  exists (lu_{E} U).
  exact (double_glued_leftunitor_data_eq1 R U X l l').
  exists (double_glued_leftunitor_data_comp2 pb k dr).
  exact (double_glued_leftunitor_data_eq2 pb k dr).
Defined.


Lemma leftunitorinv_data_eq1 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R : C} {U X : E} (l : E ⟦ U, L R ⟧) (l' : E ^opp ⟦ K R, X ⟧) :
  luinv^{ E }_{ U} · (pr212 L ⊗^{ E} l · (pr112 L) I_{ pr211 C} R) = l · # L luinv^{ pr211 C }_{ R}.
Proof.
  refine (! pr2 (pr121 (pr111 E)) _ _ _ @ _).
  refine (! maponpaths (compose _) (functor_id _ _) @ _).
  refine (! maponpaths (λ f, _ · (# L f)) (pr1 (monoidal_leftunitorisolaw C R)) @ _).
  refine (maponpaths (compose _) (functor_comp _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (_ @ pr1 (pr121 (pr111 E)) _ _ _).
  refine (_ @ maponpaths (postcompose _) (pr2 (monoidal_leftunitorisolaw E U))).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  exact (! pr21 (double_glued_leftunitor_data pb L K k R ((U,,l),,(X,,l')))).
Qed.

Lemma leftunitorinv_data_eq21 {E C : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K)
  (R : ob C) :
  # K luinv^{ pr211 C }_{ R} =
    internal_lam ((pr121 E) (K (I_{ pr211 C} ⊗_{ C} R)) (L I_{ pr211 C}) · pr1 k I_{ pr211 C} R) · internal_precomp (pr212 L) (K R)
      · (ruinv^{ E }_{ internal_hom I_{ E} (K R)} · internal_eval I_{ E} (K R)).
Proof.

  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, f · (ruinv^{ E }_{ internal_hom I_{ E} (K R)} · internal_eval I_{ E} (K R))) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) · _) (mon_closed_adj_natural E (K (I_{C} ⊗_{C} R)) _ _ (pr212 L))).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (internal_postcomp_comp _ _ _)).
  assert (_ ⊗^{E}_{l} # K luinv^{ C }_{ R} · lu^{ E }_{ K R} = pr212 L ⊗^{ E}_{r} _ · pr1 k I_{ C} R) as keq.
  refine (_ @ pr1 (pr121 (pr111 E)) _ _ _).
  rewrite (! bifunctor_leftid (monoidal_tensor E) _ _).
  refine (_ @ maponpaths (λ f, I_{E} ⊗^{E}_{l} f · _) (functor_id K _)).
  rewrite (! pr1 (monoidal_leftunitorisolaw C R)).
  rewrite (functor_comp K _ _).
  refine (_ @ ! maponpaths (postcompose _) (bifunctor_leftcomp (monoidal_tensor E) (I_{E}) _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (pr1 (pr222 k) R @ _).
  apply (maponpaths (postcompose _)).
  exact (bifunctor_equalwhiskers (monoidal_tensor E) _ _ _ _ _ _).
  assert (K (I_{ C} ⊗_{ C} R) ⊗^{ E}_{l} pr212 L · ((pr121 E) (K (I_{ pr211 C} ⊗_{ C} R)) (L I_{ pr211 C}) · pr1 k I_{ pr211 C} R) = (# K (luinv^{C}_{R}) ⊗^{E}_{r} I_{E}) · ru^{E}_{K R}) as eqm.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left (pr21 E) (K (I_{C} ⊗_{C} R)) _ _ (pr212 L)) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose _) keq @ _).
  refine (_ @ maponpaths (compose _) (sym_mon_braiding_lunitor E (K R))).
  do 2 rewrite assoc.
  apply (maponpaths (postcompose _)).
  exact (monoidal_braiding_naturality_right (pr21 E) _ _ _ (# K luinv^{ C }_{ R})).
  refine (_ @ ! maponpaths (λ f, _ · (internal_postcomp _ f) · _) eqm).
  clear eqm keq.
  rewrite internal_postcomp_comp.
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite assoc'.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E I_{ E}))) _ _ (# K luinv^{ C }_{ R}))).
  rewrite assoc'.
  refine (! id_right _ @ _).
  apply maponpaths.
  do 2 rewrite assoc.
  exact (rightunitors_eval_expand2 (K R)).
Qed.

Lemma leftunitorinv_data_eq2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K)
  {R : ob C} {U X : E} (l : E ⟦ U, L R ⟧) (l' : E ^opp ⟦ K R, X ⟧)
  (dpb := doublePullback_exists pb (internal_postcomp I_{ E} l')
           (internal_lam ((pr121 E) (K (I_{ pr211 C} ⊗_{ C} R)) (L I_{ pr211 C}) · pr1 k I_{ pr211 C} R) · internal_precomp (pr212 L) (K R))
           (compose (C:=E) (# K ((pr121 C) R I_{ pr211 C})) (internal_lam ((pr121 E) (K (R ⊗_{ C} I_{ pr211 C})) (L R) · pr1 k R I_{ pr211 C}))
            · internal_precomp l (K I_{ pr211 C})) (internal_postcomp U (identity (K I_{ C}))))
  (pb1 := pb (internal_hom I_{ E} (K R)) (internal_hom I_{ E} X) (K (I_{ pr211 C} ⊗_{ C} R)) (internal_postcomp I_{ E} l')
           (internal_lam ((pr121 E) (K (I_{ pr211 C} ⊗_{ C} R)) (L I_{ pr211 C}) · pr1 k I_{ pr211 C} R) · internal_precomp (pr212 L) (K R))):
   # K luinv^{ pr211 C }_{ R}
  · (pr121 (doublePullback_exists pb (internal_postcomp I_{ E} l')
              (internal_lam ((pr121 E) (K (I_{ pr211 C} ⊗_{ C} R)) (L I_{ pr211 C}) · pr1 k I_{ pr211 C} R) · internal_precomp (pr212 L) (K R))
              (compose (C:=E) (# K ((pr121 C) R I_{ pr211 C})) (internal_lam ((pr121 E) (K (R ⊗_{ C} I_{ pr211 C})) (L R) · pr1 k R I_{ pr211 C}))
               · internal_precomp l (K I_{ pr211 C})) (internal_postcomp U (identity (K I_{ C}))))
     · pr221 (pb (internal_hom I_{ E} (K R)) (internal_hom I_{ E} X) (K (I_{ pr211 C} ⊗_{ C} R)) (internal_postcomp I_{ E} l')
                (internal_lam ((pr121 E) (K (I_{ pr211 C} ⊗_{ C} R)) (L I_{ pr211 C}) · pr1 k I_{ pr211 C} R) · internal_precomp (pr212 L) (K R)))) =
  l' · (pr121 dpb · (pr121 pb1 · postcompose (internal_eval I_{ E} X) ruinv^{ E }_{ internal_hom I_{ E} X})).
Proof.
  refine (assoc' (C:=E) _ _ _ @ _ @ assoc (C:=E) _ _ _).
  apply maponpaths.
  unfold postcompose.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (! internal_eval_natural _ _ )).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  unfold monoidal_cat_tensor_mor, functoronmorphisms1.
  refine (_ @ ! maponpaths (λ f, _ · (_ · (_ · f) · _)) (bifunctor_leftid (monoidal_tensor E) _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f · _)) (pr2 (pr121 (pr111 E)) _ _ _)).  
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (monoidal_rightunitorinvnat E (internal_hom I_{ E} X) _ (internal_postcomp I_{E} l'))).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose _) (assoc' _ _ _)).
  unfold postcompose.
  refine (_ @ ! maponpaths (λ f, f · _ · _) (pr12 pb1)).
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  exact (leftunitorinv_data_eq21 k R).
Qed.

Definition double_glued_leftunitorinv_data_comp2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R):
  double_glued_mor_comp2 L K R (I_{ pr211 C} ⊗_{ pr211 C} R) dr (disp_bifunctor_on_objects (double_glued_tensor pb L K k) I_{ pr211 C} R (double_glued_monoidal_unit L K) dr).
Proof.
  change (E ⟦ pr11 (tensor_doublePullback pb k ((I_{ E},, pr212 L),, K I_{ C},, identity (K I_{ C})) dr), pr12 dr ⟧).
  apply (compose (doublePullbackPrL _)).
  apply (compose (ruinv^{E}_{_})).
  exact (internal_eval _ _).
Defined.

Lemma double_glued_leftunitorinv_data_eq2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R):
  double_glued_mor_eq2 L K R (I_{ pr211 C} ⊗_{ pr211 C} R) dr (disp_bifunctor_on_objects (double_glued_tensor pb L K k) I_{ pr211 C} R (double_glued_monoidal_unit L K) dr) (luinv^{C}_{R}) (double_glued_leftunitorinv_data_comp2 pb k dr).
Proof.
  change (doublePullbackPrM (tensor_doublePullback pb k ((I_{ E},, pr212 L),, K I_{ C},, identity (K I_{ C})) dr) · # K luinv^{ C }_{ R} =
            doublePullbackPrL (tensor_doublePullback pb k ((I_{ E},, pr212 L),, K I_{ C},, identity (K I_{ C})) dr)
              · (ruinv^{ E }_{ internal_hom I_{ E} (pr12 dr)} · internal_eval I_{ E} (pr12 dr)) · pr22 dr).
  show_id_type.
  unfold internal_eval.
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E I_{ E}))) _ _ (pr22 dr))).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite assoc.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (monoidal_rightunitorinvnat _ _ _ (internal_postcomp I_{ E} (pr22 dr)))).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite assoc'.
  refine (_ @ ! maponpaths (λ f, f · _) (doublePullbackSqrLCommutes (tensor_doublePullback pb k ((I_{ E},, pr212 L),, K I_{ C},, identity (K I_{ C})) dr))).
  rewrite assoc'.
  apply maponpaths.
  exact (leftunitorinv_data_eq21 k R).
Qed.


Definition double_glued_leftunitorinv_data {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) :
  disp_leftunitorinv_data (double_glued_tensor pb L K k) (double_glued_monoidal_unit L K).
Proof.
  intros R dr.
  split.
  destruct dr as ((U, l), (X, l')).
  exists (luinv_{E} U).
  exact (leftunitorinv_data_eq1 pb k l l').
  (* component 2: *)
  exists (double_glued_leftunitorinv_data_comp2 pb k dr).
  exact (double_glued_leftunitorinv_data_eq2 pb k dr).
Defined.

