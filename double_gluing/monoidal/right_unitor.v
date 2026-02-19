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

Local Lemma rightunitor_data_eq1 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R : C} {U X : E} (l : E ⟦ U, L R ⟧) (l' : E ^opp ⟦ K R, X ⟧):
  ru^{ E }_{ U} · l = l ⊗^{ E} pr212 L · (pr112 L) R I_{ pr211 C} · # L ru^{ pr211 C }_{ R}.
Proof.
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (pr222 (pr222 L) R)).
  exact (! pr11 (pr222 (pr211 E)) _ _ _).
Qed.

Local Lemma rightunitor_data_lemma1 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R : C} {U X : E} (l : E ⟦ U, L R ⟧) (l' : E ^opp ⟦ K R, X ⟧) :
  compose (C:=E) l' (compose (C:=E) (# K ru^{ C }_{ R}) (internal_lam (sym_mon_braiding E (K (R ⊗_{ C} I_{ C})) (L R) · pr1 k R I_{ C}) · internal_precomp l (K I_{ C})))
  · internal_postcomp U (identity (K I_{ C})) = compose (C:=E) l' (# K ru^{ C }_{ R})
  · (internal_lam (sym_mon_braiding E (K (R ⊗_{ C} I_{ pr211 C})) (L R) · pr1 k R I_{ pr211 C}) · internal_precomp l (K I_{ pr211 C})).
Proof.
  refine (maponpaths (compose _) (internal_postcomp_id U _) @ _).
  rewrite id_right.
  rewrite assoc'.
  exact (idpath _).
Qed.

Local Lemma rightunitor_data_lemma2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R : C} {U X : E} (l : E ⟦ U, L R ⟧) (l' : E ^opp ⟦ K R, X ⟧) :
  compose (C:=E) l' (# K ru^{ C }_{ R})
  · (compose (C:=E) (# K (sym_mon_braiding C I_{ pr211 C} R))
     (internal_lam ((pr121 E) (K (I_{ pr211 C} ⊗_{ C} R)) (L I_{ pr211 C}) · pr1 k I_{ pr211 C} R) · internal_precomp (pr212 L) (K R))) =
  internal_lam ru^{ E }_{ X} · internal_postcomp I_{ E} l'.
Proof.
  refine (_ @ maponpaths (compose _) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (functor_comp _ _ _ )).
  refine (_ @ maponpaths (λ f, compose _ (# _ f)) (monoidal_rightunitornat E X _ l')).
  refine (_ @ ! maponpaths (compose _) (functor_comp _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E I_{ E}))) _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (postcompose (C:=E) _) (functor_comp K _ _) @ _).
  set (eqlbr := maponpaths (# K) (sym_mon_braiding_runitor C R)).
  refine (maponpaths (postcompose (C:=E) _) eqlbr @ _); clear eqlbr.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (postcompose _) (assoc _ _ _) @ _).
  refine (_ @ maponpaths (λ f, _ · # (pr1 (pr2 E I_{ E})) f) (sym_mon_braiding_lunitor E (K R))).
  rewrite functor_comp.
  rewrite 3 (hom_onmorphisms_is_postcomp).
  refine (maponpaths (postcompose _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  rewrite assoc'.
  rewrite (internal_postcomp_comp I_{ E}).
  refine (maponpaths (compose _) (assoc _ _ _) @ _ @ assoc' _ _ _).
  refine (! maponpaths (λ f, _ · (f · _)) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  generalize (pr1 (pr222 k) R); simpl; intros eqk.
  refine (_ @ ! maponpaths (λ f, _ · (internal_postcomp _ f)) eqk); clear eqk.
  rewrite internal_postcomp_comp.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite (pr2 (pr222 (monoidal_tensor_is_bifunctor E))).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) · _) (internal_postcomp_comp _ _ _)).
  set (braideq := maponpaths (internal_postcomp (I_{E})) (pr21 (pr221 E) _ _ (I_{E}) (# K lu^{ C }_{ R}))).
  refine (_ @ ! maponpaths (λ f, _ · f · _) braideq); clear braideq.
  refine (_ @ ! maponpaths (λ f, _ · f · _) (internal_postcomp_comp _ _ _)).
  refine (_ @ maponpaths (postcompose _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, (_ · f) · _ ) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ maponpaths (postcompose _) (pr2 (pr112 (pr2 E (I_{E}))) _ _ (# K lu^{ C }_{ R}))).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite <- internal_postcomp_comp.
  set (braideq := maponpaths (internal_postcomp (I_{E})) (pr11 (pr221 E) (K (I_{C} ⊗_{C} R )) _ _ (pr212 L))).
  refine (_ @ ! maponpaths (compose _) braideq); clear braideq.
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_comp _ _ _ )).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  exact (! mon_closed_adj_natural E (K (I_{C} ⊗_{C} R)) _ _ (pr212 L)).
Qed.

Definition double_glued_rightunitor_data_comp2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R):
  double_glued_mor_comp2 L K (R ⊗_{ pr211 C} I_{ pr211 C}) R
    (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R I_{ pr211 C} dr (double_glued_monoidal_unit L K)) dr.
Proof.
  destruct dr as ((U, l), (X, l')).
  use (doublePullbackArrow _).
  apply (compose (C:=E) l').
  apply (compose (C:=E) (# K (ru_{C} R))).
  refine (compose (C:=E) (internal_lam _ ) (internal_precomp l _)).
  apply (compose (sym_mon_braiding E _ _)).
  exact (pr1 k _ _).
  exact (compose (C:=E) l' (# K (ru_{C} R))).
  exact (internal_lam (ru_{E} X)).
  exact (rightunitor_data_lemma1 pb k l l').
  exact (rightunitor_data_lemma2 pb k l l').
Defined.

Lemma double_glued_rightunitor_data_eq2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R : ob C} (dr : double_glued_cat L K R):
  double_glued_mor_eq2 L K (R ⊗_{ pr211 C} I_{ pr211 C}) R
    (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R I_{ pr211 C} dr (double_glued_monoidal_unit L K)) dr (ru^{C}_{R})
    (double_glued_rightunitor_data_comp2 pb k dr).
Proof.
  simpl. (* necessary *)
  exact (! doublePullbackArrow_PrM _ _ _ _ _ _ _).
Qed.

Definition double_glued_rightunitor_data {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) :
  disp_rightunitor_data (double_glued_tensor pb L K k) (double_glued_monoidal_unit L K).
Proof.
  intros R dr.
  split.
  destruct dr as ((U, l), (X, l')).
  exists (ru_{E} U).
  exact (rightunitor_data_eq1 pb k l l').
  exists (double_glued_rightunitor_data_comp2 pb k dr).
  exact (double_glued_rightunitor_data_eq2 pb k dr).
Defined.

Local Lemma rightunitorinv_data_eq1 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R : C} {U X : E} (l : E ⟦ U, L R ⟧) (l' : E ^opp ⟦ K R, X ⟧) :
  ruinv^{ E }_{ U} · (l ⊗^{ E} pr212 L · (pr112 L) R I_{ pr211 C}) = l · # L ruinv^{ pr211 C }_{ R}.
Proof.

  refine (! pr2 (pr121 (pr111 E)) _ _ _ @ _).
  refine (! maponpaths (compose _) (functor_id _ _) @ _).
  refine (! maponpaths (λ f, _ · (# L f)) (pr1 (monoidal_rightunitorisolaw C R)) @ _).
  refine (maponpaths (compose _) (functor_comp _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (_ @ pr1 (pr121 (pr111 E)) _ _ _).
  refine (_ @ maponpaths (postcompose _) (pr2 (monoidal_rightunitorisolaw E U))).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  exact (! pr21 (double_glued_rightunitor_data pb L K k R ((U,,l),,(X,,l')))).
Qed.

Definition double_glued_rightunitorinv_data_comp2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R : C} (dr : double_glued_cat L K R):
  double_glued_mor_comp2 L K R (R ⊗_{ pr211 C} I_{ pr211 C}) dr
    (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R I_{ pr211 C} dr (double_glued_monoidal_unit L K)).
Proof.
  apply (compose (doublePullbackPrR _)).
  apply (compose (ruinv^{E}_{_})).
  exact (internal_eval _ _).
Defined.

Lemma double_glued_rightunitorinv_data_eq2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R : C} (dr : double_glued_cat L K R) :
  double_glued_mor_eq2 L K R (R ⊗_{ pr211 C} I_{ pr211 C}) dr (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R I_{ pr211 C} dr (double_glued_monoidal_unit L K)) ruinv^{ pr211 C }_{ R} (double_glued_rightunitorinv_data_comp2 pb k dr).
Proof.
  change (compose (C:=E) (doublePullbackPrM (tensor_doublePullback pb k ((pr11 dr,, pr21 dr),, pr12 dr,, pr22 dr) ((I_{ E},, pr212 L),, K I_{ C},, identity (K I_{ C})))) (# K ruinv^{ pr211 C }_{ R}) = compose (C:=E) (double_glued_rightunitorinv_data_comp2 pb k dr) (pr22 dr)).
  destruct dr as ((U, l), (X, l')).
  unfold double_glued_rightunitorinv_data_comp2; simpl.
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  rewrite assoc.
  unfold internal_eval.
  refine (_ @ maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E I_{ E}))) _ _ l')).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite assoc.
  refine (_ @ ! maponpaths (λ f, _ · f · _) (monoidal_rightunitorinvnat E (internal_hom I_{ E} X) _ (internal_postcomp I_{E} l'))).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite assoc'.
  refine (_ @ maponpaths (λ f, f · _) (doublePullbackSqrRCommutes (tensor_doublePullback pb k ((U,, l),, X,, l') ((I_{ E},, pr212 L),, K I_{ C},, identity (K I_{ C}))))).
  rewrite assoc'.
  apply maponpaths.
  unfold internal_eval.
  refine (! maponpaths (# K) (sym_mon_braiding_linvunitor C R) @ _).
  rewrite (functor_comp K).
  do 2 rewrite assoc'.
  apply (maponpaths (compose (C:=E) _)).
  refine (leftunitorinv_data_eq21 k R @ _).
  rewrite assoc'.
  reflexivity.
Qed.

Definition double_glued_rightunitorinv_data {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) :
  disp_rightunitorinv_data (double_glued_tensor pb L K k) (double_glued_monoidal_unit L K).
Proof.
  intros R dr.
  split.
  destruct dr as ((U, l), (X, l')).
  exists (ruinv_{E} U).
  exact (rightunitorinv_data_eq1 pb k l l').
  (* component 2: *)
  exists (double_glued_rightunitorinv_data_comp2 pb k dr).
  exact (double_glued_rightunitorinv_data_eq2 pb k dr).
Defined.

