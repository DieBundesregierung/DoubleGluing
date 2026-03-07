(*******************************

In this file we define the bang functor of the double glued category of two linear categories.

 ******************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.Semantics.LinearLogic.LinearCategory.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.

Local Open Scope cat.


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


(* bang functor *)

Lemma double_glued_total_bang_functor_data_eq1 {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 : ob C} {dr1 : double_glued_ob L K R1} {dr2 : double_glued_ob L K R2} {f : C⟦R1, R2⟧}
  (df : double_glued_mor L K R1 R2 dr1 dr2 f):
  # (pr111 (linear_category_bang E)) (pr11 df) · (# (pr111 (linear_category_bang E)) (pr21 dr2) · (pr121 L) R2) =
  # (pr111 (linear_category_bang E)) (pr21 dr1) · (pr121 L) R1 · # L (# (pr111 (linear_category_bang C)) f).
Proof.
  simpl.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (pr221 L R1 R2 _)).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  simpl.
  refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
  apply maponpaths.  
  exact (pr21 df).
  
Qed.

Definition double_glued_total_bang_functor_data {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : functor_data (double_glued_total_sym_mon_closed_cat pb k) (double_glued_total_sym_mon_closed_cat pb k).
Proof.
  use tpair.
  intros (R, ((U, l), (X, l'))).
  exists (linear_category_bang C R).
  split.
  exists (linear_category_bang E U).
  apply (compose (# (linear_category_bang E) l)).
  exact (pr121 L R).
  exact (_ ,, identity _).
  intros (R1, dr1) (R2, dr2).
  intros (f, df).
  exists (# (linear_category_bang C) f).
  use tpair.
  exists (# (linear_category_bang E) (pr11 df)).
  exact (double_glued_total_bang_functor_data_eq1 pb L k df).
  use tpair.
  2: {
    simpl.
    refine (_ @ ! id_left (C:=E^opp) _).
    exact ( id_right (C:=E^opp) _).
    }
Defined.

Lemma double_glued_total_bang_is_functor {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : is_functor (double_glued_total_bang_functor_data pb L k).
Proof.
  split.
  intros (R, dr).
  apply (double_glued_total_mor_eq_transp k).
  split3; try apply (functor_id _).
  simpl.
  rewrite functor_id.
  exact (functor_id K _).
  intros (R1, dr1) (R2, dr2) (R3, dr3).
  intros (f12, df12) (f23, df23).
  apply (double_glued_total_mor_eq_transp k); split3; try apply (functor_comp _).
  simpl.
  rewrite functor_comp.
  exact (functor_comp K _ _).
Qed.

Definition double_glued_total_bang_functor {C E : linear_category} (pb : Pullbacks E) (L : linear_distributive_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : functor (double_glued_total_sym_mon_closed_cat pb k) (double_glued_total_sym_mon_closed_cat pb k).
Proof.
  exists (double_glued_total_bang_functor_data pb L k).
  exact (double_glued_total_bang_is_functor pb L k).
Defined.
