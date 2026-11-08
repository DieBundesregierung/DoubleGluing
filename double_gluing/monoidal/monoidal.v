(***********************************

This file contains the final bundled monoidal structure of both the displayed double glued category as well as the total double glued category. 

*************************************)
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Local Open Scope cat.

Require Import preliminaries.
Require Import double_pullbacks.
Require Import natural_contraction.

Require Import double_gluing.double_gluing.

Require Import double_gluing.monoidal.monoidal_data.
Require Import double_gluing.monoidal.monoidal_laws.

Definition double_glued_monoidal {C : sym_monoidal_cat} {E : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  (L : sym_monoidal_functor C E) {K : functor C (E^opp)} (k : natural_contraction E L K) :
  disp_monoidal (double_glued_cat L K) C.
Proof.
  exists (double_glued_monoidal_data dpbs k).
  exact (double_glued_monoidal_laws dpbs k).
Defined.

Definition double_glued_total_monoidal {C : sym_monoidal_cat} {E : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  (L : sym_monoidal_functor C E) {K : functor C (E^opp)}
  (k : natural_contraction E L K) : monoidal (double_glued_total_cat L K) :=
  total_monoidal (double_glued_monoidal dpbs L k).

Definition double_glued_total_monoidal_cat {C : sym_monoidal_cat} {E : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  (L : sym_monoidal_functor C E) {K : functor C (E^opp)} (k : natural_contraction E L K) : monoidal_cat :=
  _ ,, double_glued_total_monoidal dpbs L k.

Definition forgetful_functor_fmonoidal_data {C : sym_monoidal_cat} {E : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  (L : sym_monoidal_functor C E) {K : functor C (E^opp)} (k : natural_contraction E L K) :
  fmonoidal_data (double_glued_total_monoidal dpbs L k) C (double_glued_forgetful_functor L K).
Proof.
  split.
  intros (R, dr) (S, ds).
  apply identity.
  apply identity.
Defined.

Lemma forgetful_functor_fmonoidal_laxlaws {C : sym_monoidal_cat} {E : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  (L : sym_monoidal_functor C E) {K : functor C (E^opp)} (k : natural_contraction E L K) :
  fmonoidal_laxlaws (forgetful_functor_fmonoidal_data dpbs L k).
Proof.
  split5.
  intros (R1, dr1) (R2, dr2) (S, ds) (f, df).
  apply (id_right _ @ ! id_left _).
  intros (R1, dr1) (R2, dr2) (S, ds) (f, df).
  apply (id_right _ @ ! id_left _).
  intros (R1, dr1) (R2, dr2) (R3, dr3).
  rewrite 2 id_right.
  refine (_ @ id_left _  @ ! id_right _ @ _).
  apply cancel_postcomposition.
  apply (bifunctor_rightid C).
  apply maponpaths.
  apply pathsinv0, (bifunctor_leftid C).
  intros (R, dr).
  rewrite id_right.
  refine (_ @ id_left _).
  apply cancel_postcomposition.
  apply (bifunctor_rightid C).
  intros (R, dr).
  rewrite id_right.
  refine (_ @ id_left _).
  apply cancel_postcomposition.
  apply (bifunctor_leftid C).  
Qed.

Definition forgetful_functor_fmonoidal_lax {C : sym_monoidal_cat} {E : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  (L : sym_monoidal_functor C E) {K : functor C (E^opp)} (k : natural_contraction E L K) :
  fmonoidal_lax (double_glued_total_monoidal dpbs L k) C (double_glued_forgetful_functor L K).
Proof.
  exists (forgetful_functor_fmonoidal_data dpbs L k).
  apply forgetful_functor_fmonoidal_laxlaws.
Defined.

Lemma forgetful_functor_fmonoidal_stronglaws {C : sym_monoidal_cat} {E : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  (L : sym_monoidal_functor C E) {K : functor C (E^opp)} (k : natural_contraction E L K) :
  fmonoidal_stronglaws (fmonoidal_preservestensordata (forgetful_functor_fmonoidal_lax dpbs L k))
    (fmonoidal_preservesunit (forgetful_functor_fmonoidal_lax dpbs L k)).
Proof.
  split.
  intros (R1, dr1) (R2, dr2).
  apply is_z_isomorphism_identity.
  apply is_z_isomorphism_identity.
Defined.

Definition forgetful_functor_fmonoidal {C : sym_monoidal_cat} {E : sym_mon_closed_cat} (dpbs : doublePullbacks E)
  (L : sym_monoidal_functor C E) {K : functor C (E^opp)} (k : natural_contraction E L K) :
  fmonoidal (double_glued_total_monoidal dpbs L k) C (double_glued_forgetful_functor L K).
Proof.
  exists (forgetful_functor_fmonoidal_lax dpbs L k).
  apply forgetful_functor_fmonoidal_stronglaws.
Defined.



