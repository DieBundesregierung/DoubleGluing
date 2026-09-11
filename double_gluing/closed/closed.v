(************************************

Content: bundled definition of the double glued category as a symmetric monoidal closed category

*************************************)


Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Local Open Scope cat.

Require Import preliminaries.
Require Import double_pullbacks.
Require Import natural_contraction.

Require Import double_gluing.monoidal.symmetry.
                            
Require Import double_gluing.closed.internal_hom.
Require Import double_gluing.closed.adjunction.

Definition double_glued_total_sym_mon_closed_cat {C E : sym_mon_closed_cat} (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) : sym_mon_closed_cat.
Proof.
  exists (double_glued_total_sym_monoidal_cat dpbs L K k).
  intros (R, dr).
  exists (double_glued_total_internal_hom dpbs k dr).
  exact (double_glued_internal_hom_isadjoint dpbs k dr).
Defined.

