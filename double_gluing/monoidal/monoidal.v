(***********************************

This file contains the final monoidal structure of the double glued category.

*************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

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

Definition double_glued_monoidal {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) : disp_monoidal (double_glued_cat L K) C.
Proof.
  exists (double_glued_monoidal_data pb L K k).
  exact (double_glued_monoidal_laws pb L K k).
Defined.

Definition double_glued_total_monoidal {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) : monoidal (double_glued_total_cat L K) := total_monoidal (double_glued_monoidal pb L K k).

Definition double_glued_total_monoidal_cat {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) : monoidal_cat := _ ,, double_glued_total_monoidal pb L K k.
