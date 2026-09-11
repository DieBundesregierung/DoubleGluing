(****************************************

Content: monoidal data of the double glued category bundled into one structure.

*************************************)
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
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


Definition double_glued_monoidal_data {E C : sym_mon_closed_cat} (dpbs : doublePullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) : disp_monoidal_data (double_glued_cat L K) C .
Proof.
  exists (double_glued_tensor dpbs k).
  exists (double_glued_monoidal_unit L K).
  split6.
  exact (double_glued_leftunitor_data dpbs k).
  exact (double_glued_leftunitorinv_data dpbs k).
  exact (double_glued_rightunitor_data dpbs k).
  exact (double_glued_rightunitorinv_data dpbs k).
  exact (double_glued_associator_data dpbs k).
  exact (double_glued_associatorinv_data dpbs k).
Defined.


