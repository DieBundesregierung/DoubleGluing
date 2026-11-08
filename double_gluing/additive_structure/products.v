Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Local Open Scope cat.

Require Import preliminaries.
Require Import double_pullbacks.

Require Import double_gluing.double_gluing.
Require Import double_gluing.additive_structure.coproducts.

Definition products_from_opp_coproducts {C : category} (copC : BinCoproducts (C^op)) :
  BinProducts C.
Proof.
  apply copC.
Defined.



Definition double_glued_BinProducts {C E : category} (pc : BinProducts C) (cope : BinCoproducts E) (dpb : doublePullbacks E)
  (L : functor C E) (K : functor C (E ^opp)) : BinProducts (double_glued_total_cat L K).
Proof.
  apply products_from_opp_coproducts.
  induction (double_glued_opp_is_opp L K).
  apply double_glued_BinCoproducts; assumption.
Defined.



