(**************************************

In this file we define functors between linear categories.

*************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.Semantics.LinearLogic.LinearCategory.

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

Require Import double_gluing.closed.internal_hom.
Require Import double_gluing.closed.adjunction.
Require Import double_gluing.closed.closed.


Definition lax_functor_distributes_over_bang (C E : linear_category) (F : lax_monoidal_functor C E): UU :=
  nat_trans (functor_composite F (linear_category_bang_functor E)) (functor_composite (linear_category_bang_functor C) F).

Definition linear_distributive_functor_data (C E : linear_category) : UU := ∑ F : sym_monoidal_functor C E, lax_functor_distributes_over_bang C E F.

Definition linear_functor_distributor_respects_unit {C E : linear_category} (Fd : linear_distributive_functor_data C E) : UU.
Proof.
  refine (∏ c : C, _).
  refine ((pr12 Fd c) · (# (pr1 Fd) (linear_category_counit C c)) = _).
  exact ((linear_category_counit E (pr1 Fd c)) · fmonoidal_preservesunit (pr1 Fd)).
Defined.

Definition linear_functor_distributor_respects_comult {C E : linear_category} (Fd : linear_distributive_functor_data C E) : UU.
Proof.
  refine (∏ c : C, _).
  refine ((pr12 Fd c) · (# (pr1 Fd) (linear_category_comult C c)) = _).
  apply (compose (linear_category_comult E (pr1 Fd c))).
  apply (compose (pr1 (pr2 Fd) c ⊗^{E} pr1 (pr2 Fd) c)).
  exact (fmonoidal_preservestensordata (pr1 Fd) _ _).
Defined.

Definition linear_functor_respects_bang_counit {C E : linear_category} (Fd : linear_distributive_functor_data C E) : UU.
Proof.
  set (bang_counit_E := pr2 (pr112 (linear_category_bang E))).
  set (bang_counit_C := pr2 (pr112 (linear_category_bang C))).
  refine (∏ X : ob C, _).
  refine (bang_counit_E ((pr1 Fd) X) = _).
  apply (compose ((pr12 Fd) X)).
  apply (# (pr11 Fd)).
  apply bang_counit_C.  
Defined.

Definition linear_functor_respects_bang_comult {C E : linear_category} (Fd : linear_distributive_functor_data C E) : UU.
Proof.
  set (bang_comult_E := pr1 (pr112 (linear_category_bang E))).
  set (bang_comult_C := pr1 (pr112 (linear_category_bang C))).
  refine (∏ X: ob C, _).
  refine (bang_comult_E ((pr1 Fd) X) · _ · _ = _ · _).
  refine (# (linear_category_bang_functor E) _).
  apply (pr12 Fd).
  apply (pr12 Fd).
  apply (pr12 Fd).
  apply (# (pr11 Fd)).
  apply bang_comult_C.  
Defined.


Definition linear_functor_is_comonad_mor {C E : linear_category} (Fd : linear_distributive_functor_data C E) : UU := (linear_functor_respects_bang_counit Fd) × (linear_functor_respects_bang_comult Fd).

(*
Definition islax2cell {C E : linear_category} (L : linear_distributive_functor_data C E): UU :=
  (∏ R1 R2 : ob C, ( pr11 (lax_monoidal_from_symmetric_monoidal_comonad E (linear_category_bang E)) (pr1 L R1) (pr1 L R2)
  · (# (pr111 (linear_category_bang E)) (fmonoidal_preservestensordata (pr1 L) R1 R2) · (pr12 L) (R1 ⊗_{ C} R2)) =
  (pr12 L) R1 ⊗^{ E}_{r} (pr111 (linear_category_bang E)) (pr1 L R2)
  · (pr1 L ((pr111 (linear_category_bang C)) R1) ⊗^{ E}_{l} (pr12 L) R2
     · (fmonoidal_preservestensordata (pr1 L) ((pr111 (linear_category_bang C)) R1) ((pr111 (linear_category_bang C)) R2)
          · # (pr1 L) (fmonoidal_preservestensordata (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C)) R1 R2))) ))
    ×
    (fmonoidal_preservesunit (lax_monoidal_from_symmetric_monoidal_comonad E (linear_category_bang E)) ·
       (# (pr111 (linear_category_bang E)) (fmonoidal_preservesunit (pr1 L)) · (pr12 L (I_{C}))) =
       fmonoidal_preservesunit (pr1 L) · (# (pr1 L) (fmonoidal_preservesunit (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C))))). *)

Definition linear_distributor_is_monoidal {C E : linear_category} (Fd : linear_distributive_functor_data C E): UU :=
  is_mon_nat_trans (comp_fmonoidal_lax (pr1 Fd) (linear_category_bang_functor E)) (comp_fmonoidal_lax (linear_category_bang_functor C) (pr1 Fd)) (pr2 Fd).

Definition linear_distributive_functor_laws {C E : linear_category} (Fd : linear_distributive_functor_data C E) : UU :=
  (linear_functor_distributor_respects_unit Fd) × (linear_functor_distributor_respects_comult Fd) ×
    (linear_functor_is_comonad_mor Fd) × (linear_distributor_is_monoidal Fd).

Definition linear_distributive_functor (C E : linear_category) : UU := ∑ Fd : linear_distributive_functor_data C E, linear_distributive_functor_laws Fd.

Definition lax_monoidal_from_linear_functor {C E : linear_category} : linear_distributive_functor C E → sym_monoidal_functor C E := λ F, pr11 F.
Coercion lax_monoidal_from_linear_functor : linear_distributive_functor >-> sym_monoidal_functor.
Definition flinear_distributesoverbang {C E : linear_category} (F : linear_distributive_functor C E) : lax_functor_distributes_over_bang C E F := pr21 F.
Notation "κ^{ F }" := (flinear_distributesoverbang F).
