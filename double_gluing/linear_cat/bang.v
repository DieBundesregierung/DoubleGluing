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
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.

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

(**** Linear Category ****)
Definition functor_distributes_over_bang (C E : linear_category) (F : lax_monoidal_functor C E): UU :=
  nat_trans (functor_composite F (linear_category_bang E)) (functor_composite (linear_category_bang C) F).

Definition linear_distributive_functor_data (C E : linear_category) : UU := ∑ F : sym_monoidal_functor C E, functor_distributes_over_bang C E F.

Definition functor_distributor_respects_unit {C E : linear_category} (Fd : linear_distributive_functor_data C E) : UU.
Proof.
  refine (∏ c : C, _).
  refine ((pr12 Fd c) · (# (pr1 Fd) (linear_category_counit C c)) = _).
  exact ((linear_category_counit E (pr1 Fd c)) · fmonoidal_preservesunit (pr1 Fd)).
Defined.

Definition functor_distributor_respects_comult {C E : linear_category} (Fd : linear_distributive_functor_data C E) : UU.
Proof.
  refine (∏ c : C, _).
  refine ((pr12 Fd c) · (# (pr1 Fd) (linear_category_comult C c)) = _).
  apply (compose (linear_category_comult E (pr1 Fd c))).
  apply (compose (pr1 (pr2 Fd) c ⊗^{E} pr1 (pr2 Fd) c)).
  exact (fmonoidal_preservestensordata (pr1 Fd) _ _).
Defined.

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
       fmonoidal_preservesunit (pr1 L) · (# (pr1 L) (fmonoidal_preservesunit (lax_monoidal_from_symmetric_monoidal_comonad C (linear_category_bang C))))).

Definition linear_distributive_functor_laws {C E : linear_category} (Fd : linear_distributive_functor_data C E) : UU :=
  (functor_distributor_respects_unit Fd) × (functor_distributor_respects_comult Fd) × (islax2cell Fd).

Definition linear_distributive_functor (C E : linear_category) : UU := ∑ Fd : linear_distributive_functor_data C E, linear_distributive_functor_laws Fd.

Definition lax_monoidal_from_linear_functor {C E : linear_category} : linear_distributive_functor C E → sym_monoidal_functor C E := λ F, pr11 F.
Coercion lax_monoidal_from_linear_functor : linear_distributive_functor >-> sym_monoidal_functor.
Definition linear_functor_distributesoverbang {C E : linear_category} (F : linear_distributive_functor C E) : functor_distributes_over_bang C E F := pr21 F.
Notation "κ^{ F }" := (linear_functor_distributesoverbang F).


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
