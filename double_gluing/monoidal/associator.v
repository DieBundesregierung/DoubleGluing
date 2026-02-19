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

Local Lemma double_glued_asociator_data_eq1 {E C : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (R1 R2 R3 : ob C) (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (U1 := pr11 dr1) (U2 := pr11 dr2) (U3 := pr11 dr3) (l1 := pr21 dr1) (l2 := pr21 dr2) (l3 := pr21 dr3) :
  α^{ E }_{ U1, U2, U3} · (l1 ⊗^{ E} (l2 ⊗^{ E} l3 · (pr112 L) R2 R3) · (pr112 L) R1 (R2 ⊗_{ pr211 C} R3)) =
    (l1 ⊗^{ E} l2 · (pr112 L) R1 R2) ⊗^{ E} l3 · (pr112 L) (R1 ⊗_{ pr211 C} R2) R3 · # L α^{ pr211 C }_{ R1, R2, R3}.
Proof.
  refine (maponpaths (λ f, _ · ((_ · f) · _)) (bifunctor_leftcomp E (L R1) _ _ _ (l2 ⊗^{E} l3) ((pr112 L) R2 R3)) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (associator_nat2 E l1 l2 l3) @ _).
  do 2 refine (_ @ assoc _ _ _).
  unfold functoronmorphisms1.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E U3 _ _ _ (l1 ⊗^{ E}_{r} U2 · L R1 ⊗^{ E}_{l} l2) ((pr112 L) R1 R2))).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (assoc' _ _ _ @ _ @ maponpaths (compose _) (assoc' _ _ _)).
  apply maponpaths.
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ (pr112 L R1 R2) l3)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 2 rewrite assoc.
  exact (! pr12 (pr222 L) R1 R2 R3).
Qed.
(*
Print is_nat_trans.
Definition internal_swap_arg_nat3_statement {V : sym_mon_closed_cat} (x y : ob V) : UU.
Proof.
  set (F := functor_composite (pr1 (pr2 V x)) (pr1 (pr2 V y))).
  refine (is_nat_trans F F _).
  Print nat_trans_data.
  intros z.
  unfold F.
  exact (identity _).
Defined.

Lemma internal_swap_arg_nat3 {V : sym_mon_closed_cat} (x y : ob V) : internal_swap_arg_nat3_statement x y.
Proof.
  unfold internal_swap_arg_nat3_statement.
  intros z1 z2 f.
  
Qed.*)


Local Lemma assocdata_lemma1 {C E : sym_mon_closed_cat} {L : sym_monoidal_functor C E} (pb : Pullbacks E) {K : functor C (E ^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {U1 X1 U2 X2 U3 X3 : ob E} (l1 : E⟦U1, L R1⟧) (l1' : E⟦X1, K R1⟧) (l2 : E⟦U2, L R2⟧) (l2' : E⟦X2, K R2⟧) (l3 : E⟦U3, L R3⟧) (l3' : E⟦X3, K R3⟧) :
   (doublePullbackPrL
     (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')))
   · (internal_postcomp U1 (doublePullbackPrR (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))) · internal_swap_arg U1 X2 U3))
  ⊗^{ E}_{r} U3 · internal_eval U3 (internal_hom U1 X2) · internal_postcomp U1 l2' =
  pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
          (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))) ⊗^{ E}_{l} l3
  · (doublePullbackPrM
       (tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
          (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')))
     · (compose (C:=E) (# K α^{ C }_{ R1, R2, R3}) (# K (sym_mon_braiding C R3 (R1 ⊗_{ C} R2))))) ⊗^{ E}_{r} L R3
  · (sym_mon_braiding E (K (R3 ⊗_{ C} (R1 ⊗_{ C} R2))) (L R3) · pr1 k R3 (R1 ⊗_{ C} R2))
  · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2)) .
Proof.
  rewrite assoc'.
  refine (maponpaths (compose _) (internal_eval_nat _ _ _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E U3 _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U3) (_ @ assoc' _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (maponpaths (compose _) (internal_swap_arg_nat3 U1 U3 _ _ l2') @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) _ @ _).
  rewrite <- (internal_postcomp_comp U1).
  refine (maponpaths (internal_postcomp _) (! doublePullbackSqrRCommutes _) @ _).
  apply (internal_postcomp_comp U1).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _) @ _).
  apply assoc'.
  apply (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite 3 internal_lam_precomp.
  repeat rewrite assoc.
  rewrite internal_lam_postcomp.
  repeat rewrite internal_lam_natural.
  unfold monoidal_cat_tensor_mor; rewrite 3 (when_bifunctor_becomes_rightwhiskering E).
  rewrite internal_lam_lam_swap.
  refine (internal_lam_tensor_eval _ @ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) _).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (maponpaths (compose _) (! natural_contraction_composed k _ _ _)).
    }
    apply assoc'.
  }
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  rewrite assoc'.
  refine (maponpaths (compose _) (! pr12 k _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  now rewrite assoc.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _ @ _) @ _).
  refine (maponpaths (compose _)  (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (natural_contraction_composed k _ _ _ @ _) @ _).
  refine (_ @ maponpaths (compose _) (natural_contraction_extranatural k R2 _ _ (sym_mon_braiding C R1 R3))).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! id_left _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_leftid E _ _ @ _ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! functor_id K _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (! bifunctor_rightid C _ _ @ _ @ bifunctor_rightcomp C _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_inverses C _ _).
  apply assoc.
  apply assoc.
  apply assoc.
  do 2 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (_ @ assoc _ _ _) @ _).
  apply maponpaths.
  apply (bifunctor_leftcomp E).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _)  (! bifunctor_rightcomp E _ _ _ _ _ _ @ _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (fsym_respects_braiding L).
  apply assoc.
  apply assoc.
  apply assoc.
  apply assoc.
  refine (assoc _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (compose _) _).
    2 : {
      refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
      apply maponpaths.
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
      apply assoc'.
    }
    apply assoc'.
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _ @ _)).
  3 : {
    apply maponpaths.
    refine (_ @ assoc _ _ _).
    apply assoc.
  }
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatorinvnatleft E _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
        apply (bifunctor_equalwhiskers E).
      }
      apply assoc'.
    }
    apply assoc'.
  }
  refine (_ @ assoc' _ _ _).
  apply map_on_two_paths.
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  do 4 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! monoidal_associatorinvnatleftright E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _ @ _) @ _).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_left E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleft E _ _ _ _ _) @ _).
  apply assoc'.
  apply assoc'.
  repeat rewrite assoc'.
  apply maponpaths.
  do 3 refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _ @ _) @ _).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleftright E _ _ _ _ _) @ _).
  apply assoc'.
  apply assoc'.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ ! monoidal_braiding_naturality_right E _ _ _ _)).
  2 : {
    rewrite (bifunctor_rightcomp E).
    apply assoc.
  }
  repeat rewrite assoc'.
  apply maponpaths.
  use pathscomp0.
  apply (compose (sym_mon_braiding E _ _ ⊗^{E}_{r} _ · α^{E}_{_,_,_})).
  apply (compose (_ ⊗^{E}_{l} sym_mon_braiding E _ _)).
  apply (compose (αinv^{E}_{_,_,_})).
  apply (sym_mon_braiding E _ _ ⊗^{E}_{r} _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (sym_mon_tensor_lassociator1 E _ _ _) @ _).
  refine (_ @ id_right _).
  do 2 refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ pr1 (monoidal_braiding_inverses E _ _)).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ id_left _).
  apply (maponpaths (postcompose _)).
  apply (monoidal_associatorisolaw E).
  rewrite assoc'.
  apply maponpaths.
  refine (_ @ ! maponpaths (λ f, f · _) (sym_mon_tensor_rassociator E _ _ _)).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E), <- (when_bifunctor_becomes_rightwhiskering E).
  refine (! id_right _ @ _).
  repeat rewrite assoc'.
  repeat apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorisolaw E).
  apply maponpaths.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _)).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply pathsinv0.
  rewrite <- (when_bifunctor_becomes_leftwhiskering C), <- (when_bifunctor_becomes_rightwhiskering C).
  apply (sym_mon_hexagon_lassociator C).
Qed.

Local Lemma assocdata_lemma2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} {U1 U2 U3 X1 X2 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (dpb23 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))
  (dpb123 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
          ((U2 ⊗_{ E} U3,, l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L) R2 R3),,
           pr11 (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')),,
           doublePullbackPrM dpb23))
  :
  pr11 dpb123 ⊗^{ E}_{l} l3
  · (doublePullbackPrM dpb123
     · (compose (C:=E) (# K α^{ C }_{ R1, R2, R3}) (# K (sym_mon_braiding C R3 (R1 ⊗_{ C} R2))))) ⊗^{ E}_{r} L R3
  · (sym_mon_braiding E (K (R3 ⊗_{ C} (R1 ⊗_{ C} R2))) (L R3) · pr1 k R3 (R1 ⊗_{ C} R2))
  · (compose (C:=E) (# K (sym_mon_braiding C R2 R1)) (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1) · internal_precomp l2 (K R1))) =
  doublePullbackPrR dpb123 ⊗^{ E}_{r} U3
  · (internal_precomp (sym_mon_braiding E U3 U2) X1 ⊗^{ E}_{r} U3 · (internal_curry U3 U2 X1 ⊗^{ E}_{r} U3 · internal_eval U3 (internal_hom U2 X1)))
  · internal_postcomp U2 l1' .
Proof.
  rewrite assoc'.
  refine (! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  do 2 refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U3))) _ _ _)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite (functor_comp (pr1 (pr2 E U2))).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 f ⊗^{E}_{r} U3 · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_postcomp U3 (f · _) ⊗^{E}_{r} U3 · _)) (triangle_id_right_ad (pr2 (pr2 E U2)) _)).
  rewrite id_left.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f ⊗^{ E}_{r} U3 · _) (curry_nat3 U3 U2 l1')).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f ⊗^{ E}_{r} U3 · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _) ⊗^{E}_{r}U3 · _)
            (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ maponpaths (λ f, _ · f ⊗^{ E}_{r} U3 · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U3 · _) (doublePullbackSqrRCommutes dpb123)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  unfold functoronmorphisms1.
  rewrite assoc'.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_rightcomp E U3 _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite internal_precomp_comp.
  do 2 refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U3 · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} U3 · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · ((f · _) ⊗^{E}_{r} U3 · _)) (internal_precomp_comp _ _ (K R1))).
  refine (_ @ maponpaths (λ f, _ · ((internal_precomp f (K R1) · _) ⊗^{E}_{r} U3 · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · ((internal_precomp (f · _) (K R1) · _) ⊗^{E}_{r} U3 · _)) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · ((internal_precomp f (K R1) · _) ⊗^{E}_{r} U3 · _)) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · ((internal_precomp (_ · f) (K R1) · _) ⊗^{E}_{r} U3 · _)) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · ((internal_precomp f (K R1) · _) ⊗^{E}_{r} U3 · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · ((f · _) ⊗^{E}_{r} U3 · _)) (internal_precomp_comp _ _ (K R1))).
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} U3 · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · ((_ · (internal_precomp f _ · _)) ⊗^{E}_{r} U3 · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · ((_ · f) ⊗^{E}_{r} U3 · _)) (curry_nat12 _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} U3 · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} U3 · _)) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E U3 _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} U3 · _)) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ ! maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U3))) _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  do 3 refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (mon_closed_adj_natural_co E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _ )).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _ ) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  repeat rewrite assoc.
  rewrite internal_lam_natural.
  refine (internal_lam_natural _ _ @ _).
  rewrite 2 internal_lam_precomp.
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (! internal_lam_curry _)).
  refine (_ @ ! internal_lam_tensor_eval _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_braiding_naturality_right E _ _ _ _ @ _) @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  rewrite assoc'.
  refine (map_on_two_paths _ _ _ @ _).
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  apply pathsinv0.
  refine (pr12 k _ _ _ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _)).
  refine (maponpaths (compose _) (! bifunctor_leftcomp E _ _ _ _ _ _ )).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (natural_contraction_composed k _ _ _ @ _) @ _).
  refine (maponpaths (compose _) _ @ _).
  refine (_ @ maponpaths (compose _) (natural_contraction_extranatural k R1 _ _ (sym_mon_braiding C R3 R2))).
  refine (! id_left _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_leftid E _ _ @ _ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! functor_id K _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (! bifunctor_rightid C _ _ @ _ @ bifunctor_rightcomp C _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_inverses C _ _).
  apply assoc.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite (bifunctor_leftcomp E (L R2)).
  do 5 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatleft E _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (! bifunctor_equalwhiskers E _ _ _ _ _ _).
  apply assoc.
  apply assoc.
  apply assoc.
  refine (assoc _ _ _ @ _).
  apply map_on_two_paths.
  rewrite 2 assoc.
  refine (maponpaths (compose _) (! bifunctor_rightcomp E _ _ _ _ _ _ @ _) @ _).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (fsym_respects_braiding L).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (_ @ id_right _).
  apply map_on_two_paths.
  refine (_ @ maponpaths (compose _) (! sym_mon_tensor_lassociator E _ _ _)).
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_leftwhiskering E).
  repeat rewrite assoc.
  do 2 apply (maponpaths (postcompose _)).
  rewrite <- (when_bifunctor_becomes_leftwhiskering E).
  apply (sym_mon_tensor_rassociator E).  
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @ bifunctor_rightid E _ _).
  apply maponpaths.
  apply (monoidal_braiding_inverses E).
  apply maponpaths.
  refine (_ @ ! functor_comp K _ _ @ _).
  apply (maponpaths (postcompose (C:=E) _)).
  refine (_ @ ! functor_comp K _ _).
  apply (maponpaths (postcompose (C:=E) _)).
  refine (_ @ ! functor_comp K _ _).
  apply (maponpaths (postcompose (C:=E) _)).
  refine (! functor_comp K _ _).
  apply maponpaths.
  refine (_ @ ! sym_mon_tensor_rassociator C _ _ _).
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering C).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_braiding_naturality_left C _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator C _ _ _) @ _).
  refine (_ @ id_left _ ).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering C).
  refine (_ @ bifunctor_rightid C _ _).
  unfold monoidal_cat_tensor_pt.
  refine (_ @ maponpaths (λ f, f ⊗^{C}_{r} _) (pr2 (monoidal_braiding_inverses C _ _))).
  rewrite (bifunctor_rightcomp C).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _ @ id_right _).
  apply maponpaths.
  apply (monoidal_associatorisolaw C).
Qed.

Local Lemma assocdata_lemma3 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} {U1 U2 U3 X1 X2 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧)
  (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) :
  doublePullbackPrL
    (tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
       ((U2 ⊗_{ E} U3,, l2 ⊗^{ E} l3 · (pr112 L) R2 R3),,
        pr11 (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))))
  · (internal_postcomp U1 (doublePullbackPrL (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))) · internal_uncurry U1 U2 X3)
  · internal_postcomp (U1 ⊗_{ E} U2) l3' =
  doublePullbackPrM
    (tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
       ((U2 ⊗_{ E} U3,, l2 ⊗^{ E} l3 · (pr112 L) R2 R3),,
        pr11 (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')))) · # K α^{ C }_{ R1, R2, R3}
  · (internal_lam (sym_mon_braiding E (K ((R1 ⊗_{ pr211 C} R2) ⊗_{ C} R3)) (L (R1 ⊗_{ pr211 C} R2)) · pr1 k (R1 ⊗_{ pr211 C} R2) R3)
     · internal_precomp (l1 ⊗^{ E} l2 · (pr112 L) R1 R2) (K R3)).
Proof.
  set (dpb123 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
       ((U2 ⊗_{ E} U3,, l2 ⊗^{ E} l3 · (pr112 L) R2 R3),,
        pr11 (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')))).
  set (dpb23 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (uncurry_nat3 U1 U2 l3') @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (internal_postcomp_comp U1 _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp U1 f · _) (doublePullbackSqrLCommutes dpb23) @ _).
  refine (maponpaths (λ f, _ · f · _) (internal_postcomp_comp U1 _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes dpb123) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  unfold internal_lam.
  do 3 rewrite hom_onmorphisms_is_postcomp.
  rewrite (maponpaths (compose _) (assoc' _ _ _)).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  refine (maponpaths (λ f, _ · (f · _) · _) (internal_postcomp_comp (L R1) _ _) @ _).
  rewrite assoc'.
  do 2 rewrite (maponpaths (compose _) (assoc' _ _ _)).
  rewrite assoc.
  rewrite (maponpaths (compose _) (assoc _ _ _)).
  refine (! maponpaths (compose _) (uncurry_nat12 (V:=E) (K R3) l1 l2) @ _).
  rewrite internal_precomp_comp.
  repeat refine (assoc _ _ _ @ _).
  repeat refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  repeat refine (assoc _ _ _ @ _).
  repeat refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (maponpaths (λ f, _ · _ · f · _) (internal_postcomp_comp (L R1) _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _ · _) (assoc' _ _ _) @ _).
  rewrite assoc'.
  refine (! maponpaths (λ f,  _ · f · _) (internal_postcomp_comp (L R1) _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp (L R1) f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (L R2)))) _ _ _) @ _).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f,  _ · f · _) (internal_postcomp_comp (L R1) _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (internal_postcomp_comp (L R1) _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_postcomp (L R1) f · _) (internal_postcomp_comp (L R2) _ _ ) @ _).
  rewrite assoc'.
  refine (! maponpaths (compose _) (uncurry_nat3 (L R1) (L R2) _) @ _).
  rewrite assoc. 
  refine (maponpaths (λ f, f · _) (uncurry_unit (L R1) (L R2) _) @ _).
  refine (_ @ ! maponpaths (λ f, f · _ · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (L (R1 ⊗_{ pr211 C} R2))))) _ _ _)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (internal_postcomp_comp _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (mon_closed_adj_natural _ _ _ _ _)).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp (L R1 ⊗_{E} L R2) _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  rewrite (bifunctor_rightcomp E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc _ _ _) @ _).
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  generalize (! pr2 (pr222 k) R1 R2 R3); unfold postcompose; simpl; intros keq.
  refine (_ @ maponpaths (compose _) keq); clear keq.
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).  
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  rewrite assoc.
  refine (_ @ id_right _).
  rewrite <- (bifunctor_leftid E).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr1 (monoidal_braiding_inverses E _ _)).
  rewrite (bifunctor_leftcomp E).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ map_on_two_paths compose _ _).
  3 : {
    refine (_ @ sym_mon_hexagon_rassociator0 _ _ _ _).
    now rewrite 2 assoc'.
  }
  2 : {
    apply pathsinv0.
    apply (monoidal_braiding_naturality_left E).
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc _ _ _)).
  2 : {
    refine (_ @ maponpaths (compose _) (! pr1 (monoidal_braiding_inverses E _ _))).
    apply pathsinv0.
    apply id_right.
  }
  rewrite 2 assoc.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E), <- (when_bifunctor_becomes_rightwhiskering E).
  refine (maponpaths (compose _) (sym_mon_tensor_rassociator E _ _ _) @ _).
  refine (_ @ id_left _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  apply (monoidal_associatorisolaw E).  
Qed.

Local Lemma assocdata_lemma4 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} {U1 U2 U3 X1 X2 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (dpb23 := tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))
  (dpb1_23 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1')
       ((U2 ⊗_{ E} U3,, l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L) R2 R3),,
        pr11 dpb23,,
        doublePullbackPrM dpb23))
  (dpb12 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')):
  doublePullbackPrM dpb1_23 · # K α^{ C }_{ R1, R2, R3}
  · (compose (C:=E) (# K (sym_mon_braiding C R3 (R1 ⊗_{ pr211 C} R2)))
     (internal_lam ((pr121 E) (K (R3 ⊗_{ C} (R1 ⊗_{ pr211 C} R2))) (L R3) · pr1 k R3 (R1 ⊗_{ pr211 C} R2))
        · internal_precomp l3 (K (R1 ⊗_{ pr211 C} R2)))) =
  internal_lam
    (doublePullbackArrow dpb12
       (pr11 dpb1_23 ⊗_{E} U3)
       ((doublePullbackPrL dpb1_23
         · (internal_postcomp U1 (doublePullbackPrR dpb23)
            · internal_swap_arg U1 X2 U3)) ⊗^{ E}_{r} U3 · internal_eval U3 (internal_hom U1 X2))
       (pr11 dpb1_23 ⊗^{ E}_{l} l3
        · (doublePullbackPrM dpb1_23
           · (compose (C:=E) (# K α^{ C }_{ R1, R2, R3}) (# K (sym_mon_braiding C R3 (R1 ⊗_{ C} R2))))) ⊗^{ E}_{r} L R3
        · (sym_mon_braiding E (K (R3 ⊗_{ C} (R1 ⊗_{ C} R2))) (L R3) · pr1 k R3 (R1 ⊗_{ C} R2)))
       (doublePullbackPrR dpb1_23 ⊗^{ E}_{r} U3
        · (internal_precomp (sym_mon_braiding E U3 U2) X1 ⊗^{ E}_{r} U3 · (internal_curry U3 U2 X1 ⊗^{ E}_{r} U3 · internal_eval U3 (internal_hom U2 X1))))
       (assocdata_lemma1 pb k l1 l1' l2 l2' l3 l3') (assocdata_lemma2 pb k l1 l1' l2 l2' l3 l3'))
  · internal_postcomp U3 (doublePullbackPrM dpb12).
Proof.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_precomp _ _) @ _).
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_postcomp _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ ! doublePullbackArrow_PrM dpb12 _ _ _ _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  apply assoc'.
Qed.


Definition double_glued_assoc_data_comp2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2)
  (dr3 : double_glued_cat L K R3) :
  double_glued_mor_comp2 L K _ _ (disp_bifunctor_on_objects (double_glued_tensor pb L K k) (R1 ⊗_{ pr211 C} R2) R3 (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R1 R2 dr1 dr2) dr3) (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R1 (R2 ⊗_{ pr211 C} R3) dr1 (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R2 R3 dr2 dr3)).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct dr3 as ((U3, l3), (X3, l3')).
  use (doublePullbackArrow _).
  apply (compose (doublePullbackPrL _)).
  apply (compose (internal_postcomp U1 (doublePullbackPrL _))).
  exact (internal_uncurry U1 U2 X3).
  apply (compose (doublePullbackPrM _)).
  exact (# K (α_{C} R1 R2 R3)).
  apply internal_lam.
  use (doublePullbackArrow _).
  apply (postcompose (internal_eval U3 _)).
  refine (_ ⊗^{E}_{r} U3).
  apply (compose (doublePullbackPrL _)).
  apply (compose (internal_postcomp U1 (doublePullbackPrR _))).
  exact (internal_swap_arg U1 X2 U3).
  apply (postcompose (sym_mon_braiding E _ _ · pr1 k R3 _)).
  apply (compose (_ ⊗^{E}_{l} l3)).
  refine (_ ⊗^{E}_{r} (L R3)).
  apply (compose (doublePullbackPrM _)).
  apply (compose (C:=E) (# K (α_{C} R1 R2 R3 ))).
  exact (# K (sym_mon_braiding C _ _ )).
  apply (compose ((doublePullbackPrR _) ⊗^{E}_{r} U3)).
  apply (compose (internal_precomp (sym_mon_braiding E _ _ ) X1 ⊗^{E}_{r} U3)).
  apply (compose (internal_curry _ _ _ ⊗^{E}_{r} U3)).
  exact (internal_eval U3 _).
  unfold postcompose.
  exact (assocdata_lemma1 pb k l1 l1' l2 l2' l3 l3').
  exact (assocdata_lemma2 pb k l1 l1' l2 l2' l3 l3').
  exact (assocdata_lemma3 pb k l1 l1' l2 l2' l3 l3').
  exact (assocdata_lemma4 pb k l1 l1' l2 l2' l3 l3').
Defined.

Lemma double_glued_assoc_data_eq2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2)
  (dr3 : double_glued_cat L K R3) :
  double_glued_mor_eq2 L K ((R1 ⊗_{ pr211 C} R2) ⊗_{ pr211 C} R3) (R1 ⊗_{ pr211 C} (R2 ⊗_{ pr211 C} R3))
    (disp_bifunctor_on_objects (double_glued_tensor pb L K k) (R1 ⊗_{ pr211 C} R2) R3
       (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R1 R2 dr1 dr2) dr3)
    (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R1 (R2 ⊗_{ pr211 C} R3) dr1
       (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R2 R3 dr2 dr3)) α^{ pr211 C }_{ R1, R2, R3}
                                                                                     (double_glued_assoc_data_comp2 pb k dr1 dr2 dr3).
Proof.
  unfold double_glued_mor_eq2; simpl.
  exact (! doublePullbackArrow_PrM _ _ _ _ _ _ _).
Qed.

Definition double_glued_associator_data {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) : disp_associator_data (double_glued_tensor pb L K k).
Proof.
  intros R1 R2 R3 dr1 dr2 dr3.
  split.
  exists (α_{E} (pr11 dr1) (pr11 dr2) (pr11 dr3)).
  exact (double_glued_asociator_data_eq1 R1 R2 R3 dr1 dr2 dr3).
  (* component 2: *)
  exists (double_glued_assoc_data_comp2 pb k dr1 dr2 dr3).
  exact (double_glued_assoc_data_eq2 pb k dr1 dr2 dr3).
Defined.

Local Lemma associnvdata_lemma1 {E C : sym_mon_closed_cat} {L : sym_monoidal_functor C E} {K : C ⟶ E ^opp} {R1 R2 R3 : C} {U1 U2 U3 X1 X2 X3 : E}
  (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧):
  αinv^{ E }_{ U1, U2, U3} · ((l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2) ⊗^{ E} l3 · (fmonoidal_preservestensordata L) (R1 ⊗_{ pr211 C} R2) R3) =
  l1 ⊗^{ E} (l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L) R2 R3) · (fmonoidal_preservestensordata L) R1 (R2 ⊗_{ pr211 C} R3) · # L αinv^{ pr211 C }_{ R1, R2, R3} .
Proof.
  simpl.
  refine (_ @ id_left _).
  rewrite <- (pr2 (monoidal_associatorisolaw E U1 U2 U3)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  generalize (double_glued_asociator_data_eq1 R1 R2 R3 ((U1,, l1),, (X1,, l1')) ((U2,, l2),, (X2,, l2')) ((U3,, l3),, (X3,, l3'))); simpl; intros eq1.
  refine (_ @ ! maponpaths (postcompose _) eq1).
  refine (_ @ assoc _ _ _).
  refine (! id_right _ @ _).
  apply maponpaths.
  rewrite <- (functor_comp L).
  rewrite <- (functor_id L).
  apply maponpaths.
  exact (! pr1 (monoidal_associatorisolaw C R1 R2 R3)).
Qed.

Local Lemma associnvdata_lemma21 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} {U1 U2 U3 X1 X2 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧):
  doublePullbackPrL
    (tensor_doublePullback pb k
       ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
        pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3')) ⊗^{ E}_{r} U1
  · (internal_curry U1 U2 X3 ⊗^{ E}_{r} U1 · internal_eval U1 (internal_hom U2 X3)) · internal_postcomp U2 l3' =
  doublePullbackPrM
    (tensor_doublePullback pb k
       ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
        pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3')) ⊗^{ E}_{r} U1
  · (K ((R1 ⊗_{ pr211 C} R2) ⊗_{ C} R3) ⊗^{ E}_{l} l1
     · (sym_mon_braiding E (K ((R1 ⊗_{ pr211 C} R2) ⊗_{ C} R3)) (L R1) · (L R1 ⊗^{ E}_{l} # K αinv^{ C }_{ R1, R2, R3} · pr1 k R1 (R2 ⊗_{ C} R3))))
  · (internal_lam (sym_mon_braiding E (K (R2 ⊗_{ C} R3)) (L R2) · pr1 k R2 R3) · internal_precomp l2 (K R3)).
Proof.
  set (dpb := tensor_doublePullback pb k
       ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
        pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3')).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f)) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _) @ _).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  rewrite (functor_comp (pr1 (pr2 E U2))).
  rewrite (maponpaths (internal_postcomp U1) (assoc _ _ _)).
  refine (maponpaths (λ f, (_ · (_ · internal_postcomp U1 (f · _))) ⊗^{E}_{r} U1 · _)
            (triangle_id_right_ad (pr2 (pr2 E U2)) X3) @ _).
  rewrite id_left.
  rewrite hom_onmorphisms_is_postcomp.
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} U1 · _) (curry_nat3 U1 U2 l3') @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U1 · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} U1 · _) (doublePullbackSqrLCommutes dpb) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} U1 · _) (assoc' _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite 2 internal_lam_precomp.
(*  Check (internal_curry U1 U2 (K R3)). *)
  refine (_ @ maponpaths (λ f, _ · f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose _) (internal_lam_natural _ _)).
  unfold monoidal_cat_tensor_mor, functoronmorphisms1.
  rewrite (bifunctor_leftid E).
  rewrite id_right.
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_lam (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f · _))) (id_left _)).
  set (assoceq := pr2 (monoidal_associatorisolaw E (L R2) (L R1) (K (R1 ⊗_{ C} (R2 ⊗_{ C} R3))))).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f · _ · _))) assoceq); clear assoceq.
  do 2 refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f · _))) (id_left _)).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  rewrite (bifunctor_rightcomp E (K (R1 ⊗_{ C} (R2 ⊗_{ C} R3)))).
  do 2 refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f)) (pr2 (pr222 k) R1 R2 R3)).
  refine (maponpaths (λ f, (internal_lam f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  unfold internal_lam.
  rewrite (functor_comp (pr1 (pr2 E (U1 ⊗_{ E} U2)))).
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite 3 hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _) @ _).
  repeat rewrite assoc.
  rewrite (internal_postcomp_comp U2).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite (bifunctor_leftcomp E).
  refine (maponpaths (λ f, (_ · internal_postcomp _ f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (maponpaths (λ f, (_ · internal_postcomp _ f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite internal_postcomp_comp.
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _) @ _).
  repeat rewrite assoc.
  rewrite (internal_postcomp_comp U2).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U2 (f · _ · _ · _)) (monoidal_braiding_naturality_left E _ _ _ _)).
  do 3 refine (_ @ maponpaths (λ f, _ · internal_postcomp U2 f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U2 (_ · f)) (assoc' _ _ _)).
  rewrite (monoidal_associatorinvnatright E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U2 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U2 f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U2 (_ · f)) (assoc' _ _ _)).
  unfold monoidal_braiding_data_inv.
  rewrite <- (bifunctor_rightcomp E).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp U2 (_ · (f · _))) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U2 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U2 f) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp U2 (_ · f)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U2 f) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (! maponpaths (λ f, (_ · internal_postcomp _ f · _) ⊗^{E}_{r} _ · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  rewrite internal_postcomp_comp.
  refine (maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  refine (! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, _ · (internal_postcomp _ f)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  do 3 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (pr2 (unit_from_are_adjoints (pr2 (pr2 E U2))) _ _ _)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 (_ · f))) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 f)) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 (_ · f))) (assoc' _ _ _)).
  rewrite (monoidal_associatorinvnatleftright E).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 (_ · f))) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 (_ · f))) (assoc' _ _ _)).
  rewrite <- (bifunctor_rightcomp E).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ ! maponpaths (λ f, _ · (internal_postcomp U2 (_ · (f · _)))) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 (_ · f))) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 f)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_postcomp U2 (_ · f))) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U2 f)) (assoc' _ _ _)).
  rewrite internal_postcomp_comp.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E U2))) _ _ _)).
  simpl.
  refine (_ @ assoc _ _ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (compose _) (internal_postcomp_comp _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ f) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (assoc' _ _ _)).
  rewrite (monoidal_associatorinvnatleft E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · (f · _))) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ f) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp _ (_ · _ ⊗^{E}_{l} f)) (functor_comp K _ _)).
  rewrite (pr1 (monoidal_associatorisolaw C _ _ _)).
  rewrite (functor_id K).
  rewrite (bifunctor_leftid E).
  rewrite id_right.
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (curry_unit _ _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  rewrite <- (internal_postcomp_comp U1).
  refine (! maponpaths (λ f, (_ · internal_postcomp U1 f) ⊗^{E}_{r} _ · _) (internal_postcomp_comp U2 _ _) @ _).
  refine (maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_postcomp_comp U1 _ _) @ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _) @ _).
  simpl.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (triangle_id_left_ad (pr2 (pr2 E _)) _) @ _).
  rewrite id_left.
  do 2 apply maponpaths.
  refine (! id_right _ @ _).
  rewrite <- (pr1 (monoidal_associatorisolaw E _ _ _)).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (sym_mon_hexagon_lassociator _ _ _ _) @ _).
  unfold monoidal_cat_tensor_mor, functoronmorphisms1.
  rewrite (bifunctor_rightid E).
  rewrite (bifunctor_leftid E).
  rewrite id_left.
  rewrite id_right.
  rewrite (monoidal_braiding_naturality_right E).
  do 2 refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (sym_mon_hexagon_rassociator0 E _ _ _) @ _).
  refine (_ @ id_right _).
  repeat rewrite assoc'.
  repeat apply maponpaths.
  apply monoidal_associatorisolaw.
Qed.

Local Lemma associnvdata_lemma22 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} {U1 U2 U3 X1 X2 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) :
doublePullbackPrM
    (tensor_doublePullback pb k
       ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
        pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3')) ⊗^{ E}_{r} U1
  · (K ((R1 ⊗_{ pr211 C} R2) ⊗_{ C} R3) ⊗^{ E}_{l} l1
     · (sym_mon_braiding E (K ((R1 ⊗_{ pr211 C} R2) ⊗_{ C} R3)) (L R1) · (L R1 ⊗^{ E}_{l} # K αinv^{ C }_{ R1, R2, R3} · pr1 k R1 (R2 ⊗_{ C} R3))))
  · (compose (C:=E) (# K (sym_mon_braiding C R3 R2)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R2)) (L R3) · pr1 k R3 R2) · internal_precomp l3 (K R2))) =
  doublePullbackPrR
    (tensor_doublePullback pb k
       ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
        pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3')) ⊗^{ E}_{r} U1
  · (internal_postcomp U3 (doublePullbackPrL (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ⊗^{ E}_{r} U1
     · (internal_swap_arg U3 X2 U1 ⊗^{ E}_{r} U1 · internal_eval U1 (internal_hom U3 X2))) · internal_postcomp U3 l2'.
Proof.
  set (dpb12 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')).
  set (dpb12_3 := tensor_doublePullback pb k
                    ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
                       pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),, doublePullbackPrM dpb12) ((U3,, l3),, X3,, l3')).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · (_ · f))) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _)).
  simpl.
  rewrite (functor_comp (pr1 (pr2 E U3))).
  refine (_ @ maponpaths (λ f, _ · (_ · (_ · (# _ f ⊗^{E}_{r} _ · _)))) (assoc' (C:=E) _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · (_ · (# _ (f · _) ⊗^{E}_{r} _ · _)))) (triangle_id_right_ad (pr2 (pr2 E _)) _)).
  rewrite id_left. 
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (λ f, _ · (_ · (_ · (f ⊗^{E}_{r} _ · _)))) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · (f · _))) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · (f ⊗^{E}_{r} _ · _))) (internal_swap_arg_nat3 _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · (f · _))) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f) (assoc' _ _ _)).
  rewrite <- (bifunctor_rightcomp E U1).
  rewrite <- (internal_postcomp_comp U3).
  refine (_ @ ! maponpaths (λ f, _ · (internal_postcomp U3 f ⊗^{E}_{r} _ · _)) (doublePullbackSqrLCommutes dpb12)).
  rewrite (internal_postcomp_comp U3).
  rewrite (bifunctor_rightcomp E U1).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (doublePullbackSqrRCommutes dpb12_3)).
  rewrite (bifunctor_rightcomp E U1).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite 3 internal_lam_precomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  rewrite 2 assoc.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (pr12 k R1 _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite internal_lam_natural.
  rewrite assoc.
  simpl.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  rewrite (maponpaths internal_lam (assoc _ _ _)).
  refine (maponpaths (λ f, _ · internal_lam (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam (_ · f)) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  unfold monoidal_cat_tensor_pt.
  refine (maponpaths (λ f, _ · internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_lam (_ · (f · _))) (id_left _) @ _).
  rewrite <- (pr2 (monoidal_associatorisolaw _ _ _ _)).
  do 2 refine (maponpaths (λ f, _ · internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_lam (_ · (f · _))) (id_left _) @ _).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  rewrite (bifunctor_rightcomp E (K (R1 ⊗_{ C} (R3 ⊗_{C} R2)))).
  do 2 refine (maponpaths (λ f, _ · internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_lam f) (assoc _ _ _) @ _).
  do 2 refine (maponpaths (λ f, _ · internal_lam (_ · f)) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · internal_lam (_ · f)) (pr2 (pr222 k) R1 R3 R2) @ _).
  unfold internal_lam.
  rewrite 3 hom_onmorphisms_is_postcomp.
  rewrite (maponpaths (λ f, (f · _) ⊗^{E}_{r} U1) (assoc _ _ _)).
  rewrite (maponpaths (λ f, f ⊗^{E}_{r} U1) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} U1 · _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ maponpaths (λ f, (_ · internal_postcomp U3 f) ⊗^{E}_{r} U1 · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · internal_postcomp U3 (f · _)) ⊗^{E}_{r} U1 · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, (_ · internal_postcomp U3 f) ⊗^{E}_{r} U1 · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · internal_postcomp U3 (_ · f)) ⊗^{E}_{r} U1 · _) (internal_postcomp_comp U1 _ _)).
  rewrite (maponpaths (internal_postcomp U1) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · internal_postcomp U3 (_ · internal_postcomp U1 (f · _))) ⊗^{E}_{r} U1 · _)
            (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · internal_postcomp U3 (_ · internal_postcomp U1 f)) ⊗^{E}_{r} U1 · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · internal_postcomp U3 (_ · internal_postcomp U1 (_ · f))) ⊗^{E}_{r} U1 · _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ ! maponpaths (λ f, (_ · f) ⊗^{E}_{r} U1 · _) (internal_postcomp_comp U3  _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U1 · _) (assoc' _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (bifunctor_rightcomp E U1).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U1 · _) (assoc _ _ _)).
  rewrite <- internal_swap_arg_nat3.
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U1 · _) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E U1).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ ! maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _)).
  simpl.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · (_ ⊗^{E}_{l} f · _))) (assoc' _ _ _)).
  rewrite (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (f · _)) (id_left _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (f · _ · _)) (pr2 (monoidal_associatorisolaw _ _ _ _))).
  do 2 refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · (f · _))) (id_left _)).
  rewrite <- (bifunctor_rightid E).
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  rewrite (bifunctor_rightcomp E (K (R3 ⊗_{ C} (R1 ⊗_{C} R2)))).
  do 2 refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · (f · _))) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (pr2 (pr222 k) R3 R1 R2)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (id_left _)).
  rewrite <- (bifunctor_leftid E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · (_ ⊗^{E}_{l} f · _))) (functor_id K _)).
  rewrite <- (bifunctor_rightid C).
  rewrite <- (pr1 (monoidal_braiding_inverses C _ _)).
  rewrite (bifunctor_rightcomp C R2).
  rewrite (functor_comp K).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp U3 (_ · (f · _))) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  generalize (pr122 k R2 _ _ (sym_mon_braiding C R3 R1)); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) keq).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f) (internal_postcomp_comp U3 _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite assoc.
  refine (maponpaths (λ f, _ · internal_postcomp U3 f) (assoc _ _ _) @ _).
  rewrite (internal_postcomp_comp U3).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 (f · _ · _))) (assoc' _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 (_ · f))) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (internal_postcomp U3 (_ · (f · _)))) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 (_ · f))) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 f)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 (_ · f))) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 (_ · f ⊗^{E}_{r} _))) (fsym_respects_braiding L R3 R1)).
  rewrite (bifunctor_rightcomp E (K ((R1 ⊗_{ C} R3) ⊗_{ C} R2))).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 f)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ assoc' _ _ _).
  refine (maponpaths (λ f, _ · (internal_postcomp U3 f)) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (internal_postcomp_comp U3 _ _) @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  rewrite <- (internal_postcomp_comp U3).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (maponpaths (λ f, f · _ · _) (assoc' _ _ _) @ _).
  rewrite <- (bifunctor_leftcomp E (L R1)).
  refine (maponpaths (λ f, f · _ · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _ · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  rewrite <- (hom_onmorphisms_is_postcomp U3).
  refine (internal_lam_natural _ _ @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (! maponpaths (λ f, internal_lam (_ · (f · _ · _ · _))) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  do 3 refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (internal_lam) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  rewrite (monoidal_associatorinvnatright E).
  unfold monoidal_braiding_data_inv.
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (internal_lam) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  rewrite <- (bifunctor_rightcomp E).
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite (bifunctor_rightcomp E (K (R1 ⊗_{ C} (R3 ⊗_{ C} R2)))).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  rewrite (bifunctor_rightcomp E U3).
  do 4 refine (maponpaths internal_lam (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  rewrite (monoidal_associatorinvnatleftright E).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  rewrite <- (bifunctor_rightcomp E).
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite (bifunctor_rightcomp E (K (R1 ⊗_{ C} (R3 ⊗_{ C} R2)))).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f · _))) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).  
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  rewrite <- (bifunctor_rightcomp E).
  do 2 rewrite <- (monoidal_braiding_naturality_left E).
  do 3 refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · (_ · f))) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp U3 (_ · (f · _))) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  rewrite <- (bifunctor_rightcomp E).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp U3 (_ · f ⊗^{E}_{r} _)) (pr1 (monoidal_braiding_inverses E _ _))).
  rewrite (bifunctor_rightid E).
  rewrite id_right.
  rewrite (bifunctor_leftcomp E (L R1)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (f · _ · _)) (assoc' _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc' _ _ _)).
  rewrite (monoidal_associatorinvnatleftright E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  do 3 refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp U3 (_ · (f · _))) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc' _ _ _)).
  rewrite (monoidal_associatorinvnatright E).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_postcomp U3 (_ · (f · _))) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 (_ · f)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) (assoc' _ _ _)).
  rewrite <- (bifunctor_rightcomp E).
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite internal_postcomp_comp.
  rewrite assoc.
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (λ f, (f · _ · _) ⊗^{E}_{r} U1 · _ · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E U3))) _ _ _)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} U1 · _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} U1 · _ · _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · internal_postcomp _ f · _) ⊗^{E}_{r} U1 · _ · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} U1 · _ · _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} U1 · _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U1 · _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} U1 · _ · _) (internal_swap_arg_nat3 _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} U1 · _ · _) (assoc' _ _ _)).
  rewrite (bifunctor_rightcomp E U1).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  rewrite <- (hom_onmorphisms_is_postcomp U1).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _)).
  simpl.
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite <- (internal_postcomp_comp U3).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (id_right _)).
  do 2 rewrite <- internal_postcomp_id.
  rewrite <- (pr1 (monoidal_associatorisolaw E _ _ _)).
  rewrite (internal_postcomp_comp U1).
  refine (_ @ ! maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (internal_swap_arg_nat3 _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (curry_unit U3 U1 (K ((R1 ⊗_{ C} R2) ⊗_{ C} R3)))).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (curry_swap _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (mon_closed_adj_natural E _ _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, (_ · f · _) ⊗^{E}_{r} _ · _) (curry_nat3 _ _ _)).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  rewrite <- (internal_postcomp_comp U1).
  rewrite <- (internal_postcomp_comp U3).
  refine (_ @ maponpaths (λ f, (f · _) ⊗^{E}_{r} _ · _) (curry_unit U1 U3 (K ((R1 ⊗_{ C} R2) ⊗_{ C} R3)))).
  refine (_ @ maponpaths (λ f, f ⊗^{E}_{r} _ · _) (assoc _ _ _)).
  rewrite <- (internal_postcomp_comp U1).
  refine (_ @ maponpaths (λ f, (_ · internal_postcomp U1 f) ⊗^{E}_{r} _ · _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ maponpaths (λ f, (_ · f) ⊗^{E}_{r} _ · _) (hom_onmorphisms_is_postcomp _ _)).
  rewrite (bifunctor_rightcomp E U1).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  simpl.
  rewrite <- (internal_postcomp_comp U3).
  rewrite (bifunctor_rightcomp E U1).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _) · _) (hom_onmorphisms_is_postcomp _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  simpl.
  refine (_ @ ! maponpaths (λ f, f · _ · _) (triangle_id_left_ad (pr2 (pr2 E _)) _)).
  rewrite id_left.
  do 2 apply maponpaths.
  repeat rewrite assoc.
  refine (_ @ maponpaths (λ f, _ · _ ⊗^{E}_{l} f) (functor_comp K _ _)).
  do 4 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (bifunctor_leftcomp E).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite (monoidal_associatorinvnatleft E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (bifunctor_leftcomp E).
  refine (_ @ maponpaths (λ f, _ · _ ⊗^{E}_{l} f) (functor_comp K _ _)).
  rewrite (bifunctor_rightcomp E).
  do 4 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite (monoidal_associatorinvnatleft E).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  rewrite <- (bifunctor_leftcomp E).
  apply map_on_two_paths.
  etrans.
  Unshelve.
  4 : {
    apply (compose α^{E}_{_,_,_}).
    apply sym_mon_braiding.
  }
  refine (! maponpaths (λ f, f · _ · _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ id_left _).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr2 (monoidal_braiding_inverses E _ _)).
  repeat rewrite assoc'.
  apply maponpaths.
  repeat rewrite assoc.
  refine (_ @ ! maponpaths (λ f, f · _) (sym_mon_tensor_lassociator0 E _ _ _)).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_left E _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ id_right _).
  rewrite <- (pr1 (monoidal_associatorisolaw E _ _ _)).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! id_left _ @ _).
  refine (! maponpaths (λ f, f · _) (pr2 (monoidal_associatorisolaw E _ _ _)) @ _).
  repeat rewrite assoc'.
  apply maponpaths.
  repeat rewrite assoc.
  apply sym_mon_tensor_lassociator1. (* completes subgoal *)  
  repeat rewrite assoc'.
  apply maponpaths.
  repeat rewrite assoc.
  refine (sym_mon_tensor_lassociator E _ _ _ @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  do 2 apply (maponpaths (postcompose _)).
  refine (! id_right _ @ _).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr1 (monoidal_braiding_inverses E _ _)).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! id_right _ @ _).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr1 (monoidal_associatorisolaw E _ _ _)).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  do 2 rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (compose _) (sym_mon_hexagon_lassociator E _ _ _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering E).
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ id_left _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{E}_{r} _ · _) (pr1 (monoidal_braiding_inverses E _ _)) @ _).
  rewrite (bifunctor_rightid E).
  rewrite id_right.
  exact (pr2 (monoidal_associatorisolaw E _ _ _)).
  apply maponpaths.
  refine (maponpaths (λ f, compose (C:=E) f _) (! functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (_ @ id_right _).
  rewrite <- (pr1 (monoidal_associatorisolaw C _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (compose _) (sym_mon_hexagon_lassociator C R3 R1 R2)).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering C).
  rewrite (when_bifunctor_becomes_rightwhiskering C).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  rewrite assoc.
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_rightcomp C R2 _ _ _ _ _)).
  refine (_ @ ! maponpaths (λ f, f ⊗^{C}_{r} R2 · _) (pr1 (monoidal_braiding_inverses C R1 R3))).
  rewrite (bifunctor_rightid C).
  exact (! id_left _).
Qed.

Local Lemma associnvdata_lemma30 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} {U1 X1 U2 X2 U3 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧) :
   internal_lam
    (doublePullbackArrow (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))
       (pr11 (tensor_doublePullback pb k
                ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
                 pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
                 doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3')) ⊗_{E} U1)
       (doublePullbackPrL
          (tensor_doublePullback pb k
             ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
              pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
              doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3')) ⊗^{ E}_{r} U1
        · (internal_curry U1 U2 X3 ⊗^{ E}_{r} U1 · internal_eval U1 (internal_hom U2 X3)))
       (doublePullbackPrM
          (tensor_doublePullback pb k
             ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
              pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
              doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3')) ⊗^{ E}_{r} U1
        · (K ((R1 ⊗_{ pr211 C} R2) ⊗_{ C} R3) ⊗^{ E}_{l} l1
           · (sym_mon_braiding E (K ((R1 ⊗_{ pr211 C} R2) ⊗_{ C} R3)) (L R1) · (L R1 ⊗^{ E}_{l} # K αinv^{ C }_{ R1, R2, R3} · pr1 k R1 (R2 ⊗_{ C} R3)))))
       (doublePullbackPrR
          (tensor_doublePullback pb k
             ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
              pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
              doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3')) ⊗^{ E}_{r} U1
        · (internal_postcomp U3 (doublePullbackPrL (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ⊗^{ E}_{r} U1
           · (internal_swap_arg U3 X2 U1 ⊗^{ E}_{r} U1 · internal_eval U1 (internal_hom U3 X2)))) (associnvdata_lemma21 pb k l1 l1' l2 l2' l3 l3')
       (associnvdata_lemma22 pb k l1 l1' l2 l2' l3 l3'))
  · internal_postcomp U1 (doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))) =
  doublePullbackPrM
    (tensor_doublePullback pb k
       ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
        pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3'))
  · # K αinv^{ C }_{ R1, R2, R3}
  · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} (R2 ⊗_{ pr211 C} R3))) (L R1) · pr1 k R1 (R2 ⊗_{ pr211 C} R3))
     · internal_precomp l1 (K (R2 ⊗_{ pr211 C} R3))).
Proof.
  refine (assoc' _ _ _ @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (! maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (λ f, _ · internal_postcomp _ f) (doublePullbackArrow_PrM _ _ _ _ _ _ _ ) @ _).
  refine (maponpaths (compose _) (internal_postcomp_comp _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (hom_onmorphisms_is_postcomp _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  unfold internal_lam.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (mon_closed_adj_natural E _ _ _ l1)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (internal_postcomp_comp U1 _ _)).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E U1))) _ _ _)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (internal_postcomp_comp U1 _ _)).
  do 2 apply maponpaths.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  exact (monoidal_braiding_naturality_right E _ _ _ _).
Qed.


Local Lemma associnvdata_lemma31 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : C ⟶ E ^opp}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} {U1 X1 U2 X2 U3 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧) (l2 : E ⟦ U2, L R2 ⟧)
  (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧):
  doublePullbackPrM
    (tensor_doublePullback pb k
       ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
        pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3'))
  · # K αinv^{ C }_{ R1, R2, R3}
  · (compose (C:=E) (# K (sym_mon_braiding C (R2 ⊗_{ pr211 C} R3) R1))
       (internal_lam ((pr121 E) (K ((R2 ⊗_{ pr211 C} R3) ⊗_{ C} R1)) (L (R2 ⊗_{ pr211 C} R3)) · pr1 k (R2 ⊗_{ pr211 C} R3) R1)
        · internal_precomp (l2 ⊗^{ E} l3 · (fmonoidal_preservestensordata L) R2 R3) (K R1))) =
  doublePullbackPrR
    (tensor_doublePullback pb k
       ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),,
        pr11 (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')),,
        doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) ((U3,, l3),, X3,, l3'))
  · (internal_postcomp U3 (doublePullbackPrR (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))) · internal_uncurry U3 U2 X1
     · internal_precomp (sym_mon_braiding E U2 U3) X1) · internal_postcomp (U2 ⊗_{ E} U3) l1'.
Proof.
  set (dpb12 := tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')).
  set (dpb123 := tensor_doublePullback pb k ((U1 ⊗_{ E} U2,, l1 ⊗^{ E} l2 · (fmonoidal_preservestensordata L) R1 R2),, pr11 dpb12,, doublePullbackPrM dpb12)
                   ((U3,, l3),, X3,, l3')).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · f) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f · _)) (uncurry_nat3 U3 U2 l1')).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp U3 _ _)).
  refine (_ @ maponpaths (λ f, _ · (internal_postcomp U3 f · _)) (doublePullbackSqrRCommutes dpb12)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp U3 _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (doublePullbackSqrRCommutes dpb123)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  unfold internal_lam; simpl.
  rewrite internal_precomp_comp.
  rewrite (maponpaths (λ f, internal_postcomp U3 f) (assoc _ _ _)).
  rewrite (internal_postcomp_comp U3).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f · _ · _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · f) (uncurry_swap U2 U3 (K R1))).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f · _)) (internal_swap_arg_nat2 U3 (K R1) U2 _ l2)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _ · _)) (internal_swap_arg_nat1 (L R2) (K R1) U3 _ l3)).
  do 2 refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _)).
  rewrite <- (uncurry_nat12 (K R1) l2 l3).
  do 2 refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  repeat rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (uncurry_swap _ _ (K R1))).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f) · _ · _) (internal_postcomp_comp (L R3) _ _)).
  do 2 refine (_ @ maponpaths (λ f, _ · (_ · internal_postcomp (L R3) f) · _ · _) (assoc' _ _ _)).
  rewrite (internal_postcomp_comp (L R3)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · (internal_postcomp (L R3) f · _)) · _ · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (L R2)))) _ _ _)).
  rewrite (internal_postcomp_comp (L R3)).
  simpl.
  rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ maponpaths (λ f, _ · (_ · f) · _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _ · _) (assoc' _ _ _)).
  rewrite <- (internal_postcomp_comp (L R3)).
  refine (_ @ maponpaths (λ f, _ · (_ · internal_postcomp (L R3) f) · _ · _) (internal_postcomp_comp (L R2) _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (_ · f) · _) (uncurry_nat3 _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, _ · f · _) (uncurry_unit _ _ _)).
  refine (maponpaths (λ f, _ · f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (L (R2 ⊗_{ pr211 C} R3))))) _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _)).
  simpl.
  do 3 rewrite hom_onmorphisms_is_postcomp.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp (L (R2 ⊗_{ pr211 C} R3)) _ _) @ _).
  refine (! maponpaths (compose _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp ((L R3 ⊗_{ E} L R2)) _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp ((L R3 ⊗_{ E} L R2)) _ _)).
  refine (_ @ maponpaths (compose _) (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (mon_closed_adj_natural E _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! internal_postcomp_comp ((L R2 ⊗_{ E} L R3)) _ _ @ _ @ internal_postcomp_comp ((L R2 ⊗_{ E} L R3)) _ _).
  apply maponpaths.
  repeat refine (assoc _ _ _ @ _).
  refine (! maponpaths (compose _) (id_left _) @ _).
  rewrite <- (bifunctor_leftid E).
  refine (! maponpaths (λ f, _ · (_ ⊗^{E}_{l} f · _)) (functor_id K _) @ _).
  rewrite <- (bifunctor_rightid C).
  refine (! maponpaths (λ f, _ · ((_ ⊗^{E}_{l} # K (f ⊗^{C}_{r} _)) · _)) (pr1 (monoidal_braiding_inverses C R2 R3)) @ _).
  unfold monoidal_braiding_data_inv.
  rewrite (bifunctor_rightcomp C R1).
  rewrite (functor_comp K).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_leftcomp E (L (R2 ⊗_{ pr211 C} R3)) _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  generalize (pr122 k R1 _ _ (sym_mon_braiding C R2 R3)); simpl;
    repeat rewrite id_right; repeat rewrite id_left; unfold monoidal_cat_tensor_pt;
    intros keq1.
  refine (maponpaths (compose _) keq1 @ _); clear keq1.
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · f · _ · _) (bifunctor_rightcomp E (L (R2 ⊗_{ pr211 C} R3)) _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · f · _) (triangle_id_left_ad (pr2 (pr2 E (L (R2 ⊗_{C} R3)))) _) @ _).
  rewrite (id_right _).
  do 2 refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _ · _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _ · _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · f · _ · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (maponpaths (λ f, f · _ · _) (assoc _ _ _) @ _).
  do 2 refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  unfold functoronmorphisms2.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (fsym_respects_braiding L R2 R3) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f) (assoc' _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  assert ((fmonoidal_preservestensordata L) R3 R2 ⊗^{ E}_{r} K ((R3 ⊗_{ C} R2) ⊗_{ C} R1)
        · pr1 k (R3 ⊗_{ C} R2) R1 =
            ((L R3 ⊗_{ E} L R2) ⊗^{E}_{l} # K αinv^{ C }_{ R3, R2, R1}) · (sym_mon_braiding E (L R3) (L R2) ⊗^{ E}_{r} K (R3 ⊗_{ C} (R2 ⊗_{ C} R1)) · α^{ E }_{ L R2, L R3, K (R3 ⊗_{ C} (R2 ⊗_{ C} R1))} · L R2 ⊗^{ E}_{l} pr1 k R3 (R2 ⊗_{ C} R1) · pr1 k R2 R1)) as keq.
  generalize (pr2 (pr222 k) R3 R2 R1); simpl; intros keq.
  unfold postcompose in keq.
  refine (! id_left _ @ _).
  rewrite <- (bifunctor_leftid E).
  refine (! maponpaths (λ f, _ ⊗^{E}_{l} f · _) (functor_id K _) @ _).
  refine (! maponpaths (λ f, compose (C:=E) (_ ⊗^{E}_{l} (# K f)) _) (pr1 (monoidal_associatorisolaw C _ _ _)) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f · _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) f _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  exact (assoc _ _ _ @ keq).
  refine (maponpaths (λ f, _ · (_ · (_ · f))) keq @ _); clear keq.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · (_ · (_ · (f · _)))) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · (_ · f))) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · (f · _))) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (pr1 (monoidal_braiding_inverses E (L R2) (L R3))) @ _).
  rewrite (bifunctor_rightid E).
  rewrite (id_left _).
  repeat refine (assoc _ _ _ @ _).
  repeat refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · ((_ · f) ⊗^{E}_{r} _ · _)) (pr12 k R3 _ _ ((pr121 C) R2 R1))).
  unfold monoidal_cat_tensor_pt; simpl.
  refine (_ @ maponpaths (λ f, _ · (f ⊗^{E}_{r} _ · _)) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp E _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (monoidal_braiding_naturality_right E _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, f ⊗^{E}_{r} _ · _ · _ · _ · _) (functor_comp K _ _) @ _).
  repeat refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · (f · _))) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (bifunctor_rightcomp E _ _ _ _ _ _) @ _).
  refine (_ @ ! maponpaths (λ f, _ ·_ · f ⊗^{E}_{r} (L R2) · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  rewrite (bifunctor_rightcomp E (L R2)).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _ · _) (monoidal_associatorinvnatright E _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _ · _ · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, f · _ · _ · _ · _) (bifunctor_rightcomp E _ _ _ _ _ _)).
  do 3 refine (_ @ assoc _ _ _).
  apply map_on_two_paths.
  apply maponpaths.
  refine (! maponpaths (compose (C:=E) _) (functor_comp K _ _) @ _).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  refine (_ @ monoidal_braiding_naturality_left C _ _ _ _).
  rewrite <- (when_bifunctor_becomes_rightwhiskering C).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (compose _) (sym_mon_tensor_lassociator' C _ _ _ @ _) @ _).
  rewrite 3 assoc'.
  unfold monoidal_cat_tensor_mor; now rewrite (when_bifunctor_becomes_leftwhiskering C).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (pr2 (monoidal_associatorisolaw C _ _ _)) @ _).
  apply id_left.
  rewrite assoc'.
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  apply (sym_mon_hexagon_rassociator C).
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_leftwhiskering C), (when_bifunctor_becomes_rightwhiskering C).
  rewrite 2 assoc.
  refine (_ @ id_left _).
  apply (maponpaths (postcompose _)).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr1 (monoidal_associatorisolaw C _ _ _)).
  apply (maponpaths (postcompose _)).
  refine (_ @ id_right _).
  rewrite assoc'.
  apply maponpaths.
  refine (! bifunctor_leftcomp C _ _ _ _ _ _ @ _ @ bifunctor_leftid C _ _).
  apply maponpaths.
  apply (monoidal_braiding_inverses C).
  rewrite 2 assoc.
  rewrite <- (when_bifunctor_becomes_leftwhiskering E), <- (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ maponpaths (λ f, f · _) (sym_mon_hexagon_rassociator E _ _ _)).
  rewrite 2 assoc'.
  refine (_ @ maponpaths (compose _) _).
  2 : {
    rewrite assoc.
    apply (sym_mon_braiding_tensor_associator E).
  }
  refine (! id_left _ @ _).
  repeat rewrite assoc.
  repeat apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (monoidal_associatorisolaw E).  
Qed.

Definition double_glued_associnv_data_comp2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) :
 double_glued_mor_comp2 L K (R1 ⊗_{ pr211 C} (R2 ⊗_{ pr211 C} R3)) ((R1 ⊗_{ pr211 C} R2) ⊗_{ pr211 C} R3)
        (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R1 (R2 ⊗_{ pr211 C} R3) dr1
           (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R2 R3 dr2 dr3))
        (disp_bifunctor_on_objects (double_glued_tensor pb L K k) (R1 ⊗_{ pr211 C} R2) R3
           (disp_bifunctor_on_objects (double_glued_tensor pb L K k) R1 R2 dr1 dr2) dr3).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct dr3 as ((U3, l3), (X3, l3')).
  unfold double_glued_mor_comp2, disp_bifunctor_on_objects; simpl.
  use doublePullbackArrow.
  apply internal_lam.
  use doublePullbackArrow.
  apply (compose (doublePullbackPrL _ ⊗^{E}_{r} U1)).
  apply (compose (internal_curry U1 U2 X3 ⊗^{E}_{r} U1)).
  exact (internal_eval _ _).
  apply (compose (doublePullbackPrM _ ⊗^{E}_{r} U1)).
  apply (compose (_ ⊗^{E}_{l} l1)).
  apply (compose (sym_mon_braiding E _ _)).
  apply (compose (_ ⊗^{E}_{l} # K αinv^{C}_{R1, R2, R3})).
  exact (pr1 k R1 _).
  apply (compose (doublePullbackPrR _ ⊗^{E}_{r} U1)).
  apply (compose (internal_postcomp U3 (doublePullbackPrL _) ⊗^{E}_{r} U1)).
  apply (compose (internal_swap_arg _ _ _ ⊗^{E}_{r} U1)).
  exact (internal_eval _ _).
  exact (associnvdata_lemma21 pb k l1 l1' l2 l2' l3 l3').
  exact (associnvdata_lemma22 pb k l1 l1' l2 l2' l3 l3').
  apply (compose (doublePullbackPrM _)).
  exact (# K (αinv_{C} R1 R2 R3)).
  apply (compose (doublePullbackPrR _)).
  apply (postcompose (internal_precomp (sym_mon_braiding E U2 U3) X1)).
  apply (postcompose (internal_uncurry U3 U2 X1)).
  apply (internal_postcomp U3).
  exact (doublePullbackPrR _).
  exact (associnvdata_lemma30 pb k l1 l1' l2 l2' l3 l3').
  exact (associnvdata_lemma31 pb k l1 l1' l2 l2' l3 l3').
Defined.

Lemma double_glued_associnv_data_eq2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : sym_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : ob C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) :
  double_glued_mor_eq2 L K _ _ _ _ (αinv^{C}_{R1, R2, R3}) (double_glued_associnv_data_comp2 pb k dr1 dr2 dr3).
Proof.
  unfold double_glued_mor_eq2; simpl.
  refine (! doublePullbackArrow_PrM _ _ _ _ _ _ _).
Qed.

Definition double_glued_associatorinv_data {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : sym_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) : disp_associatorinv_data (double_glued_tensor pb L K k).
Proof.
  intros R1 R2 R3 dr1 dr2 dr3.
  split.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  destruct dr3 as ((U3, l3), (X3, l3')).
  exists (αinv_{E} U1 U2 U3).
  exact (associnvdata_lemma1 l1 l1' l2 l2' l3 l3').
  (* component 2 :*)
  exists (double_glued_associnv_data_comp2 pb k dr1 dr2 dr3).
  exact (double_glued_associnv_data_eq2 pb k dr1 dr2 dr3).
Defined.

