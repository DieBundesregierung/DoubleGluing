(************************************

This files contains some preliminary definitions and lemmata, namely:
- definition of dinaturality
- definition of a constant bifunctor
- a bundled approach to symmetric monoidal functors (will be partially removed because it overlaps with existing code of the UniMath library)
- many results about internal structure of symmetric monoidal categories (some described in section 3.2 of the paper)

************************************)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

(* dinatural transformations *)
Section dinaturals.
  Context {C D : category}.
  
  Definition is_dinatural {F G : bifunctor (C^opp) C D} (α : ∏ c : C, D⟦ (pr11 F) c c, (pr11 G) c c⟧) : hProp.
  Proof.
    refine (∀ c c' : C, ∀ f : C⟦c, c'⟧, _).
    use make_hProp.
    exact ((leftwhiskering_on_morphisms G c c c' f) ∘ (α c) ∘ (rightwhiskering_on_morphisms F c c' c f) =
             (rightwhiskering_on_morphisms G c' c' c f) ∘ (α c') ∘ (leftwhiskering_on_morphisms F c' c c' f)).
    exact (pr2 D _ _ _ _).
  Defined.

  Definition dinat_trans (F G : bifunctor (C^opp) C D) : UU :=
    ∑ (α : ∏ c : C, D⟦(pr11 F) c c, (pr11 G) c c⟧), is_dinatural α.

End dinaturals.

(* constant bifunctor *)
Definition constant_bifunctor {E : category} (C D : category) (a : ob E) : bifunctor C D E.
Proof.
  use tpair.
  exists (λ _ _, a).
  split.
  exact (λ _ _ _ _, identity a).
  exact (λ _ _ _ _, identity a).
  split5.
  exact (λ _ _, idpath _).
  exact (λ _ _, idpath _).
  exact (λ _ _ _ _ _ _, ! id_left _).
  exact (λ _ _ _ _ _ _, ! id_left _).
  exact (λ _ _ _ _ _ _, idpath _).
Defined.


(* bundled approach to symmetric monoidal functors  *)
(* will be partially removed because it overlaps with existing code of the UniMath library *)
Definition sym_monoidal_functor (C D : sym_monoidal_cat) : UU :=
  ∑ (F : lax_monoidal_functor C D), is_symmetric_monoidal_functor C D F.

Definition fsym_respects_braiding {C D : sym_monoidal_cat} (F : sym_monoidal_functor C D) := pr2 F.

Definition fmonoidal_from_fsym {C D : sym_monoidal_cat} (F : sym_monoidal_functor C D) : lax_monoidal_functor C D := pr1 F.
Coercion fmonoidal_from_fsym : sym_monoidal_functor >-> lax_monoidal_functor.


Section sym_mon_closed_results.

  Context  {V : sym_mon_closed_cat}.
  
Lemma hom_onmorphisms_is_postcomp {Y Z : ob V} (X : ob V) (f : V⟦Y, Z⟧) : # (pr1 (pr2 V X)) f = internal_postcomp X f.
Proof.
  unfold internal_postcomp, internal_lam.
  rewrite functor_comp.
  rewrite assoc.
  refine (! id_left _ @ _).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (triangle_id_right_ad (pr2 (pr2 V X))).
Qed.

Lemma mon_closed_adj_natural' (A : ob V) {X Y : V} (f : V ⟦ X, Y ⟧):
  unit_from_are_adjoints (pr2 (pr2 V X)) A · # (pr1 (pr2 V X)) (A ⊗^{ V}_{l} f) =
  unit_from_are_adjoints (pr2 (pr2 V Y)) A · internal_precomp f (A ⊗_{ pr1 V} Y).
Proof.
  refine (_ @ ! internal_lam_natural _ _).
  apply (maponpaths internal_lam).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering V), (when_bifunctor_becomes_leftwhiskering V).
  rewrite assoc.
  refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers V _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (! id_right _ @ _).
  apply (maponpaths (compose _)).
  apply pathsinv0.
  apply (triangle_id_left_ad (pr2 (pr2 V Y))).
Qed.

Lemma mon_closed_adj_natural (A : ob V) {X Y : V} (f : V ⟦ X, Y ⟧) :
  unit_from_are_adjoints (pr2 (pr2 V X)) A · internal_postcomp X (A ⊗^{ V}_{l} f) =
  unit_from_are_adjoints (pr2 (pr2 V Y)) A · internal_precomp f (A ⊗_{ pr1 V} Y).
Proof.
  rewrite <- hom_onmorphisms_is_postcomp.
  apply mon_closed_adj_natural'.
Qed.
  
Lemma internal_eval_nat (X : V) {Z Y : ob V} (f : V ⟦Y, Z⟧) :
  internal_eval X Y · f = # (pr1 (pr2 V X)) f ⊗^{ V}_{r} X · internal_eval X Z.
Proof.
  apply pathsinv0.
  apply (counit_from_are_adjoints (pr2 (pr2 V X))).
Qed.

Lemma internal_lam_tensor_eval {X Y Z: ob V} (f : V⟦X ⊗_{V} Y, Z⟧) :
  internal_lam f ⊗^{V}_{r} Y · internal_eval _ _ = f.
Proof.
  refine (_ @ internal_beta f).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (when_bifunctor_becomes_rightwhiskering V).
Qed.

Lemma mon_closed_adj_natural_co (A : V) {X Y : V} (f : V ⟦ X, Y ⟧) :
  internal_precomp f A ⊗^{ V}_{r} X · counit_from_are_adjoints (pr2 (pr2 V X)) A =
  pr1 (pr2 V Y) A ⊗^{ V}_{l} f · counit_from_are_adjoints (pr2 (pr2 V Y)) A.
Proof.
  refine (internal_lam_tensor_eval _ @ _).
  unfold monoidal_cat_tensor_mor.
  now rewrite (when_bifunctor_becomes_leftwhiskering V).
Qed.

Definition lolli_bifunctor_data : bifunctor_data (V^opp) V V.
Proof.
  exists (λ x, pr11 (pr2 V x)).
  split.
  intros x y1 y2 g12.
  exact (internal_postcomp _ g12).
  intros y x1 x2 f12.
  exact (internal_precomp f12 _).
Defined.

Lemma lolli_functoronmorphisms_eq : functoronmorphisms_are_equal (lolli_bifunctor_data).
Proof.
  intros x1 x2 y1 y2 f g.
  exact (! internal_pre_post_comp_as_pre_post_comp f g @ internal_pre_post_comp_as_post_pre_comp f g).
Qed.

Definition lolli_bifunctor: bifunctor (V^opp) V V.
Proof.
  exists lolli_bifunctor_data.
  exists internal_postcomp_id.
  exists (λ x y, internal_precomp_id y x).
  exists internal_postcomp_comp.
  split.
  intros w x y z f1 f2.
  exact (internal_precomp_comp f2 f1 w).
  exact lolli_functoronmorphisms_eq.
Defined.

Lemma internal_lam_precomp {X Y1 Y2 Z : ob V} (f : V⟦X ⊗_{V} Y1, Z⟧) (g : V⟦Y2, Y1⟧) :
  internal_lam f · internal_precomp g Z = internal_lam (X ⊗^{V}_{l} g · f).
Proof.
  unfold internal_lam.
  refine (assoc' _ _ _ @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp Y2 _ _ @ _).
  apply pathsinv0.
  apply hom_onmorphisms_is_postcomp.
Qed.

Lemma internal_lam_postcomp {X Y Z1 Z2 : ob V} (f : V⟦X ⊗_{V} Y, Z1⟧) (g : V⟦Z1, Z2⟧) :
  internal_lam f · internal_postcomp Y g = internal_lam (f · g).
Proof.
  unfold internal_lam.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  exact (! functor_comp (pr1 (pr2 V Y)) _ _).
Qed.

Lemma rightunitors_eval_expand1 (X : ob V) :
  ruinv_{V} (internal_hom (I_{V}) X) · counit_from_are_adjoints (pr2 ((pr2 V) (I_{V}))) X · unit_from_are_adjoints (pr2 ((pr2 V) (I_{V}))) X · # (pr1 ((pr2 V) (I_{V}))) (ru_{V} X) = identity (internal_hom (I_{V}) X).
Proof.
  refine (maponpaths (postcompose _) (assoc' _ _ _) @ _).
  set (unitnateq := pr2 (pr112 ((pr2 V) (I_{V}))) _ _ (counit_from_are_adjoints (pr2 ((pr2 V) (I_{V}))) X)).
  refine (maponpaths (λ f, _ · f · _) unitnateq @ _); clear unitnateq.
  rewrite assoc.
  rewrite assoc'.
  set (unitnateq := pr2 (pr112 ((pr2 V) (I_{V}))) _ _ (ruinv_{V} (internal_hom (I_{V}) X))).
  refine (maponpaths (postcompose _) unitnateq @ _); clear unitnateq.
  unfold postcompose.
  unfold internal_hom.
  rewrite <- (triangle_id_right_ad (pr2 (pr2 V I_{ V}))).
  rewrite assoc'.
  apply maponpaths.
  simpl.
  repeat rewrite <- functor_comp.
  apply maponpaths.
  refine (_ @ pr1 (pr121 (pr111 V)) _ _ _).
  set (bif := monoidal_tensor_is_bifunctor V).
  rewrite <- (pr12 bif).
  refine (_ @ maponpaths (λ f, f ⊗^{ V}_{r} I_{ V} · _) (pr2 ((monoidal_rightunitorisolaw V) _))).
  rewrite (pr1 (pr222 bif)).
  refine (_ @ assoc _ _ _ ).
  apply (maponpaths (compose _)).
  refine (monoidal_rightunitornat V _ _ (counit_from_are_adjoints (pr2 (pr2 V I_{ V})) X) @ _).
  apply (maponpaths (postcompose _)).
  show_id_type.
  apply pathsinv0.
  refine (! id_right _ @ _ @ id_right _).
  rewrite <- (pr1 (monoidal_rightunitorisolaw V _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  exact (monoidal_rightunitornat V _ _ (ru_{V} _)).
Qed.

Lemma rightunitors_eval_expand2 (X : ob V) :
  identity X =
    pr1 (unit_from_are_adjoints (pr2 (pr2 V I_{ V}))) X · internal_postcomp I_{ V} ru^{ V }_{ X} · ruinv^{ V }_{ pr1 (pr2 V I_{ V}) X} · pr1 (counit_from_are_adjoints (pr2 (pr2 V I_{ V}))) X.
Proof.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (monoidal_rightunitorinvnat V _ _ (internal_postcomp I_{ V} ru^{ V }_{ X}))).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite assoc'.
  refine (_ @ maponpaths (λ f, f · _) (monoidal_rightunitorinvnat V _ _ (pr1 (unit_from_are_adjoints (pr2 (pr2 V I_{ V}))) X))).
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 V I_{ V}))) _ _ (ru^{V}_{X}))).
  simpl.
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (triangle_id_left_ad (pr2 (pr2 V I_{ V})) _)).
  rewrite id_left.
  exact (! pr2 (monoidal_rightunitorisolaw V X)).
Qed.

Lemma internal_swap_arg_nat1 (y z : ob V) : ∏ (x1 x2 : V) (f : V ⟦ x1, x2 ⟧),
    internal_swap_arg x2 z y · internal_postcomp y (internal_precomp f z) = internal_precomp f (internal_hom y z) · internal_swap_arg x1 z y .
Proof.
  intros x1 x2 f.
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor;
    rewrite 5 (when_bifunctor_becomes_rightwhiskering V).
  rewrite 2 (when_bifunctor_becomes_leftwhiskering V).
  refine (maponpaths (λ f, f ⊗^{V}_{r} _ · _) _ @ _).
  apply internal_lam_tensor_eval.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers V _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_tensor_eval _) @ _).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt;
    rewrite (when_bifunctor_becomes_rightwhiskering V), (when_bifunctor_becomes_leftwhiskering V).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply pathsinv0.
  apply (monoidal_associatornatleft V).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp V _ _ _ _ _ _ @ _) @ _).
  refine (_ @ bifunctor_leftcomp V _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left V).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  apply (monoidal_associatorinvnatleftright V).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) _).
      2 : {
        apply (monoidal_associatornatright V).
      }
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      apply maponpaths.
      apply pathsinv0.
      apply (bifunctor_equalwhiskers V).
    }
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_associatorinvnatright V).
  }
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! bifunctor_rightcomp V _ _ _ _ _ _ @ _
            @ bifunctor_rightcomp V _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (mon_closed_adj_natural_co _ f).
Qed.

Lemma internal_swap_arg_nat2 (x z : ob V) : ∏ (y1 y2 : V) (f : V ⟦ y1, y2 ⟧),
    internal_swap_arg x z y2 · internal_precomp f (internal_hom x z) = internal_postcomp x (internal_precomp f z) · internal_swap_arg x z y1.
Proof.
  intros y1 y2 f.
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering V).
  rewrite 2 (when_bifunctor_becomes_leftwhiskering V).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers V _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_tensor_eval _) @ _).
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 4 (when_bifunctor_becomes_rightwhiskering V).
  rewrite (when_bifunctor_becomes_leftwhiskering V).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) _ @ _).
  apply pathsinv0.
  apply (monoidal_associatornatleftright V).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp V _ _ _ _ _ _ @ _) @ _).
  refine (_ @ bifunctor_leftcomp V _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right V).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _ @ _).
  apply (monoidal_associatorinvnatleft V).
  apply assoc.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _).
  apply pathsinv0.
  apply (bifunctor_equalwhiskers V).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (monoidal_associatornatright V _ _ _ _ _)).
        refine (assoc' _ _ _ @ _ @ assoc _ _ _).
        apply maponpaths.
        apply pathsinv0.
        apply (bifunctor_equalwhiskers V).        
      }
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      apply maponpaths.
      apply pathsinv0.
      apply (monoidal_associatorinvnatright V).
    }
    refine (_ @ assoc _ _ _).
    refine (maponpaths (compose _) (_ @ bifunctor_rightcomp V _ _ _ _ _ _)).
    refine (_ @ maponpaths (λ f, f ⊗^{V}_{r} _) (! internal_lam_tensor_eval _)).
    apply pathsinv0.
    apply (bifunctor_rightcomp V).
  }
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply mon_closed_adj_natural_co.
Qed.

Lemma internal_swap_arg_nat3 (x y : ob V) : ∏ (z1 z2 : V) (f : V ⟦ z1, z2 ⟧),
    internal_swap_arg x z1 y · internal_postcomp y (internal_postcomp x f) = internal_postcomp x (internal_postcomp y f) · internal_swap_arg x z2 y .
Proof.
  intros z1 z2 f.
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering V).
  rewrite (when_bifunctor_becomes_leftwhiskering V).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_tensor_eval _) @ _).
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 4 (when_bifunctor_becomes_rightwhiskering V).
  rewrite (when_bifunctor_becomes_leftwhiskering V).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_lam_tensor_eval _) @ _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (monoidal_associatornatright V _ _ _ _ _)).
        refine (assoc' _ _ _ @ _ @ assoc _ _ _).
        apply maponpaths.
        apply pathsinv0.
        apply (bifunctor_equalwhiskers V).        
      }
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      apply maponpaths.
      apply pathsinv0.
      apply (monoidal_associatorinvnatright V).
    }
    refine (_ @ assoc _ _ _).
    refine (maponpaths (compose _) (_ @ bifunctor_rightcomp V _ _ _ _ _ _)).
    refine (_ @ maponpaths (λ f, f ⊗^{V}_{r} _) (! internal_lam_tensor_eval _)).
    apply pathsinv0.
    apply (bifunctor_rightcomp V).
  }
  refine (assoc' _ _ _ @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (internal_eval_natural _ _ @ _).
  unfold monoidal_cat_tensor_mor.
  now rewrite (when_bifunctor_becomes_rightwhiskering V).
Qed.
  
Lemma curry_swap (X Y Z : ob V) :
  internal_precomp (sym_mon_braiding V X Y) Z · internal_curry X Y Z = internal_curry Y X Z · internal_swap_arg Y Z X.
Proof.
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 5 (when_bifunctor_becomes_rightwhiskering V).
  rewrite (when_bifunctor_becomes_leftwhiskering V).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (λ f, f · _) (monoidal_associatornatright V _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_tensor_eval _) @ _).
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_leftwhiskering V).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) _).
  2 : {
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ f, f · _) _).
      2 : {
        refine (_ @ assoc' _ _ _).
        refine (_ @ maponpaths (λ f, f · _) _).
        2 : {
          apply (monoidal_associatornatright V).
        }
        refine (assoc' _ _ _ @ _ @ assoc _ _ _).
        apply maponpaths.
        apply pathsinv0.
        apply (bifunctor_equalwhiskers V).
      }
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      apply maponpaths.
      apply pathsinv0.
      apply (monoidal_associatorinvnatright V).      
    }
    refine (_ @ assoc _ _ _).
    refine (maponpaths (compose _) (_ @ bifunctor_rightcomp V _ _ _ _ _ _)).
    exact (maponpaths (λ f, f ⊗^{V}_{r} X) (! internal_lam_tensor_eval _)).
  }
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (! internal_lam_tensor_eval _)).
  refine (! id_left _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (monoidal_associatorisolaw V).
Qed.
    
Lemma curry_nat3 (X Y : ob V) {Z1 Z2 : ob V} (f : V⟦Z1, Z2⟧) :
  (internal_postcomp (X ⊗_{ V} Y) f) · internal_curry X Y Z2 = internal_curry X Y Z1 · internal_postcomp X (internal_postcomp Y f).
Proof.
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering V).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! internal_lam_tensor_eval _)).
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_postcomp _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering V).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (! monoidal_associatornatright V _ _ _ _ _) @ _).
  rewrite 2 assoc'.
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  apply pathsinv0.
  apply internal_eval_nat.
Qed.

Lemma curry_nat12 {X1 X2 Y1 Y2 : ob V} (Z : ob V) (f : V⟦X1, X2⟧) (g : V⟦Y1, Y2⟧) :
  (internal_precomp (f ⊗^{ V} g) Z) · internal_curry X1 Y1 Z =
    internal_curry X2 Y2 Z · (internal_postcomp X2 (internal_precomp g Z) · internal_precomp f _).
Proof.
  rewrite assoc.
  refine (_ @ maponpaths (λ f, f · _) (! internal_lam_natural _ _)).
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_precomp _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering V).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (! internal_lam_tensor_eval _)).
    apply pathsinv0.
    apply internal_lam_precomp.
  }
  refine (internal_lam_natural _ _ @ _ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold internal_precomp, monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering V).
  rewrite (when_bifunctor_becomes_leftwhiskering V).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_associatornatright V _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (_ @ maponpaths (compose _) (assoc _ _ _ @ _ @ assoc' _ _ _)).
  2 : {
    apply (maponpaths (λ f, f · _)).
    apply (monoidal_associatornatleft V).
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _)  (monoidal_associatornatleftright V _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (internal_lam_tensor_eval _ @ _).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  apply (bifunctor_leftcomp V).
Qed.

Lemma curry_unit (X Y Z : ob V) :
  unit_from_are_adjoints (pr2 (pr2 V X)) Z · internal_postcomp X (unit_from_are_adjoints (pr2 (pr2 V Y)) (Z ⊗_{V} X)) ·
    internal_postcomp X (internal_postcomp Y (α^{V}_{Z, X, Y})) =
    unit_from_are_adjoints (pr2 (pr2 V (X ⊗_{V} Y))) Z · internal_curry X Y _.
Proof.
  unfold internal_curry, internal_lam; simpl.
  refine (_ @ assoc' _ _ _).
  generalize (pr2 (unit_from_are_adjoints (pr2 (pr2 V X))) _ _ (unit_from_are_adjoints (pr2 (pr2 V (X ⊗_{ V} Y))) Z)); simpl; intros eq.
  refine (_ @ ! maponpaths (λ f, f · _) eq); clear eq.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  repeat rewrite hom_onmorphisms_is_postcomp.
  refine (! internal_postcomp_comp X _ _ @ _ @ internal_postcomp_comp X _ _).
  apply maponpaths.
  generalize (pr2 (unit_from_are_adjoints (pr2 (pr2 V Y))) _ _ (unit_from_are_adjoints (pr2 (pr2 V (X ⊗_{ V} Y))) Z ⊗^{V}_{r} X)); simpl; intros eq.
  rewrite assoc.
  refine (_ @ ! maponpaths (λ f, f · _) eq); clear eq.
  rewrite hom_onmorphisms_is_postcomp.
  rewrite assoc'.
  apply maponpaths.
  refine (_ @ internal_postcomp_comp Y _ _).
  apply maponpaths.
  rewrite assoc.
  generalize (monoidal_associatornatright V _ _ X Y (unit_from_are_adjoints (pr2 (pr2 V (X ⊗_{ V} Y))) Z)); simpl; intros eq.
  refine (_ @ maponpaths (λ f, f · _) eq); clear eq.
  rewrite assoc'.
  generalize (triangle_id_left_ad (pr2 (pr2 V (X ⊗_{ V} Y))) Z); simpl; intros treq.
  refine (_ @ ! maponpaths (compose _) treq).
  exact (! id_right _).
Qed.
                                                
Lemma uncurry_swap (X Y Z : ob V) :
  internal_uncurry Y X Z · internal_precomp (sym_mon_braiding V X Y) Z = internal_swap_arg Y Z X · internal_uncurry X Y Z.
Proof.
  refine (_ @ id_left _).
  rewrite <- internal_uncurry_curry.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! id_right _ @ _).
  rewrite <- internal_curry_uncurry.
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  apply curry_swap.
Qed.
    
Lemma uncurry_nat3 (X Y : ob V) {Z1 Z2 : ob V} (f : V⟦Z1, Z2⟧) :
  internal_uncurry X Y Z1 · (internal_postcomp (X ⊗_{ V} Y) f) = internal_postcomp X (internal_postcomp Y f) · internal_uncurry X Y Z2.
Proof.
  refine (_ @ id_left _).
  rewrite <- internal_uncurry_curry.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! id_right _ @ _).
  refine (maponpaths (compose _) (! internal_curry_uncurry _ _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  apply curry_nat3.
Qed.

Lemma uncurry_nat12 {X1 X2 Y1 Y2 : ob V} (Z : ob V) (f : V⟦X1, X2⟧) (g : V⟦Y1, Y2⟧) :
  internal_uncurry X2 Y2 Z · (internal_precomp (f ⊗^{ V} g) Z) =
    (internal_postcomp X2 (internal_precomp g Z) · internal_precomp f _) · internal_uncurry X1 Y1 Z.
Proof.
  refine (_ @ id_left _).
  rewrite <- internal_uncurry_curry.
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! id_right _ @ _).
  refine (maponpaths (compose _) (! internal_curry_uncurry _ _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  apply curry_nat12.
Qed.

Lemma uncurry_unit (X Y Z : ob V) :
  unit_from_are_adjoints (pr2 (pr2 V X)) Z · internal_postcomp X (unit_from_are_adjoints (pr2 (pr2 V Y)) (Z ⊗_{V} X)) · internal_uncurry X Y _ =
    unit_from_are_adjoints (pr2 (pr2 V (X ⊗_{V} Y))) Z · (internal_postcomp (X ⊗_{V} Y) (αinv^{V}_{Z, X, Y})).
Proof.
  refine (_ @ id_right _).
  refine (_ @ maponpaths (compose _) (internal_curry_uncurry _ _ _)).
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (! curry_nat3 _ _ _)).
  rewrite assoc.
  refine (_ @ maponpaths (λ f, f · _) (curry_unit _ _ _)).
  rewrite assoc'.
  refine (! id_right _ @ _).
  apply maponpaths.
  refine (! internal_postcomp_id _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  refine (! internal_postcomp_id _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorisolaw V).
Qed.


Lemma internal_swap_arg_involution (X Y Z : ob V) : internal_swap_arg X Y Z · internal_swap_arg _ _ _ = identity _.
Proof.
  unfold internal_swap_arg.
  refine (internal_lam_natural _ _ @ _).
  rewrite internal_lam_natural.
  unfold internal_swap_arg, monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_leftwhiskering V).
  rewrite 4 (when_bifunctor_becomes_rightwhiskering V).
  refine (_ @ triangle_id_right_ad (pr2 (pr2 V _)) _).
  apply (maponpaths (compose _)), maponpaths.
  do 3 refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, internal_lam (f · _)) (monoidal_associatornatright V _ _ _ _ _) @ _).
  refine (maponpaths internal_lam (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f · _))) (bifunctor_equalwhiskers V _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f · _))) (monoidal_associatorinvnatright V _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, internal_lam (_ · (f · _))) (bifunctor_rightcomp V _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · ((f · _) ⊗^{V}_{r} _ · _))) (bifunctor_rightcomp V _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f ⊗^{V}_{r} _ · _))) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, internal_lam (_ · ((_ · f) ⊗^{V}_{r} _ · _))) (internal_eval_nat _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f ⊗^{V}_{r} _ · _))) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · ((f · _) ⊗^{V}_{r} _ · _))) (triangle_id_left_ad (pr2 (pr2 V _)) _) @ _).
  rewrite id_left.
  refine (maponpaths (λ f, internal_lam (_ · (f · _))) (bifunctor_rightcomp V _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, internal_lam (_ · (_ · f))) (internal_eval_nat _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f · _))) (triangle_id_left_ad (pr2 (pr2 V _)) _) @ _).
  rewrite id_left.
  do 3 refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _)) (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f · _)) (pr2 (monoidal_associatorisolaw V _ _ _)) @ _).
  rewrite id_right.
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _)) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, internal_lam (_ · f · _)) (bifunctor_leftcomp V _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · _ ⊗^{V}_{l} f · _)) (pr2 (monoidal_braiding_inverses V _ _)) @ _).
  rewrite (bifunctor_leftid V), id_right.
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _)) (pr1 (monoidal_associatorisolaw V _ _ _)) @ _).
  rewrite id_left.
  rewrite <- (when_bifunctor_becomes_rightwhiskering V).
  refine (! internal_lam_natural _ _ @ _).
  refine (_ @ id_right _).
  apply maponpaths.
  unfold internal_lam.
  exact (triangle_id_right_ad (pr2 (pr2 V _)) _).
Qed.

Lemma curry_counit (W X Z : ob V) :
  (internal_curry W X Z ⊗^{ V}_{r} W · internal_eval W (internal_hom X Z)) ⊗^{ V}_{r} X
  · internal_eval X Z = α^{ V }_{ internal_hom (W ⊗_{ V} X) Z, W, X} · internal_eval (W ⊗_{ V} X) Z.
Proof.
  unfold internal_curry.
  refine (maponpaths (λ f, f ⊗^{ V}_{r} X · _) (internal_lam_tensor_eval _) @ _).
  apply internal_lam_tensor_eval.
Qed.

Lemma uncurry_counit (X Y Z : ob V) :
  αinv^{ V }_{ internal_hom X (internal_hom Y Z), X, Y} · internal_eval X (internal_hom Y Z) ⊗^{ V}_{r} Y
  · internal_eval Y Z = internal_uncurry X Y Z ⊗^{ V}_{r} (X ⊗_{ V} Y) · internal_eval (X ⊗_{ V} Y) Z.
Proof.
  unfold internal_uncurry.
  refine (_ @ ! internal_lam_tensor_eval _).
  apply (maponpaths (postcompose _)).
  apply maponpaths.
  apply pathsinv0.
  apply (when_bifunctor_becomes_rightwhiskering V).
Qed.

Lemma internal_uncurry_runitor (X Y: ob V) :
  internal_postcomp X (internal_lam ru^{V}_{ Y}) · internal_uncurry X I_{ V} Y = internal_precomp ru^{ V }_{ X} Y.
Proof.
  refine (internal_lam_natural _ _ @ _).
  unfold monoidal_cat_tensor_mor; rewrite 2 (when_bifunctor_becomes_rightwhiskering V).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (f · _)) (monoidal_associatorinvnatright V _ _ _ _ _) @ _).
  refine (maponpaths internal_lam (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f · _))) (! bifunctor_rightcomp V _ _ _ _ _ _) @ _).
  rewrite <- (hom_onmorphisms_is_postcomp X).
  refine (! maponpaths (λ f, internal_lam (_ · (f ⊗^{V}_{r} _ · _))) (internal_eval_nat _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f · _))) (bifunctor_rightcomp V _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (internal_lam_tensor_eval _) @ _).
  refine (maponpaths internal_lam (assoc' _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (monoidal_rightunitornat _ _ _ _) @ _).
  refine (maponpaths internal_lam (assoc _ _ _) @ _).
  refine (! id_right _ @ _).
  rewrite <- internal_precomp_id.
  rewrite <- (pr1 (monoidal_rightunitorisolaw V _)).
  rewrite internal_precomp_comp.
  refine (assoc _ _ _ @ _ @ id_left _).
  apply (maponpaths (postcompose _)).
  rewrite internal_lam_precomp.
  refine (_ @ triangle_id_right_ad (pr2 (pr2 V _)) _).
  apply (maponpaths (compose _)), maponpaths.
  refine (assoc _ _ _ @ _ @ id_left _).
  apply (maponpaths (postcompose _)).
  rewrite assoc.
  rewrite <- (when_bifunctor_becomes_leftwhiskering V).
  refine (maponpaths (λ f, f · _) (mon_rinvunitor_triangle _ _) @ _).
  apply (monoidal_rightunitorisolaw V).
Qed.

Lemma internal_lam_uncurry {W X Y Z : ob V} (f : V⟦(W ⊗_{V} X) ⊗_{V} Y, Z⟧) :
  internal_lam (internal_lam f) · internal_uncurry _ _ _ = internal_lam (αinv^{V}_{_,_,_} · f).
Proof.
  unfold internal_lam.
  rewrite 3 hom_onmorphisms_is_postcomp.
  rewrite (internal_postcomp_comp X).
  rewrite assoc.
  rewrite assoc'.
  refine (! maponpaths (compose _) (uncurry_nat3 _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (uncurry_unit _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  apply pathsinv0.
  now rewrite internal_postcomp_comp.
Qed.

Lemma internal_uncurry_uncurry (W X Y Z : ob V) :
  internal_postcomp W (internal_uncurry X Y Z) · internal_uncurry _ _ _ · internal_precomp (α^{V}_{_,_,_}) _ =
    internal_uncurry _ _ _ · internal_uncurry _ _ _.
Proof.
  unfold internal_uncurry.
  rewrite 2 internal_lam_natural.
  rewrite internal_lam_precomp.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt;
    rewrite 6 (when_bifunctor_becomes_rightwhiskering V).  
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatorinvnatright V _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (maponpaths (λ f, f · _) (_ @ bifunctor_rightcomp  V _ _ _ _ _ _)).
    apply maponpaths.
    apply pathsinv0.
    apply internal_lam_tensor_eval.
  }
  refine (maponpaths (compose _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (monoidal_associatorinvnatright V _ _ _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (! bifunctor_rightcomp V _ _ _ _ _ _ @ _)).
  refine (maponpaths (λ f, f ⊗^{V}_{r} _) (internal_lam_tensor_eval _ @ _)).
  apply internal_lam_natural.
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering V).
  rewrite assoc'.
  refine (maponpaths (compose _) (internal_lam_tensor_eval _)).
  rewrite (bifunctor_rightcomp V).
  repeat rewrite assoc.
  do 2 apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (monoidal_associatorinvnatright V _ _ _ _ _) @ _).
  rewrite (bifunctor_rightcomp V).
  repeat rewrite assoc.
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (! monoidal_pentagon_identity_inv V _ _ _ _) @ _).
  refine (_ @ id_left _).
  repeat rewrite assoc.
  repeat apply cancel_postcomposition.
  refine (! bifunctor_leftcomp V _ _ _ _ _ _ @ _ @ bifunctor_leftid V _ _).
  apply maponpaths.
  apply (monoidal_associatorisolaw V).
Qed.

Lemma internal_swap_tensor_curry (W X Y Z : ob V) :
  internal_swap_arg W X (Y ⊗_{V} Z) · internal_curry Y Z (internal_hom W X) =
  internal_postcomp W (internal_curry Y Z X) · internal_swap_arg W (internal_hom Z X) Y · internal_postcomp Y (internal_swap_arg W X Z).
Proof.
  unfold internal_swap_arg, internal_curry.
  repeat rewrite internal_lam_natural.
  rewrite internal_lam_postcomp.
  rewrite 2 internal_lam_natural.
  do 2 apply maponpaths.
  unfold monoidal_cat_tensor_mor; repeat rewrite (when_bifunctor_becomes_rightwhiskering V).
  rewrite 3 (when_bifunctor_becomes_leftwhiskering V).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_associatornatright V _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (internal_lam_tensor_eval _) @ _).
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering V).
  refine (assoc _ _ _ @ _).
  refine (! maponpaths (compose _) (id_left _) @ _).
  unfold monoidal_cat_tensor_pt; rewrite <- (bifunctor_rightid V).
  refine (maponpaths (λ f, _ · (f ⊗^{V}_{r} _ · _)) (! internal_curry_uncurry _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (bifunctor_rightcomp V _ _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! uncurry_counit _ _ _) @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  unfold internal_curry.
  unfold monoidal_cat_tensor_pt.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_associatorinvnatright V _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, _ · f) (! bifunctor_rightcomp V _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ · f ⊗^{V}_{r} _) (internal_lam_tensor_eval _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (monoidal_associatorinvnatright V _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  do 2 refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_associatornatright V _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (bifunctor_equalwhiskers V _ _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).  
  do 2 refine (_ @ assoc' _ _ _).
  do 3 refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f) ⊗^{V}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f ⊗^{V}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (f · _) ⊗^{V}_{r} _ · _) (monoidal_associatornatright V _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f ⊗^{V}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f) ⊗^{V}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ ! maponpaths (λ f, _ · internal_lam (_ · (f · _)) ⊗^{V}_{r} _ · _) (bifunctor_equalwhiskers V _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f) ⊗^{V}_{r} _ · _) (assoc _ _ _)).
  do 2 refine (_ @ maponpaths (λ f, _ · internal_lam f ⊗^{V}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f ⊗^{V}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f) ⊗^{V}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f ⊗^{V}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f · _) ⊗^{V}_{r} _ · _) (! monoidal_associatorinvnatright V _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (f · _) ⊗^{V}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f ⊗^{V}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f) ⊗^{V}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f · _)) ⊗^{V}_{r} _ · _) (bifunctor_rightcomp V _ _ _ _ _ _)).
  rewrite <- (hom_onmorphisms_is_postcomp W).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f ⊗^{ V}_{r} Y · _)) ⊗^{V}_{r} _ · _) (internal_eval_nat _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f · _)) ⊗^{V}_{r} _ · _) (! bifunctor_rightcomp V _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f) ⊗^{V}_{r} _ · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam f ⊗^{V}_{r} _ · _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · f) ⊗^{V}_{r} _ · _) (! internal_lam_tensor_eval _)).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  refine (_ @ maponpaths (λ f, _ · (f · _)) (! monoidal_associatorinvnatright V _ _ _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (bifunctor_rightcomp V _ _ _ _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f ⊗^{V}_{r} _) (! internal_lam_tensor_eval _)).
  refine (_ @ maponpaths (compose _) (! bifunctor_rightcomp V _ _ _ _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (compose _) (! bifunctor_rightcomp V _ _ _ _ _ _)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  do 2 refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ id_right _)).
  2 : {
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    exact (pr1 (monoidal_associatorisolaw V _ _ _)).
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_pentagonidentity V _ _ _ _)).
  repeat rewrite assoc'.
  do 2 apply maponpaths.
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (monoidal_associatorinvnatleft V _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (maponpaths (compose _) (_ @ assoc' _ _ _)).
    refine (_ @ maponpaths (λ f, f · _) (monoidal_pentagon_identity_inv V _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) _).
    2 : {
      refine (_ @ bifunctor_rightcomp V _ _ _ _ _ _).
      apply maponpaths.
      refine (_ @ assoc' _ _ _).
      refine (! id_left _ @ _).
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (monoidal_associatorisolaw V).
    }
    rewrite (bifunctor_rightcomp V).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (monoidal_associatorinvnatleftright V _ _ _ _ _)).
      apply assoc.
    }
    refine (_ @ assoc' _ _ _).
    refine (maponpaths (compose _) _).
    refine (assoc _ _ _ @ _ @ id_left _).
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      refine (! bifunctor_leftcomp V _ _ _ _ _ _ @ _).
      refine (_ @ bifunctor_leftid V _ _).
      apply maponpaths.
      apply (pr1 (monoidal_associatorisolaw V _ _ _)).
    }
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      apply pathsinv0.
      apply monoidal_pentagon_identity_inv.
    }
    apply assoc'.
  }
  repeat rewrite assoc.
  do 2 apply cancel_postcomposition.
  refine (_ @ assoc _ _ _).
  refine (_ @ map_on_two_paths compose _ (bifunctor_leftcomp V _ _ _ _ _ _)).
  refine (_ @ bifunctor_leftcomp V _ _ _ _ _ _).
  apply maponpaths.
  2 : {
    refine (bifunctor_leftcomp V _ _ _ _ _ _ @ _).
    apply cancel_postcomposition.
    apply (bifunctor_leftcomp V).
  }
  refine (_ @ assoc' _ _ _).
  rewrite <- (when_bifunctor_becomes_leftwhiskering V), <- (when_bifunctor_becomes_rightwhiskering V).
  apply (sym_mon_tensor_rassociator V).
Qed.

Lemma internal_uncurry_tensor_swap (W X Y Z : ob V) :
  internal_uncurry W X (internal_hom Y Z) · internal_swap_arg (W ⊗_{V} X) Z Y =
  internal_postcomp W (internal_swap_arg X Z Y) · (internal_swap_arg W (internal_hom X Z) Y · internal_postcomp Y (internal_uncurry W X Z)).
Proof.
  unfold internal_uncurry, internal_swap_arg.
  rewrite internal_lam_postcomp.
  repeat rewrite internal_lam_natural.
  do 2 apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  repeat rewrite (when_bifunctor_becomes_rightwhiskering V).
  repeat rewrite (when_bifunctor_becomes_leftwhiskering V).
  unfold monoidal_cat_tensor_pt.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _ @ _) @ _).
  refine (maponpaths (λ f, f · _) (! monoidal_associatornatright V _ _ _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (bifunctor_equalwhiskers V _ _ _ _ _ _) @ _).
  apply assoc.
  rewrite assoc'.
  refine (maponpaths (compose _) (monoidal_associatorinvnatright V _ _ _ _ _) @ _).
  apply assoc.
  rewrite assoc'.
  refine (maponpaths (compose _) (! bifunctor_rightcomp V _ _ _ _ _ _ @ _)).
  now rewrite internal_lam_tensor_eval.
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
    refine (_ @ maponpaths (λ f, f · _) (! monoidal_associatorinvnatright V _ _ _ _ _)).
    rewrite assoc'.
    refine (maponpaths (compose _) (_ @ bifunctor_rightcomp V _ _ _ _ _ _)).
    now rewrite internal_lam_tensor_eval.
  }
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) _).
    2 : {
      apply pathsinv0.
      apply (monoidal_associatorinvnatright V).
    }
    rewrite assoc'.
    refine (_ @ maponpaths (compose _) _).
    2 : {
      refine (_ @ bifunctor_rightcomp V _ _ _ _ _ _).
      apply maponpaths.
      rewrite assoc.
      refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
      2 : {
        refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, f · _) (_ @ assoc' _ _ _)).
          2 : {
            refine (_ @ maponpaths (λ f, f · _) (monoidal_associatornatright V _ _ _ _ _)).
            rewrite assoc'.
            refine (_ @ maponpaths (compose _) (! bifunctor_equalwhiskers V _ _ _ _ _ _)).
            apply assoc'.            
          }
          rewrite assoc'.
          refine (_ @ maponpaths (compose _) (! monoidal_associatorinvnatright V _ _ _ _ _)).
          apply assoc'. 
        }
        rewrite assoc'.
        refine (_ @ maponpaths (compose _) (_ @ bifunctor_rightcomp V _ _ _ _ _ _)).
        2 : {
          refine (_ @ maponpaths (λ f, f ⊗^{V}_{r} _) (! internal_lam_tensor_eval _)).
          apply pathsinv0.
          apply (bifunctor_rightcomp V).
        }
        apply assoc'.
      }
      rewrite assoc'.
      refine (maponpaths (compose _) (! internal_lam_tensor_eval _)).
    }
    rewrite 2 (bifunctor_rightcomp V X).
    now rewrite 2 assoc.
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (! internal_lam_tensor_eval _)).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  rewrite (bifunctor_rightcomp V Y).
  repeat rewrite assoc.
  apply cancel_postcomposition.
  do 3 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f · _) (monoidal_associatornatright V _ _ _ _ _)).
    refine (_ @ assoc _ _ _).
    refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
    2 : {
      refine (_ @ maponpaths (λ f, f · _) (! bifunctor_equalwhiskers V _ _ _ _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths (compose _) (! monoidal_associatorinvnatright V _ _ _ _ _)).
      apply assoc'.
    }
    apply assoc'.
  }
  rewrite (bifunctor_rightcomp V Y).
  rewrite 2 assoc.
  apply cancel_postcomposition.
  do 2 refine (assoc' _ _ _ @ _).
  refine (! id_left _ @ _).
  rewrite <- (pr2 (monoidal_associatorisolaw V _ _ _)).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! monoidal_pentagonidentity V _ _ _ _ @ _)).
  apply assoc'.
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite (bifunctor_rightcomp V X).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  do 2 refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! id_left _ @ _) @ _).
  rewrite <- (bifunctor_leftid V).
  rewrite <- (pr1 (monoidal_associatorisolaw V _ _ _)).
  refine (maponpaths (λ f, f · _) (bifunctor_leftcomp V _ _ _ _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _ @ _)).
  apply (monoidal_pentagon_identity_inv V).
  repeat rewrite assoc.
  apply cancel_postcomposition.
  refine (maponpaths (λ f, f · _) (assoc' _ _ _ @ _) @ _).
  refine (maponpaths (compose _) (! bifunctor_leftcomp V _ _ _ _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (! bifunctor_leftcomp V _ _ _ _ _ _ @ _) @ _).
  refine (maponpaths (λ f,  _ ⊗^{V}_{l} f) (assoc _ _ _ @ _) @ _).
  refine (_ @ assoc' _ _ _).
  apply sym_mon_hexagon_lassociator.
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_leftwhiskering V), (when_bifunctor_becomes_rightwhiskering V).
  now rewrite 2 (bifunctor_leftcomp V).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (monoidal_associatornatleftright V _ _ _ _ _)).
  rewrite (bifunctor_rightcomp V X).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (! id_left _ @ _) @ _).
  rewrite <- (bifunctor_rightid V).
  unfold monoidal_cat_tensor_pt.
  rewrite <- (pr2 (monoidal_associatorisolaw V _ _ _)).
  rewrite (bifunctor_rightcomp V).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _ @ _)).
  apply (monoidal_pentagonidentity V).
  repeat rewrite assoc'.
  do 2 apply maponpaths.
  refine (maponpaths (compose _) (monoidal_associatorinvnatleft V _ _ _ _ _) @ _).
  refine (_ @ id_left _).
  rewrite assoc.
  apply cancel_postcomposition.
  apply (monoidal_associatorisolaw V).
Qed.

Lemma curry_nat1 {X1 X2 : ob V} (Y Z : ob V) (f : V⟦X2, X1⟧) :
  internal_curry X1 Y Z · internal_precomp f (internal_hom Y Z) = internal_precomp (f ⊗^{ V}_{r} Y) Z · internal_curry X2 Y Z.
Proof.
  unfold internal_curry.
  rewrite internal_lam_precomp.
  rewrite 3 internal_lam_natural.
  do 2 apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt.
  rewrite 3 (when_bifunctor_becomes_rightwhiskering V).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (! monoidal_associatornatleftright V _ _ _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (! mon_closed_adj_natural_co _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  exact (monoidal_associatornatright V _ _ _ _ _).
Qed.

Lemma curry_nat2 {Y1 Y2 : ob V} (X Z : ob V) (f : V⟦Y2, Y1⟧) :
  internal_curry X Y1 Z · internal_postcomp X (internal_precomp f Z) = internal_precomp (X ⊗^{ V}_{l} f) Z · internal_curry X Y2 Z.
Proof.
  unfold internal_curry.
  rewrite internal_lam_postcomp.
  rewrite internal_lam_precomp.
  rewrite 2 internal_lam_natural.
  do 2 apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering V).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (! monoidal_associatornatleft V _ _ _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (! mon_closed_adj_natural_co _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  exact (monoidal_associatornatright V _ _ _ _ _).
Qed.

Lemma internal_curry_curry (W X Y Z : ob V) :
  internal_precomp α^{V}_{_,_,_} _ · internal_curry (W ⊗_{V} X) Y Z · internal_curry _ _ _ =
    internal_curry _ _ _ · internal_postcomp _ (internal_curry _  _ _).
Proof.
  unfold internal_curry.
  rewrite internal_lam_postcomp.
  repeat rewrite internal_lam_natural.
  do 2 apply maponpaths.
  unfold monoidal_cat_tensor_mor, monoidal_cat_tensor_pt.
  repeat rewrite (when_bifunctor_becomes_rightwhiskering V).
  rewrite assoc.
  rewrite <- (monoidal_associatornatright V).
  rewrite assoc'.
  rewrite internal_lam_tensor_eval.
  rewrite internal_lam_natural.
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering V).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_associatornatright V _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite internal_lam_tensor_eval.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, _ · (f · _)) (! monoidal_associatornatright V _ _ _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (compose _) (mon_closed_adj_natural_co _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  apply monoidal_pentagonidentity.
Qed.

Lemma internal_swap_arg_unit_tensor (X Y Z : ob V) :
  unit_from_are_adjoints (pr2 (pr2 V Y)) X · internal_postcomp Y (unit_from_are_adjoints (pr2 (pr2 V Z)) (X ⊗_{ V} Y))
    · internal_swap_arg Y (rightwhiskering_functor (pr1 V) Z (X ⊗_{ V} Y)) Z =
    unit_from_are_adjoints (pr2 (pr2 V (Z ⊗_{ V} Y))) X
      · (internal_curry Z Y (X ⊗_{ pr1 V} (Z ⊗_{ V} Y))
           · internal_postcomp Z (internal_postcomp Y (X ⊗^{ V}_{l} sym_mon_braiding V Z Y · αinv^{ V }_{ X, Y, Z}))) .
Proof.
  simpl.
  refine (! maponpaths (λ f, f · _) (id_right _) @ _).
  rewrite <- (internal_postcomp_id Y).
  refine (! maponpaths (λ f, _ · internal_postcomp Y f · _) (internal_postcomp_id Z _) @ _).
  rewrite <- (pr1 (monoidal_associatorisolaw V _ _ _)).
  rewrite 2 internal_postcomp_comp.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (λ f, f · _) (curry_unit _ _ _) @ _).
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (f · _)) (curry_nat3 _ _ _) @ _).
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f)) (curry_swap _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- internal_pre_post_comp_as_post_pre_comp.
  rewrite internal_pre_post_comp_as_pre_post_comp.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite <- curry_nat3.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply internal_postcomp_comp.
Qed.  
  
Lemma internal_swap_arg_unit (X Y Z : ob V) :
  unit_from_are_adjoints (pr2 (pr2 V Y)) X · internal_postcomp Y (unit_from_are_adjoints (pr2 (pr2 V Z)) (X ⊗_{V} Y))
    · internal_swap_arg Y _ Z =
    unit_from_are_adjoints (pr2 (pr2 V Z)) X
      · internal_postcomp Z (unit_from_are_adjoints (pr2 (pr2 V Y)) (X ⊗_{V} Z)
                               · internal_postcomp Y (α^{ V }_{ X, Z, Y} · (X ⊗^{ V}_{l} sym_mon_braiding V Z Y · αinv^{ V }_{ X, Y, Z}))).
Proof.
  refine (internal_swap_arg_unit_tensor X Y Z @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (curry_unit _ _ _) @ _).
  rewrite 2 assoc'.
  apply maponpaths.
  rewrite <- (internal_postcomp_comp Z).
  refine (! internal_postcomp_comp Z _ _ @ _).
  repeat apply maponpaths.
  exact (! internal_postcomp_comp Y _ _).
Qed.

                                                                         
Lemma internal_lam_lam_swap {W X Y Z : ob V} (f : V⟦W ⊗_{V} X ⊗_{V} Y, Z⟧) :
  internal_lam (internal_lam f) · internal_swap_arg X Z Y =
    internal_lam (internal_lam (α^{ V }_{ W, Y, X} · W ⊗^{ V}_{l} sym_mon_braiding V Y X · αinv^{ V }_{ W, X, Y} · f)).
Proof.
  refine (assoc' _ _ _ @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (λ f, _ · (f · _)) (internal_postcomp_comp X _ _) @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (! internal_swap_arg_nat3 _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (internal_swap_arg_unit _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (! internal_postcomp_comp Y _ _ @ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (! internal_postcomp_comp X _ _ @ _).
  apply maponpaths.
  apply (maponpaths (postcompose _)).
  apply assoc.
Qed.

Lemma internal_lam_curry {W X Y Z : ob V} (f : V⟦W ⊗_{V} (X ⊗_{V} Y), Z⟧) :
  internal_lam f · internal_curry X Y Z = internal_lam (internal_lam (α^{ V }_{ W, X, Y} · f)).
Proof.
  refine (assoc' _ _ _ @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (curry_nat3 _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f,f · _) (! curry_unit _ _ _) @ _).
  rewrite 2 assoc'.
  apply (maponpaths (compose _)).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (! internal_postcomp_comp _ _ _) @ _).
  refine (! internal_postcomp_comp _ _ _ @ _).
  apply maponpaths.
  apply (maponpaths (compose _)).
  refine (! internal_postcomp_comp _ _ _ @ _).
  now rewrite hom_onmorphisms_is_postcomp.
Qed.

End sym_mon_closed_results.

Arguments lolli_bifunctor V : clear implicits.



Lemma sym_mon_braiding_tensor_associator {V : sym_monoidal_cat} (X Y Z : ob V) :
  α^{ V }_{ X, Y, Z} · sym_mon_braiding V X (Y ⊗_{ V} Z) · α^{ V }_{ Y, Z, X} = 
    sym_mon_braiding V (X ⊗_{ V} Y) Z · αinv^{ V }_{ Z, X, Y} · sym_mon_braiding V (Z ⊗_{ V} X) Y.
Proof.
  refine (sym_mon_hexagon_lassociator V X Y Z @ _).
  refine (! id_right _ @ _).
  refine (! maponpaths (compose _) (pr1 (monoidal_braiding_inverses V _ _)) @ _).
  refine (assoc _ _ _ @ _).
  apply cancel_postcomposition.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (tensor_sym_mon_braiding V _ _) @ _).
  refine (assoc _ _ _ @ _ @ id_right _).
  refine (_ @ maponpaths (compose _) (_ @ bifunctor_rightid V _ _)).
  2 : {
    refine (_ @ maponpaths (λ f, f ⊗^{V}_{r} _) (pr1 (monoidal_braiding_inverses V _ _))).
    apply pathsinv0.
    apply (bifunctor_rightcomp V).
  }
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering V).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ ! sym_mon_hexagon_rassociator1 V _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (! sym_mon_tensor_lassociator1 V _ _ _)).
  refine (! id_right _ @ _).
  repeat rewrite assoc'.
  repeat apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorisolaw V).
Qed.

Definition eqtype {A : UU} {a b : A} (eq : a=b) : UU := A.


Section ProductsToSymMonoidal.

  Context (C : category) (bp : BinProducts C) (T : Terminal C).
  
  Definition prods_monoidal_data : monoidal_data C.
  Proof.
    use tpair.
    apply (bifunctor_from_functorfromproductcat (binproduct_functor bp)).
    use tpair.
    apply T.
    split6.
    intros x.
    apply (BinProductPr2 _ (bp T x)).
    intros x.
    apply (BinProductArrow _ (bp T x)).
    apply (TerminalArrow T).
    apply identity.
    intros x.
    apply (BinProductPr1 _ (bp x T)).
    intros x.
    apply (BinProductArrow _ (bp x T)).
    apply identity.
    apply (TerminalArrow T).
    intros x y z.
    apply (BinProduct_assoc_invmor bp x y z).
    intros x y z.
    apply (BinProduct_assoc bp x y z).
  Defined. 
  
  Lemma prods_monoidal_laws : monoidal_laws prods_monoidal_data.
  Proof using Type.
    split6.
    apply (bifunctor_from_functorfromproductcat (binproduct_functor bp)).
    split.
    intros x y f.
    apply BinProductOfArrowsPr2.
    intros x.
    apply terminal_binprod_unit_l_z.
    split.
    intros x y f.
    apply BinProductOfArrowsPr1.
    intros x.
    apply terminal_binprod_unit_r_z.
    assert (reorder : ∏ W X Y Z : UU, ((W × X × Y) × Z) → W × X × Y × Z).
    intros W X Y Z wxyz.
    split4; apply wxyz.
    apply reorder; clear reorder.
    split.
    split3;
      intros x y z1 z2 f;
      refine (_ @ id_left _);
      refine (maponpaths (compose _) _ @ _);
      [ | refine (assoc _ _ _ @ _);
          apply cancel_postcomposition, (pr2 (BinProduct_assoc bp _ _ _)) | |
        refine (assoc _ _ _ @ _);
        apply cancel_postcomposition, (pr2 (BinProduct_assoc bp _ _ _)) | |
        refine (assoc _ _ _ @ _);
        apply cancel_postcomposition, (pr2 (BinProduct_assoc bp _ _ _))];
      refine (! id_right _ @ _ @ assoc' _ _ _);
      refine (_ @ maponpaths (λ f, f · _) _);
      [refine (_ @ assoc _ _ _);
       apply maponpaths, pathsinv0, (pr2 (BinProduct_assoc bp _ _ _)) | |
        refine (_ @ assoc _ _ _);
        apply maponpaths, pathsinv0, (pr2 (BinProduct_assoc bp _ _ _)) | |
        refine (_ @ assoc _ _ _);
        apply maponpaths, pathsinv0, (pr2 (BinProduct_assoc bp _ _ _)) | ];
      try refine (_ @ BinProduct_OfArrows_assoc bp _ _ _); 
      try refine (BinProduct_OfArrows_assoc bp _ _ _ @ _); 
      try apply cancel_postcomposition.
    try apply maponpaths.
    apply (maponpaths (λ h, BinProductOfArrows C _ _ h f)).
    apply BinProductOfArrows_id.
    apply (maponpaths (λ h, BinProductOfArrows C _ _ f h)).
    apply pathsinv0.
    apply BinProductOfArrows_id.
    apply pathsinv0.
    apply (BinProduct_OfArrows_assoc bp).    
    intros x y z.
    split; apply BinProduct_assoc_is_inverse.
    (* triangle identity : *)
    intros x y.
    apply BinProductArrowsEq.
    refine (_ @ ! BinProductOfArrowsPr1 _ _ _ _ _).
    refine (assoc' _ _ _ @ _).
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths, BinProductOfArrowsPr1.
    refine (id_right _ @ _).
    apply BinProductPr1Commutes.
    refine (_ @ ! BinProductOfArrowsPr2 _ _ _ _ _).
    refine (assoc' _ _ _ @ _).
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths, BinProductOfArrowsPr2.
    refine (_ @ ! id_right _).
    refine (maponpaths (λ f, f · _) _ @ _).
    apply BinProductPr2Commutes.
    refine (_ @ id_right _).
    apply BinProductPr2Commutes.
    (* pentagon identity : *)
    intros w x y z.
    apply BinProductArrowsEq.
    refine (assoc' _ _ _ @ _  @ assoc _ _ _ @ _).
    apply maponpaths, BinProductOfArrowsPr1.
    refine (id_right _ @ _).
    refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply maponpaths, BinProductPr1Commutes.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths, pathsinv0, BinProductPr1Commutes.
    }
    refine (_ @ assoc _ _ _ @  _).
    2 : {
      apply cancel_postcomposition, pathsinv0, BinProductPr1Commutes.
    }
    refine (_ @ assoc' _ _ _ @  _).
    apply cancel_postcomposition.
    apply BinProductPr1Commutes.
    apply maponpaths.
    apply BinProductPr1Commutes.
    refine (assoc' _ _ _ @ _  @ assoc _ _ _ @ _).
    apply maponpaths, BinProductOfArrowsPr2.
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _).
    apply maponpaths, BinProductPr2Commutes.
    refine (_ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths, pathsinv0, BinProductPr2Commutes.
    }
    apply BinProductArrowsEq.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply maponpaths, BinProductPr1Commutes.
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply BinProductOfArrowsPr1.
    refine (_ @ assoc' _ _ _ @  _).
    apply cancel_postcomposition, BinProductPr1Commutes.
    refine (_ @ _ ).
    apply maponpaths.
    refine (assoc _ _ _ @ _).
    apply cancel_postcomposition, BinProductPr2Commutes.
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths, BinProductOfArrowsPr1.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths, pathsinv0, BinProductPr1Commutes.
    }
    refine (_ @ assoc _ _ _ @ _).
    2 : {
      apply cancel_postcomposition, pathsinv0, BinProductPr1Commutes.
    }
    apply assoc'.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    apply maponpaths, BinProductPr2Commutes.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths, pathsinv0, BinProductPr2Commutes.
    }
    refine (_ @ ! id_right _).
    refine (_ @ ! BinProductPr2Commutes _ _ _ _ _ _ _).
    refine (_ @ BinProductOfArrows_compxid _ _ _ _ @ _).
    apply cancel_postcomposition.
    apply BinProductOfArrows_compxid.
    refine (maponpaths (λ f, BinProductOfArrows _ _ _ f _) _).
    refine (maponpaths (λ f, f · _) _ @ _).
    apply BinProductPr2Commutes.
    refine (BinProductPr2Commutes _ _ _ _ _ _ _ @ _).
    apply id_right.
  Qed.
  
  Definition prods_monoidal_structure : monoidal C.
  Proof.
    exists prods_monoidal_data.
    apply prods_monoidal_laws.
  Defined.

  Definition prods_monoidal_cat : monoidal_cat.
  Proof.
    exists C.
    apply prods_monoidal_structure.
  Defined.

  Lemma prods_BinProductPr1Commutes {x y a : prods_monoidal_cat} (f : prods_monoidal_cat ⟦ a, x ⟧) (g : prods_monoidal_cat ⟦ a, y ⟧):
    BinProductArrow C (bp x y) f g · semi_cart_tensor_pr1 (M:= prods_monoidal_cat) (pr2 T) x y = f.
  Proof.
    refine (_ @ BinProductPr1Commutes _ _ _ _ _ _ _).
    apply maponpaths.
    refine (_ @ assoc' _ _ _ @ id_left _ @ _).
    do 2 apply cancel_postcomposition.
    apply BinProductOfArrows_id.
    refine (_ @ id_right _).
    apply BinProductOfArrowsPr1.
  Qed.

  Lemma prods_BinProductPr2Commutes {x y a : prods_monoidal_cat} (f : prods_monoidal_cat ⟦ a, x ⟧) (g : prods_monoidal_cat ⟦ a, y ⟧):
    BinProductArrow C (bp x y) f g · semi_cart_tensor_pr2 (M:= prods_monoidal_cat) (pr2 T) x y = g.
  Proof.
    refine (_ @ BinProductPr2Commutes _ _ _ _ _ _ _).
    apply maponpaths.
    unfold semi_cart_tensor_pr2, monoidal_cat_tensor_mor, functoronmorphisms1, leftwhiskering_on_morphisms; simpl.
    rewrite BinProductOfArrows_id.
    rewrite id_right.
    refine (_ @ id_right _).
    apply BinProductOfArrowsPr2.    
  Qed.
  
  Lemma prods_BinProductArrowUnique {x y a : prods_monoidal_cat} (f : prods_monoidal_cat ⟦ a, x ⟧) (g : prods_monoidal_cat ⟦ a, y ⟧):
    ∏ t :
      ∑ fg : C ⟦ a, monoidal_cat_tensor_pt x y ⟧,
          fg · semi_cart_tensor_pr1 (M:= prods_monoidal_cat) (pr2 T) x y = f ×
             fg · semi_cart_tensor_pr2 (M:= prods_monoidal_cat) (pr2 T) x y = g,
          t = BinProductArrow C (bp x y) f g,, prods_BinProductPr1Commutes f g,, prods_BinProductPr2Commutes f g.
  Proof.
    intros (pa, (eq1, eq2)).
    apply subtypePath.
    intros h.
    apply isapropdirprod;
      apply (pr2 C).
    apply BinProductArrowUnique.
    refine (_ @ eq1).
    apply maponpaths.
    unfold semi_cart_tensor_pr1, monoidal_cat_tensor_mor, functoronmorphisms1, rightwhiskering_on_morphisms; simpl.
    rewrite BinProductOfArrows_id.
    rewrite id_left.
    apply pathsinv0.
    refine (_ @ id_right _).
    apply BinProductOfArrowsPr1.
    refine (_ @ eq2).
    apply maponpaths.
    unfold semi_cart_tensor_pr2, monoidal_cat_tensor_mor, functoronmorphisms1, leftwhiskering_on_morphisms; simpl.
    rewrite BinProductOfArrows_id.
    rewrite id_right.
    apply pathsinv0.
    refine (_ @ id_right _).
    apply BinProductOfArrowsPr2.    
  Qed.
  
  Definition prods_isBinProduct : tensor_isBinProduct (M:= prods_monoidal_cat) (pr2 T).
  Proof.
    intros x y.
    intros a f g.
    use tpair.
    use tpair.
    exact (BinProductArrow _ _ f g).
    split.
    apply prods_BinProductPr1Commutes.
    apply prods_BinProductPr2Commutes.
    simpl. (* necessary *)
    apply prods_BinProductArrowUnique.
  Defined.
    
  Definition prods_sym_monoidal_cat : sym_monoidal_cat.
  Proof.
    use tpair.
    apply prods_monoidal_cat.
    apply cartesian_to_symmetric.
    use tpair.
    exact (pr2 T).
    apply prods_isBinProduct.
  Defined.
  
End ProductsToSymMonoidal.


Section HSetSMC.

  Definition HSet_sym_mon_cat : sym_monoidal_cat.
  Proof.
    use prods_sym_monoidal_cat.
    2 : apply BinProductsHSET.
    apply TerminalHSET.
  Defined.
  
  Definition HSet_SMC : sym_mon_closed_cat.
  Proof.
    exists HSet_sym_mon_cat.
    intros x.
    exists (exponential_functor x).
    apply are_adjoints_constprod_functor2.
  Defined.
  
End HSetSMC.


Section opp_SMC.

  Context (C : sym_monoidal_cat).
  
  Lemma braidinglaws_opp :
    braiding_laws (M:= monoidal_opp C) (λ X Y : C, sym_mon_braiding C Y X) (λ X Y : C, sym_mon_braiding C Y X).
  Proof.
    split3.
    split;
      intros X Y Z f;
      apply pathsinv0, (pr22 C).
    apply (pr22 C).
    split;
      intros X Y Z;
      refine (assoc (C:=C) _ _ _ @ _ @ assoc' (C:=C) _ _ _);
      apply (pr22 C).
  Qed.

  Definition symmetric_opp : symmetric (monoidal_opp C).
  Proof.
    use tpair.
    intros X Y.
    apply (sym_mon_braiding C).
    apply braidinglaws_opp.
  Defined.

  Definition sym_monoidal_opp_cat : sym_monoidal_cat.
  Proof.
    refine ((_,, monoidal_opp C),, symmetric_opp).
  Defined.

(*
Lemma homset_opfunctor_eq {C : category} (c : C) : cov_homSet_functor (C:=C^op) c = contra_homSet_functor c.
Proof.
  apply functor_eq.
  apply homset_property.
  use total2_paths_f.
  apply idpath.
  refine (idpath_transportf _ _ @ _).
  apply funextsec; intros X.
  apply funextsec; intros Y.
  apply funextfun; intros f.
  apply funextfun; intros h.
Qed.*)

End opp_SMC. 
