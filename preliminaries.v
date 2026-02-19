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

(* Preliminaries *)
Definition is_dinatural {C D : category} {F G : bifunctor (C^opp) C D} (α : ∏ c : C, D⟦(pr11 F) c c, (pr11 G) c c⟧) : hProp.
Proof.
  refine (∀ c c' : C, ∀ f : C⟦c, c'⟧, _).
  use make_hProp.
  exact ((leftwhiskering_on_morphisms G c c c' f) ∘ (α c) ∘ (rightwhiskering_on_morphisms F c c' c f) =
           (rightwhiskering_on_morphisms G c' c' c f) ∘ (α c') ∘ (leftwhiskering_on_morphisms F c' c c' f)).
  exact (pr2 D _ _ _ _).
Defined.

Definition dinat_trans {C D : category} (F G : bifunctor (C^opp) C D) : UU :=
  ∑ (α : ∏ c : C, D⟦(pr11 F) c c, (pr11 G) c c⟧), is_dinatural α.

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
  exact (λ _ _ _ _ _ _, ! pr1 (pr121 E) a a (identity a)).
  exact (λ _ _ _ _ _ _, ! pr1 (pr121 E) a a (identity a)).
  exact (λ _ _ _ _ _ _, idpath _).
Defined.

Lemma hom_onmorphisms_is_postcomp {E : sym_mon_closed_cat} {Y Z : ob E} (X : ob E) (f : E⟦Y, Z⟧) : # (pr1 (pr2 E X)) f = internal_postcomp X f.
Proof.
  unfold internal_postcomp, internal_lam.
  rewrite functor_comp.
  rewrite assoc.
  refine (! id_left _ @ _).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (triangle_id_right_ad (pr2 (pr2 E X))).
Qed.

(* Extra results about symm. mon. cats *)

Definition sym_monoidal_functor (C D : sym_monoidal_cat) : UU :=
  ∑ (F : lax_monoidal_functor C D), is_symmetric_monoidal_functor C D F.

Definition fsym_respects_braiding {C D : sym_monoidal_cat} (F : sym_monoidal_functor C D) := pr2 F.

Definition fmonoidal_from_fsym {C D : sym_monoidal_cat} (F : sym_monoidal_functor C D) : lax_monoidal_functor C D := pr1 F.
Coercion fmonoidal_from_fsym : sym_monoidal_functor >-> lax_monoidal_functor.

Definition mon_closed_adj_natural_statement (V : sym_mon_closed_cat) : UU.
Proof.
  refine (∏ (A X Y : ob V) (f : V ⟦X, Y⟧), _).
  set (etaX := unit_from_are_adjoints (pr2 (pr2 V X))).
  set (etaY := unit_from_are_adjoints (pr2 (pr2 V Y))).
  refine (compose (c:= pr1 (pr2 V X) (A ⊗_{V} Y)) (etaX A) _ = etaY A · _).
  exact (internal_postcomp _ (A ⊗^{V}_{l} f)).
  exact (internal_precomp f _).
Defined.

Lemma mon_closed_adj_natural' (V : sym_mon_closed_cat) :  ∏ (A X Y : V) (f : V ⟦ X, Y ⟧),
  unit_from_are_adjoints (pr2 (pr2 V X)) A · # (pr1 (pr2 V X)) (A ⊗^{ V}_{l} f) =
  unit_from_are_adjoints (pr2 (pr2 V Y)) A · internal_precomp f (A ⊗_{ pr1 V} Y).
Proof.
  unfold mon_closed_adj_natural_statement; simpl.
  intros A X Y f.
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

Lemma mon_closed_adj_natural (V : sym_mon_closed_cat) : mon_closed_adj_natural_statement V.
Proof.
  unfold mon_closed_adj_natural_statement; simpl.
  intros A X Y f.
  rewrite <- hom_onmorphisms_is_postcomp.
  apply mon_closed_adj_natural'.
Qed.

Definition mon_closed_adj_natural_statement_co (V : sym_mon_closed_cat) : UU.
Proof.
  refine (∏ (A X Y : ob V) (f : V ⟦X, Y⟧), _).
  set (epsX := counit_from_are_adjoints (pr2 (pr2 V X))).
  set (epsY := counit_from_are_adjoints (pr2 (pr2 V Y))).
  refine (compose (a:= (pr1 (pr2 V Y) A) ⊗_{V} X) _ (epsX A) = _ · epsY A ).
  exact (internal_precomp f A ⊗^{V}_{r} X).
  exact (_ ⊗^{V}_{l} f).
Defined.
  
Lemma internal_eval_nat {V : sym_mon_closed_cat} (X Z Y : ob V) (f : V ⟦Y, Z⟧) :
  internal_eval X Y · f = # (pr1 (pr2 V X)) f ⊗^{ V}_{r} X · internal_eval X Z.
Proof.
  apply pathsinv0.
  apply (counit_from_are_adjoints (pr2 (pr2 V X))).
Qed.

Lemma internal_lam_tensor_eval {V : sym_mon_closed_cat} {X Y Z: ob V} (f : V⟦X ⊗_{V} Y, Z⟧) :
  internal_lam f ⊗^{V}_{r} Y · internal_eval _ _ = f.
Proof.
  refine (_ @ internal_beta f).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (when_bifunctor_becomes_rightwhiskering V).
Qed.

Lemma mon_closed_adj_natural_co (V : sym_mon_closed_cat) : mon_closed_adj_natural_statement_co V.
Proof.
  intros A X Y f.
  refine (internal_lam_tensor_eval _ @ _).
  unfold monoidal_cat_tensor_mor.
  now rewrite (when_bifunctor_becomes_leftwhiskering V).
Qed.

Definition lolli_bifunctor_data (E : sym_mon_closed_cat) : bifunctor_data (E^opp) E E.
Proof.
  exists (λ x, pr11 (pr2 E x)).
  split.
  intros x y1 y2 g12.
  exact (internal_postcomp _ g12).
  intros y x1 x2 f12.
  exact (internal_precomp f12 _).
Defined.

Lemma lolli_functoronmorphisms_eq (E : sym_mon_closed_cat) : functoronmorphisms_are_equal (lolli_bifunctor_data E).
Proof.
  intros x1 x2 y1 y2 f g.
  exact (! internal_pre_post_comp_as_pre_post_comp f g @ internal_pre_post_comp_as_post_pre_comp f g).
Qed.

Definition lolli_bifunctor (E : sym_mon_closed_cat) : bifunctor (E^opp) E E.
Proof.
  exists (lolli_bifunctor_data E).
  exists internal_postcomp_id.
  exists (λ x y, internal_precomp_id y x).
  exists internal_postcomp_comp.
  split.
  intros w x y z f1 f2.
  exact (internal_precomp_comp f2 f1 w).
  exact (lolli_functoronmorphisms_eq E).
Defined.

Lemma internal_lam_precomp {V : sym_mon_closed_cat} {X Y1 Y2 Z : ob V} (f : V⟦X ⊗_{V} Y1, Z⟧) (g : V⟦Y2, Y1⟧) :
  internal_lam f · internal_precomp g Z = internal_lam (X ⊗^{V}_{l} g · f).
Proof.
  unfold internal_lam.
  refine (assoc' _ _ _ @ _).
  rewrite hom_onmorphisms_is_postcomp.
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural V _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp Y2 _ _ @ _).
  apply pathsinv0.
  apply hom_onmorphisms_is_postcomp.
Qed.

Lemma internal_lam_postcomp {V : sym_mon_closed_cat} {X Y Z1 Z2 : ob V} (f : V⟦X ⊗_{V} Y, Z1⟧) (g : V⟦Z1, Z2⟧) :
  internal_lam f · internal_postcomp Y g = internal_lam (f · g).
Proof.
  unfold internal_lam.
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  exact (! functor_comp (pr1 (pr2 V Y)) _ _).
Qed.

Lemma sym_mon_braiding_tensor_associator (V : sym_monoidal_cat) (X Y Z : ob V) :
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

Lemma rightunitors_eval_expand1 {C : sym_mon_closed_cat} (X : ob C) :
  ruinv_{C} (internal_hom (I_{C}) X) · counit_from_are_adjoints (pr2 ((pr2 C) (I_{C}))) X · unit_from_are_adjoints (pr2 ((pr2 C) (I_{C}))) X · # (pr1 ((pr2 C) (I_{C}))) (ru_{C} X) = identity (internal_hom (I_{C}) X).
Proof.
  refine (maponpaths (postcompose _) (assoc' _ _ _) @ _).
  set (unitnateq := pr2 (pr112 ((pr2 C) (I_{C}))) _ _ (counit_from_are_adjoints (pr2 ((pr2 C) (I_{C}))) X)).
  refine (maponpaths (λ f, _ · f · _) unitnateq @ _); clear unitnateq.
  rewrite assoc.
  rewrite assoc'.
  set (unitnateq := pr2 (pr112 ((pr2 C) (I_{C}))) _ _ (ruinv_{C} (internal_hom (I_{C}) X))).
  refine (maponpaths (postcompose _) unitnateq @ _); clear unitnateq.
  unfold postcompose.
  unfold internal_hom.
  rewrite <- (triangle_id_right_ad (pr2 (pr2 C I_{ C}))).
  rewrite assoc'.
  apply maponpaths.
  simpl.
  repeat rewrite <- functor_comp.
  apply maponpaths.
  refine (_ @ pr1 (pr121 (pr111 C)) _ _ _).
  set (bif := monoidal_tensor_is_bifunctor C).
  rewrite <- (pr12 bif).
  refine (_ @ maponpaths (λ f, f ⊗^{ C}_{r} I_{ C} · _) (pr2 ((monoidal_rightunitorisolaw C) _))).
  rewrite (pr1 (pr222 bif)).
  refine (_ @ assoc _ _ _ ).
  apply (maponpaths (compose _)).
  refine (monoidal_rightunitornat C _ _ (counit_from_are_adjoints (pr2 (pr2 C I_{ C})) X) @ _).
  apply (maponpaths (postcompose _)).
  show_id_type.
  apply pathsinv0.
  refine (! id_right _ @ _ @ id_right _).
  rewrite <- (pr1 (monoidal_rightunitorisolaw C _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  exact (monoidal_rightunitornat C _ _ (ru_{C} _)).
Qed.

Lemma rightunitors_eval_expand2 {E : sym_mon_closed_cat} (X : ob E) :
  identity X =
    pr1 (unit_from_are_adjoints (pr2 (pr2 E I_{ E}))) X · internal_postcomp I_{ E} ru^{ E }_{ X} · ruinv^{ E }_{ pr1 (pr2 E I_{ E}) X} · pr1 (counit_from_are_adjoints (pr2 (pr2 E I_{ E}))) X.
Proof.
  refine (_ @ maponpaths (λ f, f · _) (assoc _ _ _)).
  refine (_ @ maponpaths (λ f, _ · f · _) (monoidal_rightunitorinvnat E _ _ (internal_postcomp I_{ E} ru^{ E }_{ X}))).
  refine (_ @ maponpaths (λ f, f · _) (assoc' _ _ _)).
  rewrite assoc'.
  refine (_ @ maponpaths (λ f, f · _) (monoidal_rightunitorinvnat E _ _ (pr1 (unit_from_are_adjoints (pr2 (pr2 E I_{ E}))) X))).
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (_ @ ! maponpaths (compose _) (pr2 (counit_from_are_adjoints (pr2 (pr2 E I_{ E}))) _ _ (ru^{E}_{X}))).
  simpl.
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  Print triangle_id_left_ad.
  refine (_ @ ! maponpaths (λ f, _ · (f · _)) (triangle_id_left_ad (pr2 (pr2 E I_{ E})) _)).
  rewrite id_left.
  exact (! pr2 (monoidal_rightunitorisolaw E X)).
Qed.

Lemma internal_swap_arg_nat1 {V : sym_mon_closed_cat} (y z : ob V) : ∏ (x1 x2 : V) (f : V ⟦ x1, x2 ⟧),
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
  apply (mon_closed_adj_natural_co V _ _ _ f).
Qed.

Lemma internal_swap_arg_nat2 {V : sym_mon_closed_cat} (x z : ob V) : ∏ (y1 y2 : V) (f : V ⟦ y1, y2 ⟧),
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
  apply (mon_closed_adj_natural_co V).
Qed.

Lemma internal_swap_arg_nat3 {V : sym_mon_closed_cat} (x y : ob V) : ∏ (z1 z2 : V) (f : V ⟦ z1, z2 ⟧),
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

Definition eqtype {A : UU} {a b : A} (eq : a=b) : UU := A.
  
Lemma curry_swap {V : sym_mon_closed_cat} (X Y Z : ob V) :
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
    
Lemma curry_nat3 {V : sym_mon_closed_cat} (X Y : ob V) {Z1 Z2 : ob V} (f : V⟦Z1, Z2⟧) :
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

Lemma curry_nat12 {V : sym_mon_closed_cat} {X1 X2 Y1 Y2 : ob V} (Z : ob V) (f : V⟦X1, X2⟧) (g : V⟦Y1, Y2⟧) :
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

Lemma curry_unit {V : sym_mon_closed_cat} (X Y Z : ob V) :
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
                                                
Lemma uncurry_swap {V : sym_mon_closed_cat} (X Y Z : ob V) :
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
    
Lemma uncurry_nat3 {V : sym_mon_closed_cat} (X Y : ob V) {Z1 Z2 : ob V} (f : V⟦Z1, Z2⟧) :
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

Lemma uncurry_nat12 {V : sym_mon_closed_cat} {X1 X2 Y1 Y2 : ob V} (Z : ob V) (f : V⟦X1, X2⟧) (g : V⟦Y1, Y2⟧) :
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

Lemma uncurry_unit {V : sym_mon_closed_cat} (X Y Z : ob V) :
  unit_from_are_adjoints (pr2 (pr2 V X)) Z · internal_postcomp X (unit_from_are_adjoints (pr2 (pr2 V Y)) (Z ⊗_{V} X)) · internal_uncurry X Y _ =
    unit_from_are_adjoints (pr2 (pr2 V (X ⊗_{V} Y))) Z · (internal_postcomp (X ⊗_{V} Y) (αinv^{V}_{Z, X, Y})).
Proof. (*follows from curry_unit *)
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


Lemma internal_swap_arg_involution {V : sym_mon_closed_cat} (X Y Z : ob V) : internal_swap_arg X Y Z · internal_swap_arg _ _ _ = identity _.
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
  refine (! maponpaths (λ f, internal_lam (_ · ((_ · f) ⊗^{V}_{r} _ · _))) (internal_eval_nat _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · (f ⊗^{V}_{r} _ · _))) (assoc _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · ((f · _) ⊗^{V}_{r} _ · _))) (triangle_id_left_ad (pr2 (pr2 V _)) _) @ _).
  rewrite id_left.
  refine (maponpaths (λ f, internal_lam (_ · (f · _))) (bifunctor_rightcomp V _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, internal_lam (_ · f)) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, internal_lam (_ · (_ · f))) (internal_eval_nat _ _ _ _) @ _).
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

Lemma curry_counit {V : sym_mon_closed_cat} (W X Z : ob V) :
  (internal_curry W X Z ⊗^{ V}_{r} W · internal_eval W (internal_hom X Z)) ⊗^{ V}_{r} X
  · internal_eval X Z = α^{ V }_{ internal_hom (W ⊗_{ V} X) Z, W, X} · internal_eval (W ⊗_{ V} X) Z.
Proof.
  unfold internal_curry.
  refine (maponpaths (λ f, f ⊗^{ V}_{r} X · _) (internal_lam_tensor_eval _) @ _).
  apply internal_lam_tensor_eval.
Qed.

Lemma uncurry_counit {V : sym_mon_closed_cat} (X Y Z : ob V) :
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

Lemma internal_uncurry_runitor {V : sym_mon_closed_cat} (X Y: ob V) :
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
  refine (! maponpaths (λ f, internal_lam (_ · (f ⊗^{V}_{r} _ · _))) (internal_eval_nat _ _ _ _) @ _).
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

Lemma internal_lam_uncurry {V : sym_mon_closed_cat} {W X Y Z : ob V} (f : V⟦(W ⊗_{V} X) ⊗_{V} Y, Z⟧) :
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

Lemma internal_uncurry_uncurry {V : sym_mon_closed_cat} (W X Y Z : ob V) :
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

Lemma internal_swap_tensor_curry {V : sym_mon_closed_cat} (W X Y Z : ob V) :
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
  refine (_ @ maponpaths (λ f, _ · internal_lam (_ · (f ⊗^{ V}_{r} Y · _)) ⊗^{V}_{r} _ · _) (internal_eval_nat _ _ _ _)).
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

Lemma internal_uncurry_tensor_swap {V : sym_mon_closed_cat} (W X Y Z : ob V) :
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

Lemma curry_nat1 {V : sym_mon_closed_cat} {X1 X2 : ob V} (Y Z : ob V) (f : V⟦X2, X1⟧) :
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
  refine (maponpaths (compose _) (! mon_closed_adj_natural_co V _ _ _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  exact (monoidal_associatornatright V _ _ _ _ _).
Qed.

Lemma curry_nat2 {V : sym_mon_closed_cat} {Y1 Y2 : ob V} (X Z : ob V) (f : V⟦Y2, Y1⟧) :
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
  refine (maponpaths (compose _) (! mon_closed_adj_natural_co V _ _ _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  exact (monoidal_associatornatright V _ _ _ _ _).
Qed.

Lemma internal_curry_curry  {V : sym_mon_closed_cat} (W X Y Z : ob V) :
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
  refine (maponpaths (compose _) (mon_closed_adj_natural_co V _ _ _ _) @ _).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  apply monoidal_pentagonidentity.
Qed.

Lemma internal_swap_arg_unit_tensor {V : sym_mon_closed_cat} (X Y Z : ob V) :
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
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural V _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite <- curry_nat3.
  rewrite assoc.
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply internal_postcomp_comp.
Qed.  
  
Lemma internal_swap_arg_unit {V : sym_mon_closed_cat} (X Y Z : ob V) :
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

                                                                         
Lemma internal_lam_lam_swap {V : sym_mon_closed_cat} {W X Y Z : ob V} (f : V⟦W ⊗_{V} X ⊗_{V} Y, Z⟧) :
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

Lemma internal_lam_curry {V : sym_mon_closed_cat} {W X Y Z : ob V} (f : V⟦W ⊗_{V} (X ⊗_{V} Y), Z⟧) :
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

