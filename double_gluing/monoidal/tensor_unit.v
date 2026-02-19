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


  (*
Definition double_glued_ill_category {E C : sym_mon_closed_cat} (L : lax_monoidal_functor C E) (K : functor C (E^opp)) : disp_cat C :=
  double_glued_cat L K. *)

Definition tensor_doublePullback_statement {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) : UU.
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')).
  destruct dr2 as ((U2, l2), (X2, l2')).
  use doublePullback.
  exact E.
  exact (internal_hom U1 X2).
  exact (internal_hom U1 (K R2)).
  exact (K (R1 ⊗_{C} R2)).
  exact (internal_hom U2 (K R1)).
  exact (internal_hom U2 X1).
  assumption.
  exact (internal_postcomp U1 l2').
  apply (compose (internal_lam (sym_mon_braiding E _ _ · (pr1 k R1 R2)))).
  exact (internal_precomp l1 _).
  apply (compose (C:=E) (# K (sym_mon_braiding C R2 R1))).
  apply (compose (C:=E) (internal_lam ((pr121 E (K (R2 ⊗_{C} R1)) (L R2)) · (pr1 k R2 R1)))).
  exact (internal_precomp l2 _).
  exact (internal_postcomp U2 l1').
Defined.

Definition tensor_doublePullback {C E : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) : tensor_doublePullback_statement pb k dr1 dr2.
Proof.
  apply pb.
Defined.

Definition double_glued_tensor_product {C E : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) : ∏ x y : ob C, double_glued_cat L K x → double_glued_cat L K y → double_glued_cat L K (x ⊗_{ pr211 C} y).
Proof.
  intros R S.
  intros ((U, l), (X, l')) ((V, m), (Y, m')).
  (* Displayed tensored object : *)
  split.
  (* Component 1 : *)
  exists (U ⊗_{E} V).
  exact (compose (l ⊗^{E} m) (pr112 L R S)).
  (* Component 2 : *)
  set (P:= tensor_doublePullback pb k ((U,, l),, (X,, l')) ((V,, m),, (Y,, m'))).
  exists (pr11 P).
  exact (doublePullbackPrM P).
Defined.

Lemma double_glued_leftwhiskering_eq1 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f23 : C⟦R2, R3⟧} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2)
  (dr3 : double_glued_cat L K R3) (df23 : dr2 -->[ f23] dr3):
  double_glued_mor_eq1 L K (R1 ⊗_{C} R2) (R1 ⊗_{C} R3) (double_glued_tensor_product pb L K k _ _ dr1 dr2) (double_glued_tensor_product pb L K k _ _ dr1 dr3) (R1 ⊗^{C}_{l} f23) (_ ⊗^{E}_{l} (pr11 df23)).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df23 as ((ϕ23, eqphi), (ψ23, eqpsi)). (* displayed morphism over f23 *)
  apply (λ eq, eq @ (pr1 (pr221 (pr111 E)) _ _ _ _ (l1 ⊗^{ E} l2) ((pr112 L) R1 R2) (# L (R1 ⊗^{ pr211 C}_{l} f23)))).
  apply (λ eq, eq @ (maponpaths (compose (l1 ⊗^{ E} l2)) (pr1 (pr22 L) R1 _ _ f23))).
  apply (λ eq, eq @ (pr2 (pr221 (pr111 E)) _ _ _ _ (l1 ⊗^{ E} l2) (pr1 L R1 ⊗^{ E}_{l} # (pr1 L) f23) ((pr112 L) R1 R3))).
  apply (λ eq, (pr1 (pr221 (pr111 E)) _ _ _ _ (U1 ⊗^{ pr112 (pr11 E)}_{l} ϕ23) (l1 ⊗^{E} l3) ((pr112 L) R1 R3)) @ eq).
  apply (maponpaths (postcompose ((pr112 L) R1 R3))).
  assert (U1 ⊗^{ pr112 (pr11 E)}_{l} ϕ23 · l1 ⊗^{ E} l3 = l1 ⊗^{E} (ϕ23 · l3)) as eq1.
  apply (λ eq, eq @ !(pr222 (pr212 (pr211 E)) _ _ _ _ l1 (ϕ23 · l3))).
  set (eqcompr := pr12 (pr212 (pr211 E)) U1 _ _ _ ϕ23 l3).
  set (eqcompr' := maponpaths (postcompose (l1 ⊗^{ pr121 (pr1 E)}_{r} L R3)) eqcompr).
  apply (λ eq, eq @ !eqcompr').
  set (eqassoc := pr1 (pr221 (pr111 E)) _ _ _ _ (U1 ⊗^{ pr112 (pr11 E)}_{l} ϕ23) (U1 ⊗^{ pr121 (pr1 E)}_{l} l3) (l1 ⊗^{ pr121 (pr1 E)}_{r} L R3)).
  apply (λ eq, eq @ eqassoc).
  apply (maponpaths (compose _)).
  exact (pr222 (pr212 (pr211 E)) _ _ _ _ _ _).
  apply (λ eq, eq1 @ eq).
  induction (! eqphi).
  apply (λ eq, pr222 (pr212 (pr211 E)) _ _ _ _ l1 (l2 · # L f23) @ eq).
  apply (λ eq, maponpaths (postcompose (l1 ⊗^{ pr121 (pr1 E)}_{r} L R3)) (pr12 (pr212 (pr211 E)) U1 _ _ _ l2 (#L f23)) @ eq).
  apply (λ eq, eq @ (maponpaths (postcompose (pr1 L R1 ⊗^{ E}_{l} # (pr1 L) f23)) (! pr222 (pr212 (pr211 E)) _ _ _ _ l1 l2))).
  apply (λ eq, eq @ (pr1 (pr221 (pr111 E)) _ _ _ _ (U1 ⊗^{ pr121 (pr1 E)}_{l} l2) (l1 ⊗^{ pr121 (pr1 E)}_{r} L R2) (pr1 L R1 ⊗^{ E}_{l} # (pr1 L) f23))).
  apply (λ eq, (pr2 (pr221 (pr111 E)) _ _ _ _ (U1 ⊗^{ pr121 (pr1 E)}_{l} l2) (U1 ⊗^{ pr121 (pr1 E)}_{l} # L f23) (l1 ⊗^{ pr121 (pr1 E)}_{r} L R3)) @ eq).
  apply (maponpaths (compose (U1 ⊗^{ pr121 (pr1 E)}_{l} l2))).
  exact (!(pr222 (pr212 (pr211 E)) _ _ _ _ l1 (#L f23))).
Qed.

Local Definition double_glued_leftwhiskering_eqs2_statement {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f23 : C⟦R2, R3⟧} (d1 : double_glued_cat L K R1)
  (d2 : double_glued_cat L K R2) (d3 : double_glued_cat L K R3) (df23 : d2 -->[ f23] d3): UU.
Proof.
  destruct d1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct d2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct d3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df23 as ((ϕ23, eqphi), (ψ23, eqpsi)). (* displayed morphism over f23 *)
  set (Pb13 := doublePullback_exists pb (internal_postcomp U1 l3')
            (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3))
            (compose (C:=E) (# K ((pr121 C) R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1)) · internal_precomp l3 (K R1))
            (internal_postcomp U3 l1')).
  set (Pb131 := pb (internal_hom U1 (K R3)) (internal_hom U1 X3) (K (R1 ⊗_{ C} R3)) (internal_postcomp U1 l3')
                   (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3))).
  set (Pb132 := pb (internal_hom U3 (K R1)) (K (R1 ⊗_{ C} R3)) (internal_hom U3 X1)
                ((compose (C:=E) (# K ((pr121 C) R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1))) · internal_precomp l3 (K R1))
                (internal_postcomp U3 l1')).
  set (h1 := (pr121 Pb13) · (pr121 Pb131) · (internal_postcomp U1 ψ23)).
  set (h2 := (pr121 Pb13) · (pr221 Pb131) · (#K (R1 ⊗^{ pr121 (pr1 C)}_{l} f23))).
  set (h3 := (pr221 Pb13) · (pr221 Pb132) · (internal_precomp ϕ23 X1)).
  refine (_ × _).
  exact (h1 · internal_postcomp U1 l2' = h2 · (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2))).
  exact (h2 · (compose (C:=E) (# K ((pr121 C) R2 R1)) (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1)) · internal_precomp l2 (K R1)) =
    h3 · internal_postcomp U2 l1').
Defined.

Local Lemma double_glued_leftwhiskering_eqs2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f23 : C⟦R2, R3⟧} (d1 : double_glued_cat L K R1)
  (d2 : double_glued_cat L K R2) (d3 : double_glued_cat L K R3) (df23 : d2 -->[ f23] d3) :
  double_glued_leftwhiskering_eqs2_statement pb k d1 d2 d3 df23.
Proof.
  destruct d1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct d2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct d3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df23 as ((ϕ23, eqphi), (ψ23, eqpsi)). (* displayed morphism over f23 *)
  set (Pb13 := doublePullback_exists pb (internal_postcomp U1 l3')
            (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3))
            (compose (C:=E) (# K ((pr121 C) R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1)) · internal_precomp l3 (K R1))
            (internal_postcomp U3 l1')).
  set (Pb131 := pb (internal_hom U1 (K R3)) (internal_hom U1 X3) (K (R1 ⊗_{ C} R3)) (internal_postcomp U1 l3')
                   (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3))).
  set (Pb132 := pb (internal_hom U3 (K R1)) (K (R1 ⊗_{ C} R3)) (internal_hom U3 X1)
                ((compose (C:=E) (# K ((pr121 C) R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1))) · internal_precomp l3 (K R1))
                (internal_postcomp U3 l1')).
  split.
  set (eqass := maponpaths (postcompose (internal_postcomp U1 l2')) (pr1 (pr221 (pr111 E)) _ _ _ _ (pr121 Pb13) (pr121 Pb131) (internal_postcomp U1 ψ23))).
  refine (!eqass @ _); clear eqass.
  refine (!pr1 (pr221 (pr111 E)) _ _ _ _ (pr121 Pb13) (pr121 Pb131 · internal_postcomp U1 ψ23) (internal_postcomp U1 l2') @ _).
  set (eqass := pr1 (pr221 (pr111 E)) _ _ _ _ (pr121 Pb13) (pr221 Pb131) (# K (R1 ⊗^{ pr121 (pr1 C)}_{l} f23))).
  refine (_ @ (maponpaths (postcompose (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2))) eqass)); clear eqass.
  refine (_ @ pr1 (pr221 (pr111 E)) _ _ _ _ (pr121 Pb13) (pr221 Pb131 · # K (R1 ⊗^{ pr121 (pr1 C)}_{l} f23)) (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2))).
  apply (maponpaths (compose (pr121 Pb13))).
  refine (!pr1 (pr221 (pr111 E)) _ _ _ _ (pr121 Pb131) (internal_postcomp U1 ψ23) (internal_postcomp U1 l2') @ _).
  refine ((maponpaths (compose (pr121 Pb131)) (! internal_postcomp_comp U1 ψ23 l2')) @ _).
  refine ((maponpaths (λ f, pr121 Pb131 · internal_postcomp U1 f) (! eqpsi) ) @ _).
  refine ((maponpaths (compose (pr121 Pb131)) (internal_postcomp_comp U1 l3' (#K f23))) @ _).
  refine (pr1 (pr221 (pr111 E)) _ _ _ _ (pr121 Pb131) (internal_postcomp U1 l3') (internal_postcomp U1 (#K f23)) @ _).
  refine (maponpaths (postcompose (internal_postcomp U1 (# K f23))) (pr12 Pb131) @ _).
  refine (! (pr1 (pr221 (pr111 E)) _ _ _ _ (pr221 Pb131) (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3)) (internal_postcomp U1 (# K f23))) @ _).
  refine (_ @ (pr1 (pr221 (pr111 E)) _ _ _ _ (pr221 Pb131) (# K (R1 ⊗^{ pr121 (pr1 C)}_{l} f23)) (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2)))).
  apply (maponpaths (compose (pr221 Pb131))).
  assert (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · (internal_postcomp (L R1) (#K f23)) =
            compose (C:=E) (# K (R1 ⊗^{ pr121 (pr1 C)}_{l} f23)) (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2))) as eq.
  set (ck:= curried_contraction k).
  generalize (curried_contraction_isnat k (R1,,R2) (R1,,R3) (identity R1,, f23)); simpl.
  unfold functoronmorphisms1;
    unfold compose_functor_with_bifunctor_data, lolli_bifunctor, lolli_bifunctor_data; simpl.
  unfold rightwhiskering_on_morphisms, leftwhiskering_on_morphisms; simpl.
  unfold curried_contraction; simpl; intros cknateq.
  refine (_ @ cknateq @ _).
  assert ((# L (identity R1)) = identity (L R1)) as ideq.
  exact (pr121 L R1).
  induction (! ideq); clear ideq.
  set (precompeq := maponpaths (postcompose (internal_postcomp (L R1) (# K f23))) (internal_precomp_id (L R1) (K R3))).
  refine (_ @ !  maponpaths (compose (φ_adj (pr2 (pr2 E (L R1))) ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3))) precompeq); clear precompeq.
  set (ideq := pr1 (pr121 (E ^opp)) _ _ ( internal_postcomp (L R1) (# K f23))).
  refine (! (maponpaths (postcompose (C:= E ^opp) (φ_adj (pr2 (pr2 E (L R1))) (compose (C:=E) ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1)) (pr1 k R1 R3)))) ideq) @ _); clear ideq.
  apply (maponpaths (compose (φ_adj (pr2 (pr2 E (L R1))) (compose (C:=E) ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1)) (pr1 k R1 R3))))).
  exact (id_right _ @ ! id_left _).
  unfold compose, opp_precat_data; simpl.
  change (compose (C:=E) (# K (R1 ⊗^{ pr121 (pr1 C)}_{l} f23)) (# K (identity R1 ⊗^{ pr121 (pr1 C)}_{r} R2))
  · φ_adj (pr2 (pr2 E (L R1)))
      (compose (C:=E) ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1)) (pr1 k R1 R2)) =
  compose (C:=E) (# K (leftwhiskering_on_morphisms C R1 _ _ f23))
    (internal_lam
       (compose (C:=E) ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1)) (pr1 k R1 R2)))).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose (C:=E) (# K (R1 ⊗^{ pr121 (pr1 C)}_{l} f23)))).
  set (kideq := maponpaths (# K) (pr12 (monoidal_tensor_is_bifunctor C) R2 R1)).
  refine (maponpaths ((postcompose (C:=E) (φ_adj (pr2 (pr2 E (L R1))) ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2)))) kideq @ _).
  refine (maponpaths (postcompose (φ_adj (pr2 (pr2 E (L R1))) ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2))) (pr12 K (R1 ⊗_{ C} R2)) @ _).
  exact (id_left _).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose (internal_precomp l1 (K R2))) eq); clear eq.
  unfold postcompose.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  exact (! internal_pre_post_comp_as_pre_post_comp _ _ @ internal_pre_post_comp_as_post_pre_comp _ _).
  set (pbeq := maponpaths (postcompose (C:=E) (# K (R1 ⊗^{ pr121 (pr1 C)}_{l} f23))) (pr12 Pb13)).
  refine (maponpaths (postcompose _) pbeq @ _); clear pbeq.
  unfold postcompose.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (compose (pr221 Pb13))).
  refine (_ @ maponpaths (compose _) (internal_pre_post_comp_as_pre_post_comp _ _ )).
  refine (_ @ maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose _) (pr12 Pb132)).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (compose (pr121 Pb132))).
  refine (_ @ assoc _ _ (internal_precomp ϕ23 (K R1))).
  induction (internal_precomp_comp ϕ23 l3 (K R1)).
  revert eqphi; simpl; intros eqphi.
  induction (! eqphi).
  refine (_ @ ! maponpaths (compose _) (internal_precomp_comp l2 (# L f23) (K R1))).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose (internal_precomp l2 (K R1)))).
  set (cknateq := curried_contraction_isnat k (R2,,R1) (R3,,R1) (f23,, identity R1)).
  assert ((pr112 (pr2 E (L R3))) (K (R3 ⊗_{ C} R1)) · # (pr1 (pr2 E (L R3))) ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1)
            · (internal_precomp (# L f23) (K R1) · internal_postcomp (L R2) (# K (identity R1))) = (pr112 (pr2 E (L R3))) (K (R3 ⊗_{ C} R1)) · # (pr1 (pr2 E (L R3))) ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1)
            · (internal_precomp (# L f23) (K R1))) as eq1.
  apply (maponpaths (compose _)).
  refine (_ @ pr2 (pr121 (pr111 E)) _ _ _).
  apply (maponpaths (compose _)).
  refine (_ @ internal_postcomp_id _ _).
  apply (maponpaths (internal_postcomp (L R2))).
  exact (functor_id K R1).
  assert (compose (C:=E) (# K (f23 ⊗^{ pr121 (pr1 C)}_{r} R1))
            ((pr112 (pr2 E (L R2))) (K (R2 ⊗_{ C} R1)) · # (pr1 (pr2 E (L R2))) ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1)) =
            compose (C:=E) (compose (C:=E) (# K (R3 ⊗^{ pr121 (pr1 C)}_{l} identity R1)) (# K (f23 ⊗^{ pr121 (pr1 C)}_{r} R1)))
              ((pr112 (pr2 E (L R2))) (K (R2 ⊗_{ C} R1)) · # (pr1 (pr2 E (L R2))) ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1))) as eq2.
  apply (maponpaths (postcompose _)).
  refine (! pr1 (pr121 (pr111 E)) _ _ _ @ _).
  apply (maponpaths (compose (# K (f23 ⊗^{ pr121 (pr1 C)}_{r} R1)))).
  refine (! functor_id K _ @ _).
  apply (maponpaths (#K)).
  exact (! pr112 (pr211 C) _ _).
  set (cknateq2 := ! eq1 @ cknateq @ ! eq2).
  refine (_ @ assoc _ _ _).
  refine (_ @ ! maponpaths (compose (C:=E) (# K ((pr121 C) R3 R1))) cknateq2).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose (C:=E) (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1)))).
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply (maponpaths (# K)).
  exact (pr21 (pr221 C) R2 R3 R1 f23).
Qed.

Local Lemma double_glued_leftwhiskering_lemma2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f23 : C⟦R2, R3⟧} {U1 U2 U3 X1 X2 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧)
  (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (ϕ23 : double_glued_mor_comp1 L K R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))
  (eqphi : double_glued_mor_eq1 L K R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3') f23 ϕ23)
  (ψ23 : double_glued_mor_comp2 L K R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))
  (eqpsi : double_glued_mor_eq2 L K R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3') f23 ψ23) :
  doublePullbackPrL (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U3,, l3),, X3,, l3')) · internal_postcomp U1 ψ23 · internal_postcomp U1 l2' =
  doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U3,, l3),, X3,, l3')) · # K (R1 ⊗^{ C}_{l} f23)
    · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2)).
Proof.
  unfold double_glued_mor_comp1, double_glued_mor_eq1, double_glued_mor_comp2, double_glued_mor_eq2 in *.
  rewrite assoc'.
  refine (! maponpaths (compose _) (internal_postcomp_comp U1 _ _) @ _).
  show_id_type.
  revert eqpsi; simpl; intros eqpsi.
  refine (! maponpaths (λ f, compose (C:=E) _ (internal_postcomp U1 f)) eqpsi @ _).
  refine (maponpaths (compose _) (internal_postcomp_comp U1 _ _) @ _).
  refine (assoc (C:=E) _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U3,, l3),, X3,, l3'))) @ _).
  do 3 rewrite assoc'.
  apply maponpaths.
  refine (! maponpaths (compose _) (internal_pre_post_comp_as_pre_post_comp _ _ ) @ _).
  refine (maponpaths (compose _) (internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  do 2 rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (_ @ ! internal_lam_natural _ _).
  unfold monoidal_cat_tensor_mor, functoronmorphisms1.
  rewrite (bifunctor_leftid E (K (R1 ⊗_{ C} R2))).
  rewrite id_right.
  unfold internal_lam; simpl.
  repeat rewrite assoc'.
  apply maponpaths.
  do 2 rewrite hom_onmorphisms_is_postcomp.
  refine (! internal_postcomp_comp (L R1) _ _ @ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  do 2 rewrite assoc'.
  apply maponpaths.
  exact (! pr12 k R1 _ _ f23).
Qed.

Local Lemma double_glued_leftwhiskering_lemma3 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f23 : C⟦R2, R3⟧} {U1 U2 U3 X1 X2 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧)
  (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (ϕ23 : double_glued_mor_comp1 L K R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))
  (eqphi : double_glued_mor_eq1 L K R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3') f23 ϕ23)
  (ψ23 : double_glued_mor_comp2 L K R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))
  (eqpsi : double_glued_mor_eq2 L K R2 R3 ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3') f23 ψ23) :
  doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U3,, l3),, X3,, l3')) · # K (R1 ⊗^{ C}_{l} f23)
    · (compose (C:=E) (# K (sym_mon_braiding C R2 R1))
         (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1) · internal_precomp l2 (K R1))) =
    doublePullbackPrR (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U3,, l3),, X3,, l3')) · internal_precomp ϕ23 X1
      · internal_postcomp U2 l1'.
Proof.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (internal_pre_post_comp_as_pre_post_comp _ _ )).
  refine (_ @ ! maponpaths (compose _) (internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ assoc' _ _ _).
  rewrite <- (doublePullbackSqrRCommutes (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U3,, l3),, X3,, l3'))).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite <- internal_precomp_comp.
  rewrite eqphi.
  rewrite internal_precomp_comp.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) (# K f) _) (monoidal_braiding_naturality_right C _ _ _ _) @ _).
  rewrite (functor_comp K).
  refine (assoc' (C:=E) _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (internal_lam_natural _ _ @ _).
  unfold internal_lam.
  repeat rewrite assoc'.
  do 2 rewrite hom_onmorphisms_is_postcomp.
  unfold monoidal_cat_tensor_mor, functoronmorphisms1.
  rewrite (bifunctor_leftid E).
  rewrite id_right.
  refine (_ @ maponpaths (compose _) (internal_pre_post_comp_as_post_pre_comp _ _ )).
  refine (_ @ ! maponpaths (compose _) (internal_pre_post_comp_as_pre_post_comp _ _ )).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (mon_closed_adj_natural E (K (R3 ⊗_{ C} R1)) (L R2) (L R3) (# L f23))).
  rewrite assoc'.
  apply maponpaths.
  refine (_ @ internal_postcomp_comp (L R2) _ _).
  apply maponpaths.
  do 2 rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) (monoidal_braiding_naturality_left E _ _ _ _)).
  do 2 rewrite assoc'.
  apply maponpaths.
  generalize (pr122 k R1 _ _ f23); unfold rightwhiskering_on_morphisms, leftwhiskering_on_morphisms; simpl.
  do 2 rewrite id_right.
  exact (idfun _).
Qed.

Definition double_glued_leftwhiskering_comp2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  {f23 : C⟦R2, R3⟧} (df23 : dr2 -->[f23] dr3 ):
  double_glued_mor_comp2 L K (R1 ⊗_{ pr211 C} R2) (R1 ⊗_{ pr211 C} R3)
    (double_glued_tensor_product pb L K k R1 R2 dr1 dr2)
    (double_glued_tensor_product pb L K k R1 R3 dr1 dr3).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df23 as ((ϕ23, eqphi), (ψ23, eqpsi)).
  use doublePullbackArrow.
  apply (compose (doublePullbackPrL _)).
  exact (internal_postcomp U1 ψ23).
  apply (compose (doublePullbackPrM _)).
  exact (# K (R1 ⊗^{C}_{l} f23)).
  apply (compose (doublePullbackPrR _)).
  exact (internal_precomp ϕ23 X1).
  exact (double_glued_leftwhiskering_lemma2 pb k l1 l1' l2 l2' l3 l3' ϕ23 eqphi ψ23 eqpsi).
  exact (double_glued_leftwhiskering_lemma3 pb k l1 l1' l2 l2' l3 l3' ϕ23 eqphi ψ23 eqpsi).
Defined.

Lemma double_glued_leftwhiskering_eq2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  {f23 : C⟦R2, R3⟧} (df23 : dr2 -->[f23] dr3 ):
  double_glued_mor_eq2 L K _ _ _ _ (R1 ⊗^{C}_{l} f23) (double_glued_leftwhiskering_comp2 pb k dr1 dr2 dr3 df23).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df23 as ((ϕ23, eqphi), (ψ23, eqpsi)).
  unfold double_glued_mor_eq2; simpl.
  change (compose (C:=E) (doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U3,, l3),, X3,, l3'))) (# K (R1 ⊗^{ pr211 C}_{l} f23)) =
            compose (C:=E) (double_glued_leftwhiskering_comp2 pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')
                              ((ϕ23,, eqphi),, ψ23,, eqpsi))
              (doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2')))).
  unfold double_glued_leftwhiskering_comp2.
  rewrite (doublePullbackArrow_PrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))).
  reflexivity.
Qed.

Definition double_glued_leftwhiskering {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) :
  ∏ (x y1 y2 : pr111 C) (g : pr111 C ⟦ y1, y2 ⟧) (xx : double_glued_cat L K x) (yy1 : double_glued_cat L K y1)
   (yy2 : double_glued_cat L K y2),
    yy1 -->[ g] yy2 → double_glued_tensor_product pb L K k x y1 xx yy1 -->[ x ⊗^{ pr211 C}_{l} g] double_glued_tensor_product pb L K k x y2 xx yy2.
Proof.
(* leftwhiskering : *)
  intros R1 R2 R3 f23. (* base objects and morphism *)
  intros dr1 dr2 dr3 df23. (* displayed objects and morphism *)
  split.
  (* leftwhiskering component 1 : *)
  exists (leftwhiskering_on_morphisms (pr112 (pr11 E)) _ _ _ (pr11 df23)).
  exact (double_glued_leftwhiskering_eq1 pb k dr1 dr2 dr3 df23).
  (* leftwhiskering component 2 : *)
  exists (double_glued_leftwhiskering_comp2 pb k dr1 dr2 dr3 df23).
  exact (double_glued_leftwhiskering_eq2 pb k dr1 dr2 dr3 df23).
Defined.

Local Lemma double_glued_rightwhiskering_eq1 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f12 : C⟦R1, R2⟧} (dr1 : double_glued_cat L K R1)
  (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (df12 : dr1 -->[ f12] dr2) :
  pr11 df12 ⊗^{ pr112 (pr11 E)}_{r} pr11 dr3 · pr21 (double_glued_tensor_product pb L K k R2 R3 dr2 dr3) =
    pr21 (double_glued_tensor_product pb L K k R1 R3 dr1 dr3) · # L (f12 ⊗^{ pr211 C}_{r} R3).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* displayed object over R3 *)
  destruct df12 as ((ϕ12, eqphi), (ψ12, eqpsi)). (* displayed morphism over f12 *)
  revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  simpl.
  unfold functoronmorphisms1.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (postcompose _) (assoc _ _ _) @ _).
  unfold postcompose.
  refine (! maponpaths (λ f, f · _ · _) (pr122 (pr212 (pr211 E)) U3 _ _ _ ϕ12 l2) @ _).
  refine (maponpaths (λ f, (f ⊗^{ pr121 (pr1 E)}_{r} U3) · _ · _) eqphi @ _).
  refine (maponpaths (λ f, f · _ · _) (pr122 (pr212 (pr211 E)) U3 _ _ _ l1 (# L f12)) @ _).
  repeat refine (assoc' _ _ _ @ _ @ assoc _ _ _ ).
  apply (maponpaths (compose _)).
  refine (_ @ maponpaths (compose _) (pr1 (pr222 L) R1 R2 R3 f12)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  exact (pr222 (pr212 (pr211 E)) _ _ _ _ (# L f12) l3).
Qed.

Definition double_glued_rightwhiskering_eqs2_statement {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f12 : C⟦R1, R2⟧} (dr1 : double_glued_cat L K R1)
  (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (df12 : dr1 -->[ f12] dr2): UU.
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* displayed object over R3 *)
  destruct df12 as ((ϕ12, eqphi), (ψ12, eqpsi)). (* displayed morphism over f12 *)
  set (Pb23 := doublePullback_exists pb (internal_postcomp U2 l3')
                (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R3)) (L R2) · pr1 k R2 R3) · internal_precomp l2 (K R3))
                (compose (C:=E) (# K ((pr121 C) R3 R2)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R2)) (L R3) · pr1 k R3 R2)) · internal_precomp l3 (K R2))
                (internal_postcomp U3 l2')).
  set (Pb231 := pb (internal_hom U2 (K R3)) (internal_hom U2 X3) (K (R2 ⊗_{ C} R3)) (internal_postcomp U2 l3')
                   (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R3)) (L R2) · pr1 k R2 R3) · internal_precomp l2 (K R3))).
  set (Pb232 := pb (internal_hom U3 (K R2)) (K (R2 ⊗_{ C} R3)) (internal_hom U3 X2)
                ((compose (C:=E) (# K ((pr121 C) R3 R2)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R2)) (L R3) · pr1 k R3 R2))) · internal_precomp l3 (K R2))
                (internal_postcomp U3 l2')).
  set (Pb13 := doublePullback_exists pb (internal_postcomp U1 l3')
            (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3))
            (compose (C:=E) (# K ((pr121 C) R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1)) · internal_precomp l3 (K R1))
            (internal_postcomp U3 l1')).
  set (h1 := (pr121 Pb23) · (pr121 Pb231) · (internal_precomp ϕ12 X3)).
  set (h2 := (pr121 Pb23) · (pr221 Pb231) · #K (f12 ⊗^{ pr121 (pr1 C)}_{r} R3)).
  set (h3 := (pr221 Pb23) · (pr221 Pb232) · (internal_postcomp U3 ψ12)).
  refine (_ × _).
  exact (h1 · internal_postcomp U1 l3' = h2 · (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3))).
  exact (h2 · (compose (C:=E) (# K ((pr121 C) R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1)) · internal_precomp l3 (K R1)) =
    h3 · internal_postcomp U3 l1').
Defined.

Local Lemma double_glued_rightwhiskering_eqs2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f12 : C⟦R1, R2⟧} (dr1 : double_glued_cat L K R1)
  (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (df12 : dr1 -->[ f12] dr2) :
  double_glued_rightwhiskering_eqs2_statement pb k dr1 dr2 dr3 df12.
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* displayed object over R3 *)
  destruct df12 as ((ϕ12, eqphi), (ψ12, eqpsi)). (* displayed morphism over f12 *)
  set (Pb23 := doublePullback_exists pb (internal_postcomp U2 l3')
                (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R3)) (L R2) · pr1 k R2 R3) · internal_precomp l2 (K R3))
                (compose (C:=E) (# K ((pr121 C) R3 R2)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R2)) (L R3) · pr1 k R3 R2)) · internal_precomp l3 (K R2))
                (internal_postcomp U3 l2')).
  set (Pb231 := pb (internal_hom U2 (K R3)) (internal_hom U2 X3) (K (R2 ⊗_{ C} R3)) (internal_postcomp U2 l3')
                   (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R3)) (L R2) · pr1 k R2 R3) · internal_precomp l2 (K R3))).
  set (Pb232 := pb (internal_hom U3 (K R2)) (K (R2 ⊗_{ C} R3)) (internal_hom U3 X2)
                ((compose (C:=E) (# K ((pr121 C) R3 R2)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R2)) (L R3) · pr1 k R3 R2))) · internal_precomp l3 (K R2))
                (internal_postcomp U3 l2')).
  set (Pb13 := doublePullback_exists pb (internal_postcomp U1 l3')
            (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3))
            (compose (C:=E) (# K ((pr121 C) R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1)) · internal_precomp l3 (K R1))
            (internal_postcomp U3 l1')).
  split.
  repeat refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (compose (pr121 Pb23))).
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_pre_post_comp ϕ12 l3' @ internal_pre_post_comp_as_post_pre_comp ϕ12 l3') @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  refine (maponpaths (postcompose _) (pr12 Pb231) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (compose (pr221 Pb231))).
  refine (assoc' _ _ _ @ _).
  refine (! maponpaths (compose _) (internal_precomp_comp ϕ12 l2 (K R3)) @ _).
  induction (! eqphi).
  refine (_ @ assoc' _ _ _).
  set (cknateq := curried_contraction_isnat k (R1,,R3) (R2,,R3) (f12,, identity R3)).
  assert ((pr112 (pr2 E (L R2))) (K (R2 ⊗_{ C} R3)) · # (pr1 (pr2 E (L R2))) ((pr121 E) (K (R2 ⊗_{ C} R3)) (L R2) · pr1 k R2 R3)
            · (internal_precomp (# L f12) (K R3) · internal_postcomp (L R1) (# K (identity R3))) =
            (pr112 (pr2 E (L R2))) (K (R2 ⊗_{ C} R3)) · # (pr1 (pr2 E (L R2))) ((pr121 E) (K (R2 ⊗_{ C} R3)) (L R2) · pr1 k R2 R3)·
              (internal_precomp (# L f12) (K R3))) as eq1.
  apply (maponpaths (compose _)).
  set (ideq := ! (maponpaths (internal_postcomp (L R1)) (functor_id K R3) @ internal_postcomp_id (L R1) _)).
  exact (! maponpaths (compose _) ideq @ id_right _).
  set (cknateq2 := ! eq1 @ cknateq).
  assert (compose (C:=E) (# K (R2 ⊗^{ pr121 (pr1 C)}_{l} identity R3)) (# K (f12 ⊗^{ pr121 (pr1 C)}_{r} R3))
            · ((pr112 (pr2 E (L R1))) (K (R1 ⊗_{ C} R3)) · # (pr1 (pr2 E (L R1))) ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3)) =
            compose (C:=E) (# K (f12 ⊗^{ pr121 (pr1 C)}_{r} R3))
              (((pr112 (pr2 E (L R1))) (K (R1 ⊗_{ C} R3)) · # (pr1 (pr2 E (L R1))) ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3)))) as eq2.
  apply (maponpaths (postcompose _)).
  refine (_ @ pr1 (pr121 (pr111 E)) _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ functor_id K (R2 ⊗_{ pr121 (pr1 C)} R3)).
  exact (maponpaths (#K) (pr112 (pr211 C) R2 R3)).
  refine (_ @ maponpaths (postcompose _) (cknateq2 @ eq2)).
  refine (maponpaths (compose _) (internal_precomp_comp l1 (# L f12) (K R3)) @ _).
  exact (assoc _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (postcompose _ ) (pr12 Pb23) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  refine (_ @ maponpaths (compose (pr221 Pb232)) (internal_postcomp_comp U3 ψ12 l1')).
  refine (_ @ maponpaths (λ f, compose (C:=E) (pr221 Pb232) (internal_postcomp U3 f)) eqpsi).
  refine (_ @ maponpaths (compose (pr221 Pb232)) (! internal_postcomp_comp U3 _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose _) (pr12 Pb232)).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (postcompose _) (assoc _ _ _) @ _ @ assoc _ _ _).
  refine (assoc' _ _ _ @ _).
  assert (compose (C:=E) (# K (f12 ⊗^{ C}_{r} R3)) (# K ((pr121 C) R3 R1)) = compose (C:=E) (# K ((pr121 C) R3 R2)) (# K (R3 ⊗^{ C}_{l} f12)) ) as braideq.
  refine (_ @ maponpaths (#K) (pr11 (pr221 C) R3 R1 R2 f12) @ functor_comp K _ _).
  exact (! functor_comp K _ _).
  refine (maponpaths (postcompose _) braideq @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  set (cknateq := curried_contraction_isnat k (R3,,R1) (R3,,R2) (identity R3,, f12)).
  assert (compose (C:=E) (# K (R3 ⊗^{ pr121 (pr1 C)}_{l} f12)) (# K (identity R3 ⊗^{ pr121 (pr1 C)}_{r} R1))·
            compose (C:=E) ((pr112 (pr2 E (L R3))) (K (R3 ⊗_{ C} R1)))
            (# (pr1 (pr2 E (L R3))) (compose (C:=E) ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3)) (pr1 k R3 R1))) =
            compose (C:=E) (# K (R3 ⊗^{ pr121 (pr1 C)}_{l} f12))
              (compose (C:=E) ((pr112 (pr2 E (L R3))) (K (R3 ⊗_{ C} R1)))
                 (# (pr1 (pr2 E (L R3))) (compose (C:=E) ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3)) (pr1 k R3 R1))))) as eq1.
  apply (maponpaths (postcompose _)).
  refine (_ @ pr2 (pr121 (pr111 E)) _ _ (# K (R3 ⊗^{ pr121 (pr1 C)}_{l} f12))).
  apply (maponpaths (compose _)).
  refine (_ @ functor_id K _).
  apply (maponpaths (#K)).
  exact (pr1 (pr212 (pr211 C)) R1 R3).
  assert (compose (C:=E) ((pr112 (pr2 E (L R3))) (K (R3 ⊗_{ C} R2)))
            (# (pr1 (pr2 E (L R3))) (compose (C:=E) ((pr121 E) (K (R3 ⊗_{ C} R2)) (L R3)) (pr1 k R3 R2))) ·
            compose (C:=E) (internal_precomp (# L (identity R3)) (K R2)) (internal_postcomp (L R3) (# K f12)) =
         compose (C:=E) ((pr112 (pr2 E (L R3))) (K (R3 ⊗_{ C} R2)))
           (# (pr1 (pr2 E (L R3))) (compose (C:=E) ((pr121 E) (K (R3 ⊗_{ C} R2)) (L R3)) (pr1 k R3 R2))) · (internal_postcomp (L R3) (# K f12))) as eq2.  
  apply (maponpaths (compose _)).
  refine (_ @ pr1 (pr121 (pr111 E)) _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ internal_precomp_id _ _).
  apply (maponpaths (λ f, internal_precomp f (K R2))).
  exact (functor_id L R3).
  set (cknateq2 := ! eq1 @ ! cknateq @ eq2).
  refine ( assoc _ _ _ @ _).
  refine (maponpaths (postcompose _) cknateq2 @ _).
  refine (assoc' _ _ _ @ _).
  apply (maponpaths (compose _)).
  exact (! internal_pre_post_comp_as_post_pre_comp _ _  @ internal_pre_post_comp_as_pre_post_comp _ _).
Qed.

Local Lemma double_glued_rightwhiskering_lemma1 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f12 : C⟦R1, R2⟧} {U1 U2 U3 X1 X2 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧)
  (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (ϕ12 : double_glued_mor_comp1 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))
  (eqphi : double_glued_mor_eq1 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') f12 ϕ12)
  (ψ12 : double_glued_mor_comp2 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))
  (eqpsi : double_glued_mor_eq2 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') f12 ψ12) :
  doublePullbackPrL (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')) · internal_precomp ϕ12 X3 · internal_postcomp U1 l3' =
    doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')) · # K (f12 ⊗^{ C}_{r} R3)
      · (internal_lam (sym_mon_braiding E (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3)).
Proof.
  unfold double_glued_mor_comp1, double_glued_mor_eq1, double_glued_mor_comp2, double_glued_mor_eq2 in *.
  rewrite assoc'.
  refine (! maponpaths (compose _) (internal_pre_post_comp_as_pre_post_comp _ _ ) @ _).
  refine (maponpaths (compose _) (internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  refine (assoc _ _ _ @ _).
  rewrite (doublePullbackSqrLCommutes (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))).
  do 3 rewrite assoc'.
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  rewrite (internal_lam_natural).
  unfold monoidal_cat_tensor_mor, functoronmorphisms1.
  rewrite (bifunctor_leftid E).
  rewrite id_right.
  unfold internal_lam.
  do 2 rewrite hom_onmorphisms_is_postcomp.
  rewrite <- internal_precomp_comp.
  rewrite eqphi.
  rewrite internal_precomp_comp.
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  rewrite assoc'.
  refine (! maponpaths (compose _) (internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  refine (maponpaths (compose _) (internal_pre_post_comp_as_pre_post_comp _ _ ) @ _).
  rewrite assoc.
  refine (! maponpaths (λ f, f · _) (mon_closed_adj_natural E (K (R2 ⊗_{ C} R3)) _ _ (# L f12)) @ _).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (! internal_postcomp_comp (L R1) _ _ @ _).
  apply maponpaths.
  do 2 rewrite assoc.
  refine (! maponpaths (λ f, f · _) (monoidal_braiding_naturality_left E _ _ _ _) @ _).
  refine (_ @ maponpaths (λ f, f · _) (monoidal_braiding_naturality_right E _ _ _ _)).
  repeat rewrite assoc'.
  apply maponpaths.
  generalize (pr122 k R3 _ _ f12); unfold rightwhiskering_on_morphisms, leftwhiskering_on_morphisms; simpl.
  do 2 rewrite id_right; intros keq.
  exact (! keq).
Qed.

Local Lemma double_glued_rightwhiskering_lemma2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f12 : C⟦R1, R2⟧} {U1 U2 U3 X1 X2 X3 : E} (l1 : E ⟦ U1, L R1 ⟧) (l1' : E ^opp ⟦ K R1, X1 ⟧)
  (l2 : E ⟦ U2, L R2 ⟧) (l2' : E ^opp ⟦ K R2, X2 ⟧) (l3 : E ⟦ U3, L R3 ⟧) (l3' : E ^opp ⟦ K R3, X3 ⟧)
  (ϕ12 : double_glued_mor_comp1 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))
  (eqphi : double_glued_mor_eq1 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') f12 ϕ12)
  (ψ12 : double_glued_mor_comp2 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2'))
  (eqpsi : double_glued_mor_eq2 L K R1 R2 ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') f12 ψ12) :
  doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')) · # K (f12 ⊗^{ C}_{r} R3)
    · (compose (C:=E) (# K (sym_mon_braiding C R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1) · internal_precomp l3 (K R1))) =
    doublePullbackPrR (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')) · internal_postcomp U3 ψ12 · internal_postcomp U3 l1'.
Proof.
  refine (_ @ assoc _ _ _).
  rewrite <- internal_postcomp_comp.
  refine (_ @ maponpaths (λ f, _ · internal_postcomp U3 f) eqpsi).
  refine (_ @ ! maponpaths (compose (C:=E) _) (internal_postcomp_comp U3 _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (doublePullbackSqrRCommutes (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3')))).
  repeat rewrite assoc'.
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (compose _) (! internal_pre_post_comp_as_post_pre_comp _ _  @ internal_pre_post_comp_as_pre_post_comp _ _)).
  repeat rewrite assoc.
  apply (maponpaths (postcompose _)).
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  refine (maponpaths (λ f, compose (C:=E) (# K f) _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).  
  rewrite (functor_comp K).
  refine (assoc' (C:=E) _ _ _ @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite internal_lam_natural.
  unfold monoidal_cat_tensor_mor, functoronmorphisms1; simpl.
  rewrite (bifunctor_leftid E).
  rewrite id_right.
  unfold internal_lam.
  repeat rewrite assoc'.
  apply maponpaths.
  do 2 rewrite hom_onmorphisms_is_postcomp.
  refine (_ @ internal_postcomp_comp (L R3) _ _).
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (monoidal_braiding_naturality_right E _ _ _ _) @ _).
  do 2 rewrite assoc'.
  apply maponpaths.
  exact (pr12 k R3 _ _ f12).
Qed.

Definition double_glued_rightwhiskering_comp2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  {f12 : C⟦R1, R2⟧} (df12 : dr1 -->[f12] dr2 ):
  double_glued_mor_comp2 L K (R1 ⊗_{ pr211 C} R3) (R2 ⊗_{ pr211 C} R3)
    (double_glued_tensor_product pb L K k R1 R3 dr1 dr3)
    (double_glued_tensor_product pb L K k R2 R3 dr2 dr3).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df12 as ((ϕ12, eqphi), (ψ12, eqpsi)).
  use doublePullbackArrow.
  apply (compose (doublePullbackPrL _)).
  exact (internal_precomp ϕ12 X3).
  apply (compose (doublePullbackPrM _)).
  exact (# K (f12 ⊗^{C}_{r} R3)).
  apply (compose (doublePullbackPrR _)).
  exact (internal_postcomp U3 ψ12).
  exact (double_glued_rightwhiskering_lemma1 pb k l1 l1' l2 l2' l3 l3' ϕ12 eqphi ψ12 eqpsi).
  exact (double_glued_rightwhiskering_lemma2 pb k l1 l1' l2 l2' l3 l3' ϕ12 eqphi ψ12 eqpsi).
Defined.

Lemma double_glued_rightwhiskering_eq2 {E C : sym_mon_closed_cat} (pb : Pullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  {f12 : C⟦R1, R2⟧} (df12 : dr1 -->[f12] dr2 ):
  double_glued_mor_eq2 L K _ _ _ _ (f12 ⊗^{C}_{r} R3) (double_glued_rightwhiskering_comp2 pb k dr1 dr2 dr3 df12).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df12 as ((ϕ12, eqphi), (ψ12, eqpsi)).
  unfold double_glued_mor_eq2; simpl.
  change (compose (C:=E) (doublePullbackPrM (tensor_doublePullback pb k ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3'))) (# K (f12 ⊗^{ C}_{r} R3)) =
            compose (C:=E) (double_glued_rightwhiskering_comp2 pb k ((U1,, l1),, X1,, l1') ((U2,, l2),, X2,, l2') ((U3,, l3),, X3,, l3') ((ϕ12,, eqphi),, ψ12,, eqpsi)) (doublePullbackPrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U3,, l3),, X3,, l3')))).
  unfold double_glued_rightwhiskering_comp2.
  rewrite (doublePullbackArrow_PrM (tensor_doublePullback pb k ((U1,, l1),, X1,, l1')((U3,, l3),, X3,, l3'))).
  reflexivity.
Qed.

Definition double_glued_rightwhiskering {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) :
   ∏ (x1 x2 y : pr111 C) (f : pr111 C ⟦ x1, x2 ⟧) (xx1 : double_glued_cat L K x1) (xx2 : double_glued_cat L K x2)
  (yy : double_glued_cat L K y),
  xx1 -->[ f] xx2 → double_glued_tensor_product pb L K k x1 y xx1 yy -->[ f ⊗^{ pr211 C}_{r} y] double_glued_tensor_product pb L K k x2 y xx2 yy.
Proof.
  intros R1 R2 R3 f12. (* base objects and morphism *)
  intros dr1 dr2 dr3 df12.
  split.
  exists (rightwhiskering_on_morphisms (pr112 (pr11 E)) _ _ _ (pr11 df12)).
  exact (double_glued_rightwhiskering_eq1 pb k dr1 dr2 dr3 df12).
  (* rightwhiskering component 2 : *)
  exists (double_glued_rightwhiskering_comp2 pb k dr1 dr2 dr3 df12).
  exact (double_glued_rightwhiskering_eq2 pb k dr1 dr2 dr3 df12).
Defined.

Definition double_glued_disp_bifunctor_data {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) :
  disp_bifunctor_data (pr211 C) (double_glued_cat L K) (double_glued_cat L K) (double_glued_cat L K).
Proof.
  unfold disp_bifunctor_data.
  exists (double_glued_tensor_product pb L K k).
  exists (double_glued_leftwhiskering pb L K k).
  exact (double_glued_rightwhiskering pb L K k).
Defined.

Lemma double_glued_tensor_leftidax {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): disp_bifunctor_leftidax (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2.
  intros dr1 dr2.
  apply (double_glued_mor_eq_transp _ _).
  split.
  exact (bifunctor_leftid (pr211 E) (pr11 dr1) (pr11 dr2)).
  apply pathsinv0.
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _);
    rewrite id_left.
  rewrite (internal_postcomp_id (pr11 dr1)).
  exact (! id_right _).
  rewrite (bifunctor_leftid C).
  rewrite (functor_id K).
  exact (! id_right _).
  refine (_ @ ! maponpaths (compose _) (internal_precomp_id _ _)).
  exact (! id_right _).
Qed.

Lemma double_glued_tensor_rightidax {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): disp_bifunctor_rightidax (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2.
  intros dr1 dr2.
  apply (double_glued_mor_eq_transp _ _).
  split.
  exact (bifunctor_rightid (pr211 E) _ _).
  apply pathsinv0.
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _);
    rewrite id_left.
  refine (_ @ ! maponpaths (compose _) (internal_precomp_id _ _)).
  exact (! id_right _).
  rewrite (bifunctor_rightid C).
  rewrite (functor_id K).
  exact (! id_right _).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id _ _)).
  exact (! id_right _).
Qed.

Lemma double_glued_tensor_leftcompax {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): disp_bifunctor_leftcompax (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2 R3 R4 f23 f34.
  intros dr1 dr2 dr3 dr4 df23 df34.
  apply double_glued_mor_eq_transp.
  split.
  apply (bifunctor_leftcomp E).
  apply pathsinv0.
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_postcomp_comp.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  rewrite (bifunctor_leftcomp C).
  exact (functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_precomp_comp.
Qed.

Lemma double_glued_tensor_rightcompax {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): disp_bifunctor_rightcompax (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2 R3 R4 f23 f34.
  intros dr1 dr2 dr3 dr4 df23 df34.
  apply double_glued_mor_eq_transp.
  split.
  apply (bifunctor_rightcomp E).
  apply pathsinv0.
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_precomp_comp.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  rewrite (bifunctor_rightcomp C).
  exact (functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_postcomp_comp.
Qed.


Lemma double_glued_tensor_functoronmoreq {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): dispfunctoronmorphisms_are_equal (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2 S1 S2 f g.
  intros dr1 dr2 ds1 ds2 df dg.
  apply double_glued_mor_eq_transp.
  split.
  apply (bifunctor_equalwhiskers E).
  simpl.
  refine (doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _ @ ! doublePullbackArrowUnique _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply (compose (doublePullbackPrL _)).
    apply (compose (internal_precomp (pr11 df) _)).
    exact (internal_postcomp _ (pr12 dg)).
  }
  9 : {
    apply (compose (doublePullbackPrM _)).
    apply (# K).
    apply (compose (f ⊗^{C}_{r} _)).
    exact (_ ⊗^{C}_{l} g).
  }
  9 : {
    apply (compose (doublePullbackPrR _)).
    apply (compose (internal_precomp (pr11 dg) _)).
    exact (internal_postcomp _ (pr12 df)).
  }
  rewrite assoc'.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · f)) (internal_postcomp_comp _ _ _) @ _).
  refine (! maponpaths (λ f, _ · (_ · internal_postcomp _ f)) (pr22 dg) @ _).
  refine (maponpaths (λ f, _ · (_ · f)) (internal_postcomp_comp _ _ _) @ _).
  refine (maponpaths (compose _) (assoc _ _ _) @ _).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (maponpaths (compose _) (assoc' _ _ _) @ _).
  rewrite assoc.
  set (dpb22 := tensor_doublePullback pb k ((pr11 dr2,, pr21 dr2),, pr12 dr2,, pr22 dr2) ((pr11 ds2,, pr21 ds2),, pr12 ds2,, pr22 ds2)).
  generalize (doublePullbackSqrLCommutes dpb22); simpl; intros sqr.
  refine (maponpaths (λ f, f · _ ) sqr @ _); clear sqr.
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite internal_lam_precomp.
  do 2 rewrite assoc; do 2 rewrite internal_lam_precomp.
  refine (_ @ assoc' _ _ _).
  refine (_ @ ! maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E _))) _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  simpl.
  rewrite <- hom_onmorphisms_is_postcomp.
  refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
  apply maponpaths.
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  refine (! maponpaths (λ f, f · _ · _) (bifunctor_leftcomp E _ _ _ _ _ _) @ _).
  refine (maponpaths (λ f, _ ⊗^{E}_{l} f · _ · _) (pr21 df) @ _).
  refine (maponpaths (λ f, f · _) (assoc _ _ _) @ _).
  rewrite assoc'.
  rewrite <- (monoidal_braiding_naturality_left E).
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_right E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! maponpaths (compose _) (pr12 k R2 _ _ g) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (functor_comp K).
  refine (_ @ ! maponpaths (λ f, f · _) (bifunctor_leftcomp E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _)).
  refine (_ @ assoc _ _ _).
  rewrite (bifunctor_rightcomp E).
  rewrite assoc'.
  apply maponpaths.
  generalize (pr122 k S1 _ _ f); simpl; rewrite 2 id_right; intros keq.
  exact (! keq).
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  rewrite <- internal_postcomp_comp.
  refine (_ @ maponpaths (λ f, _ · (_ · internal_postcomp _ f)) (pr22 df)).
  refine (_ @ ! maponpaths (λ f, _ · (_ · f)) (internal_postcomp_comp _ _ _)).
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite internal_pre_post_comp_as_post_pre_comp.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (λ f, f · _) (doublePullbackSqrRCommutes (tensor_doublePullback pb k dr2 ds2))).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite assoc.
  refine (! maponpaths (λ f, compose (C:=E) f _) (functor_comp K _ _) @ _).
  rewrite (assoc (C:=C)).
  refine (maponpaths (λ f, compose (C:=E) (# K (f · _)) _) (monoidal_braiding_naturality_left C _ _ _ _) @ _).
  rewrite (assoc' (C:=C)).
  refine (maponpaths (λ f, compose (C:=E) (# K (_ · f)) _) (monoidal_braiding_naturality_right C _ _ _ _) @ _).
  rewrite (assoc (C:=C)).
  rewrite (functor_comp K).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  refine (_ @ maponpaths (compose _) (assoc' _ _ _)).
  rewrite <- internal_precomp_comp.
  rewrite (pr21 dg).
  refine (_ @ assoc' _ _ _).
  rewrite 2 internal_lam_precomp.
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (λ f, f · _) (pr2 (unit_from_are_adjoints (pr2 (pr2 E (pr11 ds1)))) _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite <- hom_onmorphisms_is_postcomp.
  simpl.
  refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
  apply maponpaths.
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (bifunctor_equalwhiskers E _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  rewrite (bifunctor_leftcomp E).
  do 2 refine (_ @ assoc _ _ _).
  apply maponpaths.
  rewrite assoc.
  rewrite <- (monoidal_braiding_naturality_right E).
  rewrite assoc'.
  refine (_ @ maponpaths (compose _) (assoc _ _ _)).
  refine (_ @ assoc' _ _ _).
  rewrite <- (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  generalize (pr122 k R2 _ _ g); simpl; rewrite 2 id_right; intros keq.
  refine (_ @ maponpaths (λ f, compose (C:=E) f _) keq); clear keq.
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (pr12 k S1 _ _ f)).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  exact (functor_comp K _ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite <- internal_pre_post_comp_as_post_pre_comp.
  reflexivity.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  exact (! functor_comp K _ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  reflexivity.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  reflexivity.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  exact (! bifunctor_equalwhiskers C _ _ _ _ _ _ ).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc.
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite <- internal_pre_post_comp_as_post_pre_comp.
  reflexivity.
Qed.

Definition double_glued_tensor {E C : sym_mon_closed_cat} (pb : Pullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K) : disp_tensor (double_glued_cat L K) (pr211 C).
Proof.
  exists (double_glued_disp_bifunctor_data pb L K k).
  split5.
  exact (double_glued_tensor_leftidax pb L K k).
  exact (double_glued_tensor_rightidax pb L K k).
  exact (double_glued_tensor_leftcompax pb L K k).
  exact (double_glued_tensor_rightcompax pb L K k).
  exact (double_glued_tensor_functoronmoreq pb L K k).
Defined.

Definition double_glued_monoidal_unit {C E : sym_mon_closed_cat} (L : lax_monoidal_functor C E) (K : functor C (E^opp)) : double_glued_cat L K I_{ C}.
Proof.
  split.
  exists (I_{E}).
  exact (pr212 L).
  exact (K I_{C},, identity _).
Defined.
