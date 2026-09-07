Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Require Import preliminaries.
Require Import double_pullbacks.
Require Import natural_contraction.

Require Import double_gluing.double_gluing.


Definition tensor_doublePullback_type {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) : UU.
Proof.
  set (U1 := pr11 dr1); set (l1 := pr21 dr1).
  set (X1 := pr12 dr1); set (l1' := pr22 dr1). 
  set (U2 := pr11 dr2); set (l2 := pr21 dr2).
  set (X2 := pr12 dr2); set (l2' := pr22 dr2). 
  use doublePullback.
  exact E.
  exact (internal_hom U1 X2).
  exact (internal_hom U1 (K R2)).
  exact (K (R1 ⊗_{C} R2)).
  exact (internal_hom U2 (K R1)).
  exact (internal_hom U2 X1).
  exact (internal_postcomp U1 l2').
  apply (compose (internal_lam (sym_mon_braiding E _ _ · (pr1 k R1 R2)))).
  exact (internal_precomp l1 _).
  apply (compose (C:=E) (# K (sym_mon_braiding C R2 R1))).
  apply (compose (C:=E) (internal_lam ((pr121 E (K (R2 ⊗_{C} R1)) (L R2)) · (pr1 k R2 R1)))).
  exact (internal_precomp l2 _).
  exact (internal_postcomp U2 l1').
Defined.

Definition tensor_doublePullback {C E : sym_mon_closed_cat} (dpb : doublePullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) :
  tensor_doublePullback_type k dr1 dr2.
Proof.
  apply dpb.
Defined.

Definition double_glued_tensor_product {C E : sym_mon_closed_cat} (dpb : doublePullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R S : ob C} :
  double_glued_cat L K R → double_glued_cat L K S → double_glued_cat L K (R ⊗_{ C} S).
Proof.
  intros dr ds.
  set (U := pr11 dr); set (l := pr21 dr).
  set (X := pr12 dr); set (l' := pr22 dr). 
  set (V := pr11 ds); set (m := pr21 ds).
  set (Y := pr12 ds); set (m' := pr22 ds). 
  (* Displayed tensored object : *)
  split.
  (* Component 1 : *)
  exists (U ⊗_{E} V).
  exact (compose (l ⊗^{E} m) (fmonoidal_preservestensordata L R S)).
  (* Component 2 : *)
  set (P:= tensor_doublePullback dpb k dr ds).
  exists (doublePullbackObject P).
  exact (doublePullbackPrM P).
Defined.
(*
Definition doublePullback_from_tensor {C E : sym_mon_closed_cat} (dpb : doublePullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) :
  ∏ (x y : ob C) (dx : double_glued_cat L K x) (dy : double_glued_cat L K y), tensor_doublePullback_type k dx dy.
Proof.
  intros x y dx dy.
  use tensor_doublePullback.
  exact dpb.
Defined. *)

Lemma double_glued_leftwhiskering_eq1 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f23 : C⟦R2, R3⟧} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2)
  (dr3 : double_glued_cat L K R3) (df23 : dr2 -->[ f23] dr3):
  double_glued_mor_eq1 L K (R1 ⊗_{C} R2) (R1 ⊗_{C} R3) (double_glued_tensor_product pb k dr1 dr2) (double_glued_tensor_product pb k dr1 dr3) (R1 ⊗^{C}_{l} f23) (_ ⊗^{E}_{l} (pr11 df23)).
Proof.
  set (U1 := pr11 dr1); set (l1 := pr21 dr1).
  set (X1 := pr12 dr1); set (l1' := pr22 dr1). 
  set (U2 := pr11 dr2); set (l2 := pr21 dr2).
  set (X2 := pr12 dr2); set (l2' := pr22 dr2). 
  set (U3 := pr11 dr3); set (l3 := pr21 dr3).
  set (X3 := pr12 dr3); set (l3' := pr22 dr3). 
  set (ϕ23 := pr11 df23); set (ψ23 := pr12 df23).
  generalize (pr21 df23) (pr22 df23); simpl; intros eqphi eqpsi.
  refine (_ @ (pr1 (pr221 (pr111 E)) _ _ _ _ (l1 ⊗^{ E} l2) ((pr112 L) R1 R2) (# L (R1 ⊗^{ pr211 C}_{l} f23)))).
  refine (_ @ (maponpaths (compose (l1 ⊗^{ E} l2)) (pr1 (pr22 L) R1 _ _ f23))).
  refine (_ @ (pr2 (pr221 (pr111 E)) _ _ _ _ (l1 ⊗^{ E} l2) (pr1 L R1 ⊗^{ E}_{l} # (pr1 L) f23) ((fmonoidal_preservestensordata L) R1 R3))).
  refine ((pr1 (pr221 (pr111 E)) _ _ _ _ (U1 ⊗^{ pr112 (pr11 E)}_{l} ϕ23) (l1 ⊗^{E} l3) ((pr112 L) R1 R3)) @ _).
  apply cancel_postcomposition.
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
  refine (_ @ assoc _ _ _ ).
  apply (maponpaths (compose _)).
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  exact eqphi.
Qed.

Local Definition double_glued_leftwhiskering_eqs2_type {E C : sym_mon_closed_cat} (dpb : doublePullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f23 : C⟦R2, R3⟧} (d1 : double_glued_cat L K R1)
  (d2 : double_glued_cat L K R2) (d3 : double_glued_cat L K R3) (df23 : d2 -->[ f23] d3): UU.
Proof.
  destruct d1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct d2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct d3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df23 as ((ϕ23, eqphi), (ψ23, eqpsi)). (* displayed morphism over f23 *)
  set (Pb13 := dpb _ _ _ _ _ (internal_postcomp U1 l3')
            (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3))
            (compose (C:=E) (# K ((pr121 C) R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1)) · internal_precomp l3 (K R1))
            (internal_postcomp U3 l1')).
  set (h1 := (doublePullbackPrL Pb13) · (internal_postcomp U1 ψ23)).
  set (h2 := (doublePullbackPrM Pb13) · (#K (R1 ⊗^{ pr121 (pr1 C)}_{l} f23))).
  set (h3 := (doublePullbackPrR Pb13) · (internal_precomp ϕ23 X1)).
  refine (_ × _).
  exact (h1 · internal_postcomp U1 l2' = h2 · (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R2)) (L R1) · pr1 k R1 R2) · internal_precomp l1 (K R2))).
  exact (h2 · (compose (C:=E) (# K ((pr121 C) R2 R1)) (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R1)) (L R2) · pr1 k R2 R1)) · internal_precomp l2 (K R1)) =
    h3 · internal_postcomp U2 l1').
Defined.

Local Lemma double_glued_leftwhiskering_eqs2 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f23 : C⟦R2, R3⟧} (d1 : double_glued_cat L K R1)
  (d2 : double_glued_cat L K R2) (d3 : double_glued_cat L K R3) (df23 : d2 -->[ f23] d3) :
  double_glued_leftwhiskering_eqs2_type pb k d1 d2 d3 df23.
Proof.
  destruct d1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct d2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct d3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df23 as ((ϕ23, eqphi), (ψ23, eqpsi)). (* displayed morphism over f23 *)
  split.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  refine (maponpaths (compose _) _).
  refine (! internal_postcomp_comp _ _ _ @ _ @ internal_postcomp_comp _ _ _).
  apply maponpaths.
  apply pathsinv0.
  exact eqpsi.
  refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (postcompose _)).
  apply doublePullbackSqrLCommutes.
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _ @ assoc' _ _ _).
  apply maponpaths.
  refine ( _ @ internal_pre_post_comp_as_post_pre_comp _ _).
  apply pathsinv0.
  apply internal_pre_post_comp_as_pre_post_comp.
  apply (maponpaths (postcompose _)).
  refine (internal_lam_postcomp _ _ @ _).
  refine (_ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ assoc _ _ _  @ maponpaths (λ f, compose f _) _).
  apply maponpaths.
  2 : {
    apply (monoidal_braiding_naturality_right E).
  }
  apply pathsinv0.
  apply (pr12 k). (* subgoal completed*)

  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  3 : {
    apply maponpaths.
    apply pathsinv0.
    refine ( _ @ internal_pre_post_comp_as_post_pre_comp _ _).
    apply pathsinv0.
    apply internal_pre_post_comp_as_pre_post_comp.
  }
  2 : {
    apply (maponpaths (postcompose _)).
    apply doublePullbackSqrRCommutes.
  }
  refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) _).
  2 : {
    refine (_ @ internal_precomp_comp _ _ _).
    exact (! maponpaths (λ f, internal_precomp f (K R1)) eqphi).
  }
  refine (maponpaths (compose _) _ @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) _).
  apply internal_lam_precomp.
  refine (assoc _ _ _ @ _).
  refine (_ @ maponpaths (λ f, compose f _) _).
  2 : {
    apply pathsinv0.
    apply internal_lam_natural.
  }
  refine (_ @ ! internal_lam_precomp _ _).
  refine (internal_lam_natural _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor.
  rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ assoc _ _ _ @ _ @ assoc _ _ _ @ _).
  2 : {
    apply (maponpaths (postcompose _)).
    apply pathsinv0.
    apply (bifunctor_leftcomp E).
  }
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply (maponpaths (postcompose _)).
      apply (bifunctor_equalwhiskers E).
    }
    apply maponpaths.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply (maponpaths (postcompose _)).
      apply (monoidal_braiding_naturality_left E).
    }
    apply maponpaths.
    apply natural_contraction_extranatural.
  }
  refine (_ @ assoc' _ _ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc' _ _ _ @ _ @  assoc _ _ _).
  2 : {
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_braiding_naturality_right E).
  }
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  refine (bifunctor_equalwhiskers E _ _ _ _ _ _ @ _).
  apply (maponpaths (compose _)).
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! functor_comp K _ _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_right C).
Qed.

Local Lemma double_glued_leftwhiskering_lemma2 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
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

Local Lemma double_glued_leftwhiskering_lemma3 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
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
  refine (_ @ maponpaths (λ f, f · _) (doublePullbackSqrRCommutes (tensor_doublePullback pb k ((U1,, l1),, X1,, l1') ((U3,, l3),, X3,, l3')))).
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite <- internal_precomp_comp.
  revert eqphi; simpl; intros eqphi.
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

Definition double_glued_leftwhiskering_comp2 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  {f23 : C⟦R2, R3⟧} (df23 : dr2 -->[f23] dr3 ):
  double_glued_mor_comp2 L K (R1 ⊗_{ pr211 C} R2) (R1 ⊗_{ pr211 C} R3)
    (double_glued_tensor_product pb k dr1 dr2)
    (double_glued_tensor_product pb k dr1 dr3).
Proof.
  set (dpb12 := tensor_doublePullback pb k dr1 dr2).
  set (dpb13 := tensor_doublePullback pb k dr1 dr3).
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df23 as ((ϕ23, eqphi), (ψ23, eqpsi)).
  use (doublePullbackArrow (C:=E) dpb12).
  apply (compose (doublePullbackPrL dpb13)).
  exact (internal_postcomp U1 ψ23).
  apply (compose (doublePullbackPrM dpb13)).
  exact (# K (R1 ⊗^{C}_{l} f23)).
  apply (compose (doublePullbackPrR dpb13)).
  exact (internal_precomp ϕ23 X1).
  exact (double_glued_leftwhiskering_lemma2 pb k l1 l1' l2 l2' l3 l3' ϕ23 eqphi ψ23 eqpsi).
  exact (double_glued_leftwhiskering_lemma3 pb k l1 l1' l2 l2' l3 l3' ϕ23 eqphi ψ23 eqpsi).
Defined.

Lemma double_glued_leftwhiskering_eq2 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  {f23 : C⟦R2, R3⟧} (df23 : dr2 -->[f23] dr3 ):
  double_glued_mor_eq2 L K _ _ _ _ (R1 ⊗^{C}_{l} f23) (double_glued_leftwhiskering_comp2 pb k dr1 dr2 dr3 df23).
Proof.
  apply pathsinv0.
  apply (doublePullbackArrow_PrM (tensor_doublePullback pb k dr1 dr2)).
Qed.

Definition double_glued_leftwhiskering {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : C} {f23 : C ⟦ R2, R3 ⟧}:
  ∏ (xx : double_glued_cat L K R1) (yy1 : double_glued_cat L K R2) (yy2 : double_glued_cat L K R3),
    yy1 -->[ f23] yy2 → double_glued_tensor_product pb k xx yy1 -->[ R1 ⊗^{ pr211 C}_{l} f23] double_glued_tensor_product pb k xx yy2.
Proof.
(* leftwhiskering : *)
  intros dr1 dr2 dr3 df23. (* displayed objects and morphism *)
  split.
  (* leftwhiskering component 1 : *)
  exists (leftwhiskering_on_morphisms (pr112 (pr11 E)) _ _ _ (pr11 df23)).
  exact (double_glued_leftwhiskering_eq1 pb k dr1 dr2 dr3 df23).
  (* leftwhiskering component 2 : *)
  exists (double_glued_leftwhiskering_comp2 pb k dr1 dr2 dr3 df23).
  exact (double_glued_leftwhiskering_eq2 pb k dr1 dr2 dr3 df23).
Defined.

Local Lemma double_glued_rightwhiskering_eq1 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f12 : C⟦R1, R2⟧} (dr1 : double_glued_cat L K R1)
  (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (df12 : dr1 -->[ f12] dr2) :
  pr11 df12 ⊗^{ pr112 (pr11 E)}_{r} pr11 dr3 · pr21 (double_glued_tensor_product pb k dr2 dr3) =
    pr21 (double_glued_tensor_product pb k dr1 dr3) · # L (f12 ⊗^{ pr211 C}_{r} R3).
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* displayed object over R3 *)
  destruct df12 as ((ϕ12, eqphi), (ψ12, eqpsi)). (* displayed morphism over f12 *)
  revert eqphi eqpsi; simpl; intros eqphi eqpsi.
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

Definition double_glued_rightwhiskering_eqs2_type {E C : sym_mon_closed_cat} (dpb : doublePullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f12 : C⟦R1, R2⟧} (dr1 : double_glued_cat L K R1)
  (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (df12 : dr1 -->[ f12] dr2): UU.
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* displayed object over R3 *)
  destruct df12 as ((ϕ12, eqphi), (ψ12, eqpsi)). (* displayed morphism over f12 *)
  set (Pb23 := dpb _ _ _ _ _ (internal_postcomp U2 l3')
                (internal_lam ((pr121 E) (K (R2 ⊗_{ C} R3)) (L R2) · pr1 k R2 R3) · internal_precomp l2 (K R3))
                (compose (C:=E) (# K ((pr121 C) R3 R2)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R2)) (L R3) · pr1 k R3 R2)) · internal_precomp l3 (K R2))
                (internal_postcomp U3 l2')).
  set (h1 := (doublePullbackPrL Pb23) · (internal_precomp ϕ12 X3)).
  set (h2 := (doublePullbackPrM Pb23) · #K (f12 ⊗^{ pr121 (pr1 C)}_{r} R3)).
  set (h3 := (doublePullbackPrR Pb23) · (internal_postcomp U3 ψ12)).
  refine (_ × _).
  exact (h1 · internal_postcomp U1 l3' = h2 · (internal_lam ((pr121 E) (K (R1 ⊗_{ C} R3)) (L R1) · pr1 k R1 R3) · internal_precomp l1 (K R3))).
  exact (h2 · (compose (C:=E) (# K ((pr121 C) R3 R1)) (internal_lam ((pr121 E) (K (R3 ⊗_{ C} R1)) (L R3) · pr1 k R3 R1)) · internal_precomp l3 (K R1)) =
    h3 · internal_postcomp U3 l1').
Defined.

Local Lemma double_glued_rightwhiskering_eqs2 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : ob C} {f12 : C⟦R1, R2⟧} (dr1 : double_glued_cat L K R1)
  (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3) (df12 : dr1 -->[ f12] dr2) :
  double_glued_rightwhiskering_eqs2_type pb k dr1 dr2 dr3 df12.
Proof.
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* displayed object over R3 *)
  destruct df12 as ((ϕ12, eqphi), (ψ12, eqpsi)). (* displayed morphism over f12 *)
  split.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (maponpaths (compose _) (! internal_pre_post_comp_as_pre_post_comp ϕ12 l3' @ internal_pre_post_comp_as_post_pre_comp ϕ12 l3') @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  apply doublePullbackSqrLCommutes.
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _ @ assoc' _ _ _).
  apply maponpaths.
  refine (! internal_precomp_comp _ _ _ @ _ @ internal_precomp_comp _ _ _).
  apply (maponpaths (λ f, internal_precomp f _)).
  apply eqphi.
  apply (maponpaths (postcompose _)).
  refine (internal_lam_precomp _ _ @ _).
  refine (_ @ ! internal_lam_natural _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (natural_contraction_extranatural k).
  apply (maponpaths (postcompose _)).
  apply (monoidal_braiding_naturality_right E). (*completes subgoal *)
  refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  2 : {
    apply maponpaths.
    refine (! internal_postcomp_comp _ _ _ @ _ @ internal_postcomp_comp _ _ _).
    apply maponpaths.
    exact eqpsi.
  }
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  2 : {
    apply (maponpaths (postcompose _)).
    apply doublePullbackSqrRCommutes.
  }
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _ @  assoc _ _ _).
  2 : {
    apply maponpaths.
    exact (! internal_pre_post_comp_as_post_pre_comp _ _ @
             internal_pre_post_comp_as_pre_post_comp _ _).
  }
  apply (maponpaths (postcompose _)).
  refine (assoc _ _ _ @ _ @ ! internal_lam_postcomp _ _ @ _).
  2 : {
    apply (maponpaths (postcompose _)).
    apply pathsinv0.
    apply internal_lam_natural.
  }
  refine (_ @ internal_lam_natural _ _ @ _ ).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (functor_comp K).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite 2 (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply (maponpaths (postcompose _)).
    apply assoc'.
  }
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  2 : {
    apply maponpaths.
    apply (pr12 k).
  }
  refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (postcompose _)).
  2 : {
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_braiding_naturality_right E).
  }
  refine (_ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  apply (monoidal_braiding_naturality_left C).
Qed.

Local Lemma double_glued_rightwhiskering_lemma1 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
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
  unfold double_glued_mor_comp1, double_glued_mor_eq1,
    double_glued_mor_comp2, double_glued_mor_eq2 in *.
  rewrite assoc'.
  refine (! maponpaths (compose _) (internal_pre_post_comp_as_pre_post_comp _ _ ) @ _).
  refine (maponpaths (compose _) (internal_pre_post_comp_as_post_pre_comp _ _ ) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackSqrLCommutes _) @ _).
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
  revert eqphi; simpl; intros eqphi.
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
  apply pathsinv0.
  apply natural_contraction_extranatural.
Qed.

Local Lemma double_glued_rightwhiskering_lemma2 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
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

Definition double_glued_rightwhiskering_comp2 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  {f12 : C⟦R1, R2⟧} (df12 : dr1 -->[f12] dr2 ):
  double_glued_mor_comp2 L K (R1 ⊗_{ pr211 C} R3) (R2 ⊗_{ pr211 C} R3)
    (double_glued_tensor_product pb k dr1 dr3)
    (double_glued_tensor_product pb k dr2 dr3).
Proof.
  set (dpb13 := tensor_doublePullback pb k dr1 dr3).
  set (dpb23 := tensor_doublePullback pb k dr2 dr3).
  destruct dr1 as ((U1, l1), (X1, l1')). (* displayed object over R1 *)
  destruct dr2 as ((U2, l2), (X2, l2')). (* displayed object over R2 *)
  destruct dr3 as ((U3, l3), (X3, l3')). (* ... *)
  destruct df12 as ((ϕ12, eqphi), (ψ12, eqpsi)).
  use (doublePullbackArrow (C:=E) dpb13).
  apply (compose (doublePullbackPrL dpb23)).
  exact (internal_precomp ϕ12 X3).
  apply (compose (doublePullbackPrM dpb23)).
  exact (# K (f12 ⊗^{C}_{r} R3)).
  apply (compose (doublePullbackPrR dpb23)).
  exact (internal_postcomp U3 ψ12).
  exact (double_glued_rightwhiskering_lemma1 pb k l1 l1' l2 l2' l3 l3' ϕ12 eqphi ψ12 eqpsi).
  exact (double_glued_rightwhiskering_lemma2 pb k l1 l1' l2 l2' l3 l3' ϕ12 eqphi ψ12 eqpsi).
Defined.

Lemma double_glued_rightwhiskering_eq2 {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) {R1 R2 R3 : C} (dr1 : double_glued_cat L K R1) (dr2 : double_glued_cat L K R2) (dr3 : double_glued_cat L K R3)
  {f12 : C⟦R1, R2⟧} (df12 : dr1 -->[f12] dr2 ):
  double_glued_mor_eq2 L K _ _ _ _ (f12 ⊗^{C}_{r} R3) (double_glued_rightwhiskering_comp2 pb k dr1 dr2 dr3 df12).
Proof.
  apply pathsinv0.
  apply (doublePullbackArrow_PrM (tensor_doublePullback pb k dr1 dr3)).
Qed.

Definition double_glued_rightwhiskering {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E}
  {K : functor C (E^opp)} (k : natural_contraction C E L K) {R1 R2 R3 : C} {f12 : C ⟦ R1, R2 ⟧} :
   ∏ (xx1 : double_glued_cat L K R1) (xx2 : double_glued_cat L K R2) (yy : double_glued_cat L K R3),
  xx1 -->[ f12] xx2 → double_glued_tensor_product pb k xx1 yy -->[ f12 ⊗^{ pr211 C}_{r} R3] double_glued_tensor_product pb k xx2 yy.
Proof.
  intros dr1 dr2 dr3 df12.
  split.
  exists (rightwhiskering_on_morphisms (pr112 (pr11 E)) _ _ _ (pr11 df12)).
  exact (double_glued_rightwhiskering_eq1 pb k dr1 dr2 dr3 df12).
  (* rightwhiskering component 2 : *)
  exists (double_glued_rightwhiskering_comp2 pb k dr1 dr2 dr3 df12).
  exact (double_glued_rightwhiskering_eq2 pb k dr1 dr2 dr3 df12).
Defined.

Definition double_glued_disp_bifunctor_data {E C : sym_mon_closed_cat} (pb : doublePullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (k : natural_contraction C E L K) :
  disp_bifunctor_data (pr211 C) (double_glued_cat L K) (double_glued_cat L K) (double_glued_cat L K).
Proof.
  unfold disp_bifunctor_data.
  exists (λ R S, double_glued_tensor_product pb k (R:=R) (S:=S)).
  exists (λ R1 R2 R3 f23, double_glued_leftwhiskering pb k (R1:=R1) (R2:=R2) (R3:=R3)).
  exact (λ R1 R2 R3 f23, double_glued_rightwhiskering pb k (R1:=R1) (R2:=R2)).
Defined.

Lemma double_glued_tensor_leftidax {E C : sym_mon_closed_cat} (pb : doublePullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): disp_bifunctor_leftidax (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2.
  intros dr1 dr2.
  apply (double_glued_mor_eq_transp _ _).
  split.
  exact (bifunctor_leftid (pr211 E) (pr11 dr1) (pr11 dr2)).
  apply pathsinv0.
  simpl.
  unfold double_glued_leftwhiskering_comp2.
  set (dpb12 := tensor_doublePullback pb k dr1 dr2).
  refine (doublePullbackArrowUnique' dpb12 _ _ _ _ _ _ _ _ _ _);
    rewrite id_left.
  rewrite (internal_postcomp_id (pr11 dr1)).
  exact (! id_right _).
  rewrite (bifunctor_leftid C).
  rewrite (functor_id K).
  exact (! id_right _).
  refine (_ @ ! maponpaths (compose _) (internal_precomp_id _ _)).
  exact (! id_right _).
Qed.

Lemma double_glued_tensor_rightidax {E C : sym_mon_closed_cat} (pb : doublePullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): disp_bifunctor_rightidax (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2.
  intros dr1 dr2.
  apply (double_glued_mor_eq_transp _ _).
  split.
  exact (bifunctor_rightid (pr211 E) _ _).
  apply pathsinv0.
  set (dpb12 := tensor_doublePullback pb k dr1 dr2).
  refine (doublePullbackArrowUnique' dpb12 _ _ _ _ _ _ _ _ _ _);
    rewrite id_left.
  refine (_ @ ! maponpaths (compose _) (internal_precomp_id _ _)).
  exact (! id_right _).
  rewrite (bifunctor_rightid C).
  rewrite (functor_id K).
  exact (! id_right _).
  refine (_ @ ! maponpaths (compose _) (internal_postcomp_id _ _)).
  exact (! id_right _).
Qed.

Lemma double_glued_tensor_leftcompax {E C : sym_mon_closed_cat} (pb : doublePullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): disp_bifunctor_leftcompax (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2 R3 R4 f23 f34.
  intros dr1 dr2 dr3 dr4 df23 df34.
  apply double_glued_mor_eq_transp.
  split.
  apply (bifunctor_leftcomp E).
  apply pathsinv0.
  set (dpb12 := tensor_doublePullback pb k dr1 dr2).
  set (dpb13 := tensor_doublePullback pb k dr1 dr3).
  refine (doublePullbackArrowUnique' dpb12 _ _ _ _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL dpb13 _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_postcomp_comp.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM dpb13 _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  rewrite (bifunctor_leftcomp C).
  exact (functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR dpb13 _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_precomp_comp.
Qed.

Lemma double_glued_tensor_rightcompax {E C : sym_mon_closed_cat} (pb : doublePullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): disp_bifunctor_rightcompax (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2 R3 R4 f23 f34.
  intros dr1 dr2 dr3 dr4 df23 df34.
  apply double_glued_mor_eq_transp.
  split.
  apply (bifunctor_rightcomp E).
  apply pathsinv0.
  set (dpb14 := tensor_doublePullback pb k dr1 dr4).
  set (dpb24 := tensor_doublePullback pb k dr2 dr4).
  refine (doublePullbackArrowUnique' dpb14 _ _ _ _ _ _ _ _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL dpb24 _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_precomp_comp.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM dpb24 _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  rewrite (bifunctor_rightcomp C).
  exact (functor_comp K _ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR dpb24 _ _ _ _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply internal_postcomp_comp.
Qed.


Lemma double_glued_tensor_functoronmoreq {E C : sym_mon_closed_cat} (pb : doublePullbacks E) (L : lax_monoidal_functor C E) (K : functor C (E^opp))
  (k : natural_contraction C E L K): dispfunctoronmorphisms_are_equal (F:= pr211 C) (double_glued_disp_bifunctor_data (E:=E) (C:=C) pb L K k).
Proof.
  intros R1 R2 S1 S2 f g.
  intros dr1 dr2 ds1 ds2 df dg.
  apply double_glued_mor_eq_transp.
  split.
  apply (bifunctor_equalwhiskers E).
  set (dpb11 := tensor_doublePullback pb k dr1 ds1).
  set (dpb22 := tensor_doublePullback pb k dr2 ds2).
  refine (doublePullbackArrowUnique' dpb11 _ _ _ _ _ _ _ _ _ _ @
            ! doublePullbackArrowUnique' dpb11 _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  9 : {
    apply (compose (doublePullbackPrL dpb22)).
    apply (compose (internal_precomp (pr11 df) _)).
    exact (internal_postcomp _ (pr12 dg)).
  }
  9 : {
    apply (compose (doublePullbackPrM dpb22)).
    apply (# K).
    apply (compose (f ⊗^{C}_{r} _)).
    exact (_ ⊗^{C}_{l} g).
  }
  9 : {
    apply (compose (doublePullbackPrR dpb22)).
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
  refine (assoc _ _ _ @ _).
  generalize (doublePullbackSqrLCommutes dpb22); simpl; intros sqr.
  refine (maponpaths (λ f, f · _ ) sqr @ _); clear sqr.
  repeat rewrite assoc'.
  apply maponpaths.
  rewrite internal_lam_precomp.
  do 2 rewrite assoc; do 2 rewrite internal_lam_precomp.
  refine (_ @ ! internal_lam_natural _ _).
  refine (internal_lam_postcomp _ _ @ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor; rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine ( _ @ assoc' _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc _ _ _ @ assoc _ _ _ @ _ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (monoidal_braiding_naturality_left E).
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply (maponpaths (postcompose _)).
    apply (monoidal_braiding_naturality_left E).
  }
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply (maponpaths (postcompose _)).
    apply (monoidal_braiding_naturality_right E).
  }
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply pathsinv0.
  apply (pr12 k).
  refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
  2 : {
    apply (maponpaths (postcompose _)).
    refine (_ @ bifunctor_equalwhiskers E _ _ _ _ _ _).
    refine (assoc' _ _ _ @ _).
    apply (maponpaths (compose _)).
    refine (! bifunctor_leftcomp E _ _ _ _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0.
    apply (functor_comp K).
  }
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    apply pathsinv0.
    apply natural_contraction_extranatural.
  }
  apply (maponpaths (postcompose _)).
  refine ( _ @ assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (postcompose _)).
  2 : {
    apply maponpaths.
    apply (bifunctor_equalwhiskers E).
  }
  refine (! bifunctor_rightcomp E _ _ _ _ _ _ @ _ @
            bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply (pr21 df).
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
  refine (_ @ assoc' _ _ _ @ _).
  2 : {
    apply maponpaths.
    apply cancel_postcomposition.
    exact (! maponpaths (λ f, internal_precomp f (K R2)) (pr21 dg)).
  }
  rewrite 2 internal_lam_precomp.
  refine (internal_lam_natural _ _ @ _).
  refine (_ @ ! internal_lam_postcomp _ _).
  apply maponpaths.
  unfold monoidal_cat_tensor_mor;
    rewrite (when_bifunctor_becomes_rightwhiskering E).
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply (maponpaths (postcompose _)).
    refine (assoc _ _ _ @ _).
    apply (maponpaths (postcompose _)).
    apply pathsinv0.
    apply (bifunctor_leftcomp E).
  }
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  apply (bifunctor_equalwhiskers E).
  apply maponpaths.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  apply pathsinv0.
  apply (monoidal_braiding_naturality_right E).
  refine (_ @ assoc _ _ _ @ _).
  2 : {
    apply (maponpaths (postcompose _)).
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply (maponpaths (postcompose _)).
    apply (monoidal_braiding_naturality_left E).    
  }
  apply maponpaths.
  refine ( _ @ assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  3 : {
    apply (maponpaths (postcompose _)).
    apply (natural_contraction_extranatural k).
  }
  refine (_ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply (functor_comp K).
  apply maponpaths.
  now apply (pr12 k).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite <- internal_pre_post_comp_as_post_pre_comp.
  reflexivity.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  exact (! functor_comp K _ _).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  reflexivity.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrL _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  reflexivity.
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrM _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  apply maponpaths.
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  exact (! bifunctor_equalwhiskers C _ _ _ _ _ _ ).
  refine (assoc' (C:=E) _ _ _ @ _).
  refine (maponpaths (compose _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ f, f · _) (doublePullbackArrow_PrR _ _ _ _ _ _ _) @ _).
  rewrite assoc'.
  rewrite <- internal_pre_post_comp_as_pre_post_comp.
  rewrite <- internal_pre_post_comp_as_post_pre_comp.
  reflexivity.
Qed.

Definition double_glued_tensor {E C : sym_mon_closed_cat} (pb : doublePullbacks E) {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
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

Definition double_glued_monoidal_unit {C E : sym_mon_closed_cat} (L : lax_monoidal_functor C E) (K : functor C (E^opp)) :
  double_glued_cat L K I_{ C}.
Proof.
  split.
  exists (I_{E}).
  exact (fmonoidal_preservesunit L).
  exact (K I_{C},, identity _).
Defined.
