(***********************************

This file contains the definition of the general double gluing construction and results
surrounding it (Compare definition 37 in the paper). In more detail, there is:
- general double glued category as a displayed category
- results about morphisms of the double glued (displayed) category regarding equality and inverses
- the total general double glued category
- the total double glued category for intuitionistic linear logic


**********************************)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.




(** general double glueing as displayed cat**)

(* type of displayed objects *)
Definition double_glued_ob {C E E': category} (L : functor C E) (K : functor C E') : C → UU :=
  λ R : ob C, (∑ U : E, E⟦U, L R⟧) × (∑ X : E', E'⟦K R, X⟧).

(* component 1 of type of morphism *)
Definition double_glued_mor_comp1 {C E E': category} (L : functor C E) (K : functor C E') :
  ∏ R S : ob C, double_glued_ob L K R → double_glued_ob L K S → UU.
Proof.
  intros R S ((U, l), (X, l')) ((V, j), (Y, j')).
  exact (E⟦U,V⟧).
Defined.

(* equation component 1 needs to satisfy *)
Definition double_glued_mor_eq1 {C E E': category} (L : functor C E) (K : functor C E') :
  ∏ R S : ob C, ∏ dr : double_glued_ob L K R, ∏ ds : double_glued_ob L K S, C⟦R, S⟧ → double_glued_mor_comp1 L K R S dr ds → hProp.
Proof.
  intros R S ((U, l), (X, l')) ((V, j), (Y, j')) f ϕ.
  refine (make_hProp(j ∘ ϕ = (# L f) ∘ l) _).
  exact (pr2 E _ _ _ _).
Defined.

(* component 2 of type of morphism *)
Definition double_glued_mor_comp2 {C E E': category} (L : functor C E) (K : functor C E') :
  ∏ R S : ob C, double_glued_ob L K R → double_glued_ob L K S → UU.
Proof.
  intros R S ((U, l), (X, l')) ((V, j), (Y, j')).
  exact (E'⟦X,Y⟧).
Defined.

(* equation component 2 needs to satisfy *)
Definition double_glued_mor_eq2 {C E E': category} (L : functor C E) (K : functor C E') :
  ∏ R S : ob C, ∏ dr : double_glued_ob L K R, ∏ ds : double_glued_ob L K S, C⟦R, S⟧ → double_glued_mor_comp2 L K R S dr ds → hProp.
Proof.
  intros R S ((U, l), (X, l')) ((V, j), (Y, j')) f ψ.
  refine (make_hProp (j' ∘ (# K f) = ψ ∘ l') _).
  exact (pr2 E' _ _ _ _).
Defined.

(* type of (displayed) morphisms bundled *)
Definition double_glued_mor {C E E': category} (L : functor C E) (K : functor C E') :
  ∏ R S : ob C, double_glued_ob L K R → double_glued_ob L K S → C⟦R, S⟧ → UU.
Proof.
  intros R S dr ds f.
  exact ((∑ ϕ, double_glued_mor_eq1 L K R S dr ds f ϕ) × (∑ ψ, double_glued_mor_eq2 L K R S dr ds f ψ)).
Defined.

(* objects and morphisms bundled *)
Definition double_glued_ob_mor {C E E': category} (L : functor C E) (K : functor C E') : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  exact (double_glued_ob L K).
  exact (double_glued_mor L K).
Defined.

(* 1st equation identity has to satisfy *)
Lemma double_glued_id_eq1 {C E E' : category} {L : C ⟶ E} {K : C ⟶ E'} {R : C} (dr : double_glued_ob L K R) :
  double_glued_mor_eq1 L K R R dr dr (identity R) (identity _).
Proof.
  destruct dr as ((U, l), (X, l')).
  refine (id_left l @ _).
  refine (! id_right l @ _).
  apply (maponpaths (compose l)).
  exact (! functor_id L R).
Qed.

(* 2nd equation identity has to satisfy *)
Lemma double_glued_id_eq2 {C E E' : category} {L : C ⟶ E} {K : C ⟶ E'} {R : C} (dr : double_glued_ob L K R) :
  double_glued_mor_eq2 L K R R dr dr (identity R) (identity _).
Proof.
  destruct dr as ((U, l), (X, l')).
  refine (_ @ ! id_right l').
  refine (_ @ id_left l').
  apply (maponpaths (λ f, compose f l')).
  exact (functor_id K R).  
Qed.

(* 1st equation composed arrow has to satisfy *)
Lemma double_glued_comp_eq1 {C E E' : category} {L : C ⟶ E} {K : C ⟶ E'} {R S T : C} {f : C ⟦ R, S ⟧} {g : C ⟦ S, T ⟧} {dr : double_glued_ob L K R}
  {ds : double_glued_ob L K S} {dt : double_glued_ob L K T} (df : double_glued_mor L K R S dr ds f) (dg : double_glued_mor L K S T ds dt g) :
  double_glued_mor_eq1 L K R T dr dt (f · g) (pr11 df · pr11 dg).
Proof.
  destruct df as ((ϕ, eqlm), (ψ, eqlm')).
  destruct dg as ((υ, eqmn), (χ, eqmn')).
  refine (_ @ maponpaths (compose _) (! functor_comp L f g)).
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose (# L g)) eqlm).
  refine (! assoc _ _ _ @ _).
  refine (_ @ assoc _ _ _).
  apply (maponpaths (compose ϕ)). 
  exact eqmn.
Qed.

(* 2nd equation composed arrow has to satisfy *)
Lemma double_glued_comp_eq2 {C E E' : category} {L : C ⟶ E} {K : C ⟶ E'} {R S T : C} {f : C ⟦ R, S ⟧} {g : C ⟦ S, T ⟧} {dr : double_glued_ob L K R}
  {ds : double_glued_ob L K S} {dt : double_glued_ob L K T} (df : double_glued_mor L K R S dr ds f) (dg : double_glued_mor L K S T ds dt g) :
  double_glued_mor_eq2 L K R T dr dt (f · g) (pr12 df · pr12 dg).
Proof.
  destruct df as ((ϕ, eqlm), (ψ, eqlm')).
  destruct dg as ((υ, eqmn), (χ, eqmn')).
  refine (maponpaths (postcompose _) (functor_comp K f g) @ _).
  refine (assoc' (# K f) (# K g) _ @ _).
  refine (maponpaths (compose (# K f)) eqmn' @ _).
  refine (_ @ assoc' _ ψ χ).
  refine (assoc (# K f) _ χ @ _).
  apply (maponpaths (postcompose χ)).
  exact eqlm'.
Qed.

(* data of the double glued displayed category:
 - type of obecjst and morphisms
 - identity
 - composition *)
Definition double_glued_data {C E E': category} (L : functor C E) (K : functor C E') : disp_cat_data C.
Proof.
  exists (double_glued_ob_mor L K).
  split.
  intros R dr.
  split.
  exists (identity _).
  exact (double_glued_id_eq1 dr).
  exists (identity _).
  exact (double_glued_id_eq2 dr).
  intros R S T f g.
  intros ((U, l), (X, l')) ((V, m), (Y, m')) ((W, n), (Z, n')).
  intros df dg.
  split.
  exists (pr11 df · pr11 dg).
  exact (double_glued_comp_eq1 df dg).
  exists (pr12 df · pr12 dg).
  exact (double_glued_comp_eq2 df dg).
Defined.

(* Proof that axioms of a displayed category are satisfied *)
Lemma double_glued_axioms {C E E': category} (L : functor C E) (K : functor C E') : disp_cat_axioms C (double_glued_data L K).
Proof.
  split4.
  intros R S f.
  intros ((U, l), (X, l')) ((V, m), (Y, m')).
  intros ((ϕ, eqml), (ψ, eqml')).
  apply dirprod_paths; apply subtypePath_prop;
    unfold transportb;
    induction (! id_left f);
    exact (id_left _).
  intros R S f.
  intros ((U, l), (X, l')) ((V, m), (Y, m')).
  intros ((ϕ, eqml), (ψ, eqml')).
  apply dirprod_paths; apply subtypePath_prop;
    unfold transportb;
    induction (! id_right f);
    exact (id_right _).
  intros R1 R2 R3 R4 f12 f23 f34.
  intros ((U1, l1), (X1, l1')) ((U2, l2), (X2, l2')) ((U3, l3), (X3, l3')) ((U4, l4), (X4, l4')).
  intros ((ϕ12, eqml12), (ψ12, eqml12')) ((ϕ23, eqml23), (ψ23, eqml23')) ((ϕ34, eqml34), (ψ34, eqml34')).
  apply dirprod_paths; apply subtypePath_prop;
    unfold transportb;
    induction (! assoc f12 f23 f34);
    exact (assoc _ _ _).
  intros R S f.
  intros ((U, l), (X, l')) ((V, m), (Y, m')).
  apply isaset_total2.
  apply isaset_total2.
  exact (pr2 E _ _).
  intro ϕ.
  exact (isasetaprop (propproperty _)).
  intros _.
  apply isaset_total2.
  exact (pr2 E' _ _).
  intro ψ.
  exact (isasetaprop (propproperty _)).
Qed.


(* the double glued displayed category *)
Definition double_glued_cat {C E E': category} (L : functor C E) (K : functor C E') : disp_cat C.
Proof.
  exists (double_glued_data L K).
  exact (double_glued_axioms L K).
Defined.



(* two morphisms in the double glued cat displayed over the same f are equal if both of their components are equal, disregarding the equations they have to satisfy *)
Lemma double_glued_mor_eq {C E E': category} {L : functor C E} {K : functor C E'} {R1 R2 : ob C} {f: C⟦R1, R2⟧} {dr1 : double_glued_cat L K R1} {dr2 : double_glued_cat L K R2} (df dg : dr1 -->[f] dr2): df = dg <-> (pr11 df = pr11 dg) × (pr12 df = pr12 dg).
Proof.
  split.
  intros deq.
  split.
  exact (maponpaths pr1 (maponpaths pr1 deq)).
  exact (maponpaths pr1 (maponpaths (pr2 (P:= λ _, _)) deq)).
  intros (eq1, eq2).
  apply dirprod_paths.
  exact (subtypePath_prop eq1).
  exact (subtypePath_prop eq2).
Qed.

(* equality of morphisms displayed over an equality of morphisms still reduces to equality of both component *)
Lemma double_glued_mor_eq_transp {C E E': category} {L : functor C E} {K : functor C E'} {R1 R2 : ob C} {f g: C⟦R1, R2⟧} {dr1 : double_glued_cat L K R1}
  {dr2 : double_glued_cat L K R2} (eqfg : f = g) (df : dr1 -->[f] dr2) (dg : dr1 -->[g] dr2) :
  df = transportf (mor_disp dr1 dr2) (! eqfg) dg <-> (pr11 df = pr11 dg) × (pr12 df = pr12 dg).
Proof.
  unfold transportf; induction (! eqfg); simpl.
  exact (double_glued_mor_eq df dg).
Qed.

(* an inverse morphism is exactly the morphism where both components are inverted *)
Lemma is_inv_iff_components_are_inv {C E E' : category} {L : functor C E} {K : functor C E'} {R1 R2 : C} {f : C⟦R1, R2⟧} {g : C⟦R2, R1⟧}
  (isinv : is_inverse_in_precat f g) (dr1 : ob_disp (double_glued_cat L K) R1) (dr2 : ob_disp (double_glued_cat L K) R2) (df : mor_disp dr1 dr2 f)
  (dg : mor_disp dr2 dr1 g) :
  (is_inverse_in_precat (pr11 df) (pr11 dg) × is_inverse_in_precat (pr12 df) (pr12 dg)) <-> is_disp_inverse isinv df dg.
Proof.
  destruct df as ((ϕ, eqphi), (ψ, eqpsi));
    revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  destruct dg as ((ϕinv, eqphiinv), (ψinv, eqpsiinv));
    revert eqphiinv eqpsiinv; simpl; intros eqphiinv eqpsiinv.
  split.
  (* left to right : *)
  intros (isinvphi, isinvpsi).
  split.
  use dirprod_paths.
  apply subtypePath_prop.
  unfold transportb, transportf; simpl.
  induction (! pr2 isinv).
  exact (pr2 isinvphi).
  apply subtypePath_prop.
  unfold transportb, transportf.
  induction (! pr2 isinv).
  exact (pr2 isinvpsi).
  use dirprod_paths.
  apply subtypePath_prop.
  unfold transportb, transportf; simpl.
  induction (! pr1 isinv).
  exact (pr1 isinvphi).
  apply subtypePath_prop.
  unfold transportb, transportf.
  induction (! pr1 isinv).
  exact (pr1 isinvpsi).
  (* right to left : *)
  destruct isinv as (isinv1, isinv2).
  simpl.
  intros (isdispinv1, isdispinv2).
  split; split.
  refine (maponpaths pr1 (maponpaths pr1 isdispinv2) @ _).
  unfold transportb, transportf; simpl.
  induction (! isinv1).
  exact (idpath _).
  refine (maponpaths pr1 (maponpaths pr1 isdispinv1) @ _).
  unfold transportb, transportf; simpl.
  induction (! isinv2).
  exact (idpath _).
  refine (maponpaths pr1 (maponpaths (pr2 (P:= λ _, _)) isdispinv2) @ _).
  unfold transportb, transportf; simpl.
  induction (! isinv1).
  exact (idpath _).
  refine (maponpaths pr1 (maponpaths (pr2 (P:= λ _, _)) isdispinv1) @ _).
  unfold transportb, transportf; simpl.
  induction (! isinv2).
  exact (idpath _).  
Defined.

(* the isomorphisms in the double glued cat are exactly the morphisms whose components are both isos *)
Lemma is_iso_iff_components_are_iso {C E E' : category} {L : functor C E} {K : functor C E'} (R1 R2 : C) (f : z_iso R1 R2) (dr1 : ob_disp (double_glued_cat L K) R1) (dr2 : ob_disp (double_glued_cat L K) R2) (df : mor_disp dr1 dr2 f) :
  (is_z_isomorphism (pr11 df) × is_z_isomorphism (pr12 df)) <-> is_z_iso_disp f df.
Proof.
  split.
  destruct df as ((ϕ, eqphi), (ψ, eqpsi));
    revert eqphi eqpsi; simpl; intros eqphi eqpsi.
  intros ((ϕinv, isinvphi), (ψinv, isinvpsi)).
  use tpair.
  split.
  exists ϕinv.
  refine (! pr2 (pr121 E) _ _ _ @ _).
  refine (! maponpaths (compose _) (functor_id _ _) @ _).
  refine (! maponpaths (λ f, _ · (# L f)) (pr122 f) @ _).
  refine (maponpaths (compose _) (functor_comp _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  refine (_ @ pr1 (pr121 E) _ _ _).
  refine (_ @ maponpaths (postcompose _) (pr2 isinvphi)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  exact (! eqphi).
  exists ψinv.
  simpl.
  refine (! pr2 (pr121 E') _ _ _ @ _).
  refine (maponpaths (compose _) (! pr1 isinvpsi) @ _).
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ pr1 (pr121 E') _ _ _).
  refine (_ @ maponpaths (postcompose _) (functor_id _ _)).
  unfold postcompose.
  refine (_ @ maponpaths (λ f, (# K f) · _) (pr222 f)).
  rewrite functor_comp.
  refine (_ @ assoc _ _ _).
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  exact (! eqpsi).
  split.
  apply dirprod_paths;
  apply subtypePath.
  intros g.
  apply (pr2 E _ _).
  unfold transportb, transportf, constr1; simpl.
  induction (! z_iso_after_z_iso_inv f).
  exact (pr2 isinvphi).
  intros g.
  apply (pr2 E' _ _).
  unfold transportb, transportf, constr1; simpl.
  induction (! z_iso_after_z_iso_inv f).
  exact (pr2 isinvpsi).
  apply dirprod_paths;
  apply subtypePath.
  intros g.
  apply (pr2 E _ _).
  unfold transportb, transportf, constr1; simpl.
  induction (! z_iso_inv_after_z_iso f).
  exact (pr1 isinvphi).
  intros g.
  apply (pr2 E' _ _).
  unfold transportb, transportf, constr1; simpl.
  induction (! z_iso_inv_after_z_iso f).
  exact (pr1 isinvpsi).
  (* other direction : *)
  intros (dfinv, isinvdf).
  split.
  exists (pr11 dfinv).
  split.
  refine (maponpaths (λ f, pr1 (pr1 f)) (pr2 isinvdf) @ _); simpl.
  unfold transportb, transportf, constr1.
  induction (! z_iso_inv_after_z_iso f).
  exact (idpath _).
  refine (maponpaths (λ f, pr1 (pr1 f)) (pr1 isinvdf) @ _); simpl.
  unfold transportb, transportf, constr1.
  induction (! z_iso_after_z_iso_inv f).
  exact (idpath _).
  exists (pr12 dfinv).
  split.
  refine (maponpaths (λ f, pr1 (pr2 f)) (pr2 isinvdf) @ _); simpl.
  unfold transportb, transportf, constr1.
  induction (! z_iso_inv_after_z_iso f).
  exact (idpath _).
  refine (maponpaths (λ f, pr1 (pr2 f)) (pr1 isinvdf) @ _); simpl.
  unfold transportb, transportf, constr1.
  induction (! z_iso_after_z_iso_inv f).
  exact (idpath _).  
Defined.


(* the total double glued category *)
Definition double_glued_general_total_cat {C E E' : category} (L : functor C E) (K : functor C E') : category
  := total_category (double_glued_cat L K).

(* the total double glued category for intutionistic linear logic *)
Definition double_glued_total_cat {C E : category} (L : functor C E) (K : functor C (E^opp)) : category
  := total_category (double_glued_cat L K).
