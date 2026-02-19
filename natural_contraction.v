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
Require Import double_gluing.



(* Double glueing for ILL *)

(* natural contraction *)

Definition contraction_fct (C E : monoidal_cat) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) :=
  λ (R S : C), E ⟦monoidal_cat_tensor_pt (L R) (K (monoidal_cat_tensor_pt R S)), K S⟧.

Definition contraction_left_functor_data (C E : monoidal_cat) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (R : ob C): functor_data (C^opp) E.
Proof.
  exists (λ S, (L R) ⊗_{E} (K (R ⊗_{C} S))).
  intros a b f.
  apply (leftwhiskering_on_morphisms (pr12 E)).
  apply (#K).
  exact (leftwhiskering_on_morphisms (pr12 C) _ _ _ f).
Defined.

Definition contraction_left_functor (C E : monoidal_cat) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (R : ob C): functor (C^opp) E.
Proof.
  exists (contraction_left_functor_data C E L K R).
  split.
  intros a.
  refine (_ @ (pr1 (pr122 E) (L R) (K (R ⊗_{C} a)))).
  apply (maponpaths (leftwhiskering_on_morphisms (pr12 E) (L R) (K (R ⊗_{C} a)) (K (R ⊗_{C} a))) ).
  exact ((maponpaths (#K) (pr1 (pr122 C) R a)) @ (functor_id K (R ⊗_{C} a))).
  intros a b c fba gcb.
  refine (_ @ pr122 (pr122 E) (L R) _ _ _ (# K (leftwhiskering_on_morphisms (pr12 C) R b a fba)) (# K (leftwhiskering_on_morphisms (pr12 C) R c b gcb))).
  apply (maponpaths (λ f, leftwhiskering_on_morphisms (pr12 E) (L R) (K (R ⊗_{C} a)) (K (R ⊗_{C} c)) f)).
  refine (_ @ pr22 K _ _ _ (leftwhiskering_on_morphisms (pr12 C) R c b gcb) (leftwhiskering_on_morphisms (pr12 C) R b a fba)).
  exact (maponpaths (# K) (pr122 (pr122 C) R _ _ _ gcb fba)).
Defined.
  
Definition contraction_left_bifunctor_data (C E : monoidal_cat) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (S : ob C):
  bifunctor_data (C^opp) C E.
Proof.
  exists (λ R1 R2, (L R2) ⊗_{E} (K (R1 ⊗_{C} S))).
  split.
  intros b a1 a2 f12.
  apply (pr22 (pr112 E)).
  exact (#L f12).
  intros a b1 b2 f21.
  apply (pr12 (pr112 E)).
  apply (#K).
  exact (pr22 (pr112 C) S b2 b1 f21).
Defined.

Definition contraction_left_bifunctor (C E : monoidal_cat) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) (S : ob C): bifunctor (C^opp) C E.
Proof.
  exists (contraction_left_bifunctor_data C E L K S).
  split.
  intros a b.
  refine (_ @ pr12 (pr122 E) (K (a ⊗_{C} S)) (L b)).
  unfold rightwhiskering_on_morphisms; simpl.
  apply (maponpaths (λ f, (pr221 (pr12 E)) (K (a ⊗_{C} S)) (L b) (L b) f)).
  exact (pr121 L b).
  split.
  intros a b.
  refine (_ @ pr1 (pr122 E) (L a) (K (b ⊗_{C} S))).
  apply (maponpaths (λ f, (pr121 (pr12 E)) (L a) (K (b ⊗_{C} S)) (K (b ⊗_{C} S)) f)).
  refine (_ @ pr12 K (b ⊗_{C} S)).
  exact (maponpaths (# K) (pr121 (pr22 C) S b)).
  split.
  intros a b c d fcb fdc.
  refine (_ @ pr1 (pr222 (pr122 E)) (K (a ⊗_{C} S)) (L b) (L c) (L d) (# L fcb) (# L fdc)).
  apply (maponpaths (λ f, rightwhiskering_on_morphisms (pr12 E) (K (a ⊗_{C} S)) (L b) (L d) f)).
  exact (pr221 L _ _ _ _ _).
  split.
  intros a b c d fcb fdc.
  set (eq1:= pr122 (pr122 E) (L a) (K (b ⊗_{C} S)) (K (c ⊗_{C} S)) (K (d ⊗_{C} S)) (# K ((pr221 (pr12 C)) S c b fcb)) (# K ((pr221 (pr12 C)) S d c fdc))).
  refine (_ @ eq1).
  apply (maponpaths (λ f, leftwhiskering_on_morphisms (pr12 E) (L a) (K (b ⊗_{C} S)) (K (d ⊗_{C} S)) f)).
  set (eq2:= pr22 K _ _ _ ((pr221 (pr12 C)) S d c fdc) ((pr221 (pr12 C)) S c b fcb)).
  refine (_ @ eq2).
  exact (maponpaths (# K) (pr1 (pr222 (pr122 C)) S d c b fdc fcb)).
  intros a b c d fba fcd.
  exact (! pr2 (pr222 (pr122 E)) (L c) (L d) (K (a ⊗_{C} S)) (K (b ⊗_{C} S))(# L fcd) (# K ((pr221 (pr12 C)) S b a fba))).
Defined.

Definition is_natural_contraction {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : ∏ (R S : C), E ⟦(L R) ⊗_{E} (K (R ⊗_{C} S)), K S⟧) : UU.
Proof.
  (* natural in S :*)
  refine ((∏ R, is_nat_trans (contraction_left_functor_data C E L K R) (functor_op K) (k R)) × _).
  (* dinatural in R :*)
  refine ((∏ S, is_dinatural (F:=contraction_left_bifunctor C E L K S) (G:=constant_bifunctor (C ^opp) C (functor_op K S)) (λ R, k R S)) × _).
  refine (_ × _).
  (* diagram 1 commutes :*)
  refine (∀ S : C, _ ).
  use make_hProp.
  refine (lu_{E} (K S) = _ · k (I_{C}) S).
  exact ((pr212 L) ⊗^{E} (# K (lu_{C} S))).
  exact (pr21 (pr11 E) _ _ _ _).
  (* diagram 2 commutes :*)
  refine (∀ R S T : C, _).
  use make_hProp.
  use ( λ f g : E⟦(L R ⊗_{E} L S) ⊗_{E} K (R ⊗_{C} (S ⊗_{C} T)) , K T⟧, f = g).
  apply (λ f, compose f (k ((R ⊗_{C}  S)) T)).
  use (compose (b:=((L R) ⊗_{E} (L S)) ⊗_{E} (K ((R ⊗_{C} S) ⊗_{C} T)))).
  apply (leftwhiskering_on_morphisms (pr112 (pr11 E)) ((L R) ⊗_{E} (L S)) _ _).
  apply (# K).
  exact (α^{C}_{R, S, T}).
  apply (rightwhiskering_on_morphisms E (K ((R ⊗_{C} S) ⊗_{C} T)) _ _).
  exact (pr112 L _ _).
  apply (postcompose (k S T)).
  apply (postcompose (leftwhiskering_on_morphisms E (L S) _ _ (k R (S ⊗_{C} T)))).
  apply (postcompose (α^{E}_{_, _, _})).
  apply (rightwhiskering_on_morphisms E (K (R ⊗_{C} (S ⊗_{C} T))) _ _ ).
  exact (sym_mon_braiding E _ _).
  exact (pr21 (pr11 E) _ _ _ _).
Defined.

Definition natural_contraction (C E : sym_mon_closed_cat) (L : lax_monoidal_functor C E) (K : functor C (E^opp)) : UU :=
  ∑ k : ∏ (R S : C), E ⟦(L R) ⊗_{E} (K (R ⊗_{C} S)), K S⟧ , is_natural_contraction k.


Lemma natural_contraction_tensor1 {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K)
  (R1 R2 R3 : ob C) :
  (fmonoidal_preservestensordata L) R1 R2 ⊗^{ E}_{r} K ((R1 ⊗_{ C} R2) ⊗_{ C} R3) · pr1 k (R1 ⊗_{ C} R2) R3 =
    (L R1 ⊗_{ E} L R2) ⊗^{E}_{l} # K αinv^{ C }_{ R1, R2, R3} · sym_mon_braiding E (L R1) (L R2) ⊗^{ E}_{r} K (R1 ⊗_{ C} (R2 ⊗_{ C} R3)) ·
                                   α^{ E }_{ L R2, L R1, K (R1 ⊗_{ C} (R2 ⊗_{ C} R3))} · L R2 ⊗^{ E}_{l} pr1 k R1 (R2 ⊗_{ C} R3) · pr1 k R2 R3.
Proof.
  do 3 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    refine (_ @ assoc' _ _ _).
    exact (pr2 (pr222 k) R1 R2 R3).
  }
  refine (! id_left _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_leftid E _ _ @ _ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! functor_id K _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_associatorisolaw C).
Qed.

Lemma natural_contraction_composed {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K)
  (R1 R2 R3 : ob C) :
  L R2 ⊗^{ E}_{l} pr1 k R1 (R2 ⊗_{ C} R3) · pr1 k R2 R3 =
    αinv^{ E }_{ L R2, L R1, K (R1 ⊗_{ C} (R2 ⊗_{ C} R3))} · sym_mon_braiding E (L R2) (L R1) ⊗^{ E}_{r} K (R1 ⊗_{ C} (R2 ⊗_{ C} R3))
  · (L R1 ⊗_{ E} L R2) ⊗^{ E}_{l} # K α^{ C }_{ R1, R2, R3} · (fmonoidal_preservestensordata L) R1 R2 ⊗^{ E}_{r} K ((R1 ⊗_{ C} R2) ⊗_{ C} R3) · pr1 k (R1 ⊗_{ C} R2) R3.
Proof.
  do 2 refine (_ @ assoc _ _ _).
  refine (_ @ maponpaths (compose _) (_ @ assoc' _ _ _)).
  2 : {
    exact (! pr2 (pr222 k) R1 R2 R3).
  }
  unfold postcompose.
  refine (! id_left _ @ _).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! pr2 (monoidal_associatorisolaw E _ _ _) @ _).
  refine (_ @ assoc _ _ _).
  apply maponpaths.
  refine (! id_left _ @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (! bifunctor_rightid E _ _ @ _ @ bifunctor_rightcomp E _ _ _ _ _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_braiding_inverses E).
Qed.

Lemma natural_contraction_unit {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) (S : ob C) :
  fmonoidal_preservesunit L ⊗^{ E}_{r} K (I_{ C} ⊗_{ C} S) · pr1 k I_{ C} S =
    I_{ E} ⊗^{ E}_{l} # K luinv^{ C }_{ S} · lu^{ E }_{ K S}.
Proof.
  refine (! id_left _ @ _ @ maponpaths (compose _) (! pr1 (pr222 k) S)).
  rewrite 2 assoc.
  apply (maponpaths (postcompose _)).
  rewrite (bifunctor_equalwhiskers E).
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (! bifunctor_leftid E _ _ @ _ @ bifunctor_leftcomp E _ _ _ _ _ _).
  apply maponpaths.
  refine (! functor_id K _ @ _ @ functor_comp K _ _).
  apply maponpaths.
  apply pathsinv0.
  apply (monoidal_leftunitorisolaw C).
Qed.
  
Lemma natural_contraction_extranatural {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)}
  (k : natural_contraction C E L K) (R1 R2 R3 : ob C) (f23 : C⟦R2, R3⟧) :
  (L R2) ⊗^{E}_{l} (# K (f23 ⊗^{C}_{r} R1)) · pr1 k R2 R1 =  (# L f23) ⊗^{E}_{r} (K (R3 ⊗_{ C} R1)) · pr1 k R3 R1.
Proof.
  generalize (pr122 k R1 _ _ f23); simpl; rewrite 2 id_right.
  exact (idfun _).
Qed.

Definition curried_contraction {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) :=
  λ R S, (φ_adj (pr2 (pr2 E (L R))) ((pr121 E (K (R ⊗_{C} S)) (L R)) · (pr1 k R S))).


Definition curried_contraction_leftfunctordata {C E : sym_mon_closed_cat} (L : lax_monoidal_functor C E) (K : functor C (E^opp)) : functor_data (precategory_binproduct C C) (E ^opp).
Proof.
  exists (λ RS, internal_hom (L (pr1 RS)) (K (pr2 RS))).
  intros (R1, S1) (R2, S2) (f12, g12).
  exact ((internal_postcomp _ (#K g12)) · (internal_precomp (#L f12) _)).
Defined.


Definition curried_contraction_leftfunctor {C E : sym_mon_closed_cat} (L : lax_monoidal_functor C E) (K : functor C (E^opp)) : functor (precategory_binproduct C C) (E ^opp).
Proof.
  apply bifunctor_to_functorfromproductcat.
  apply (compose_bifunctor_with_functor (C:=C)).
  use tpair.
  exact (pr121 (pr1 C)).
  exact (pr12 (pr211 C)).
  exact K.
Defined.

Definition curried_contraction_rightfunctor {C E : sym_mon_closed_cat} (L : lax_monoidal_functor C E) (K : functor C (E ^opp)) : functor ((category_binproduct C C)^opp ^opp) (E^opp).
Proof.
  apply (functor_op).
  change (category_binproduct (C ^opp) (C ^opp) ⟶ E).
  apply bifunctor_to_functorfromproductcat.
  apply (compose_functor_with_bifunctor (functor_op L) (functor_op K)).
  exact (lolli_bifunctor E).
Defined.

Definition curried_contraction_isnat_statement {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) : UU.
Proof.
  refine (is_nat_trans (curried_contraction_rightfunctor L K) (curried_contraction_leftfunctor L K) _).
  intros (R, S).
  exact (curried_contraction k R S).
Defined.

Proposition curried_contraction_isnat {C E : sym_mon_closed_cat} {L : lax_monoidal_functor C E} {K : functor C (E^opp)} (k : natural_contraction C E L K) :
  curried_contraction_isnat_statement k.
Proof.
  intros (R1, S1) (R2, S2) (f12, g12).
  simpl.
  unfold compose, opp_precat_data; simpl.
  refine (_ @ φ_adj_natural_precomp _ _ _ _ _ _).
  refine (_ @ ! φ_adj_natural_postcomp _ _ _ _ _ _).
  set (pr2 (pr112 (pr2 E (L R2)))).
  unfold is_nat_trans in i.
  change (φ_adj (pr2 (pr2 E (L R2)))
    (((pr121 E) (K (R2 ⊗_{ C} S2)) (L R2)) · (pr1 k R2 S2))
  · f12 ⊗^{ compose_functor_with_bifunctor_data (functor_op L) (functor_op K) (lolli_bifunctor E)} g12 =
  φ_adj (pr2 (pr2 E (L R1)))
    (# (rightwhiskering_functor (pr1 E) (L R1)) (f12 ⊗^{ compose_bifunctor_with_functor_data (_,, pr122 (pr11 C)) K} g12))
  · # (pr1 (pr2 E (L R1)))
  (((pr121 E) (K (R1 ⊗_{ C} S1)) (L R1)) · (pr1 k R1 S1))).
  set (braid := pr121 E).
  set (homLR2 := pr1 (pr2 E (L R2))).
  set (homLR1 := pr1 (pr2 E (L R1))).
  assert (# homLR2 (braid (K (R2 ⊗_{ C} S2)) (L R2) · pr1 k R2 S2)· (internal_precomp (# L f12) (K S2) · internal_postcomp (L R1) (# K g12)) =
            compose (C:=E) (compose (C:=E) (# homLR2 (braid (K (R2 ⊗_{ C} S2)) (L R2))) (internal_precomp (# L f12) (L R2 ⊗_{E} K(R2 ⊗_{C} S2))))
              (compose (C:=E) (# homLR1 (L R2 ⊗^{E}_{l} # K (R2 ⊗^{C}_{l} g12))) (# homLR1 (pr1 k R2 S1)))) as righteq.
  refine (maponpaths (postcompose _) (functor_comp homLR2 _ _) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply (maponpaths (compose _)).
  generalize (pr12 k R2 S2 S1 g12).
  unfold contraction_left_functor_data; simpl;
    intros knateq.
  refine (_ @ maponpaths (compose _) (functor_comp homLR1 _ _)).
  refine (_ @ ! maponpaths (λ f, _ · # homLR1 f) knateq).
  refine (_ @ ! maponpaths (compose _) (functor_comp homLR1 _ _)).
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  unfold internal_postcomp, internal_lam, internal_eval.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (compose _) (functor_comp homLR1 _ _) @ _). 
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (assoc' _ _ _ @ _).
  set (triangle_eq := pr222 (pr2 E (L R1)) (K S2)).
  refine (maponpaths (compose _) triangle_eq @ _); clear triangle_eq.
  refine (pr2 (pr121 (pr111 E)) _ _ _ @ _).
  unfold homLR2.
  refine (maponpaths (postcompose _) (hom_onmorphisms_is_postcomp (L R2) (pr1 k R2 S2)) @ _).
  refine (_ @ ! maponpaths (compose _) (hom_onmorphisms_is_postcomp (L R1) (pr1 k R2 S2))).
  exact (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _).

  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) righteq @ _); clear righteq.
  set (whiskereq := pr122 (pr212 (pr211 E)) (L R1) (K (R2 ⊗_{C} S2)) _ _ (# K (R2 ⊗^{ pr11 C}_{l} g12)) (# K (f12 ⊗^{ pr11 C}_{r} S1))).
  refine (_ @ ! maponpaths (λ f, _ · (# homLR1 f) · _) whiskereq); clear whiskereq.
  refine (_ @ ! maponpaths (λ f, _ · f · _) (functor_comp homLR1 _ _ )).
  refine (assoc _ _ _ @ _ @ maponpaths (postcompose _) (assoc' _ _ _)).
  refine (assoc _ _ _ @ _ @ assoc _ _ _).
  
  assert (# homLR1 (braid _ _ · # L f12 ⊗^{E}_{r} _) · # homLR1 (pr1 k R2 S1) = # homLR1 (# K (f12 ⊗^{ pr11 C}_{r} S1) ⊗^{ pr121 (pr1 E)}_{r} L R1) · # homLR1 (braid (K (R1 ⊗_{ C} S1)) (L R1)· pr1 k R1 S1)) as bottomeq.
  refine (! functor_comp homLR1 _ _ @ _ @ functor_comp homLR1 _ _).
  apply maponpaths.
  refine (assoc' _ _ _ @ _ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose (C:=E) _) (pr21 (pr221 E) _ _ _ _)).
  refine (_ @ assoc _ _ _).
  apply maponpaths.  
  set (kdnateq' := pr122 k S1 R1 R2 f12).  
  set (kdnateq := ! maponpaths (compose _) (pr2 (pr121 (pr111 E)) _ _ _) @ kdnateq' @ maponpaths (compose _) (pr2 (pr121 (pr111 E)) _ _ _)).
  exact (! kdnateq ).
  refine (_ @ maponpaths (compose _) bottomeq); clear bottomeq.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ assoc _ _ _).
  assert (# homLR1 (braid _ _) · # homLR1 (# L f12 ⊗^{E}_{r} _)· # homLR1 (L R2 ⊗^{ E}_{l} # K (R2 ⊗^{ C}_{l} g12)) =
            # homLR1 (# K (R2 ⊗^{ pr11 C}_{l} g12) ⊗^{ pr121 (pr1 E)}_{r} L R1)
              · # homLR1 (braid (K (R2 ⊗_{ C} S1)) (L (pr1 (R1,, S1))) · # L f12 ⊗^{ E}_{r} K (R2 ⊗_{ C} S1))) as middleq.
  refine (maponpaths (postcompose _) (! functor_comp homLR1 _ _) @ _).
  refine (! functor_comp homLR1 _ _ @ _ @ functor_comp homLR1 _ _).
  apply maponpaths.
  refine (_ @ assoc' _ _ _).
  refine (_ @ maponpaths (postcompose _) (pr21 (pr221 E) _ _ _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  exact (pr222 (pr212 (pr211 E)) _ _ _ _ _ _).
  refine (_ @ maponpaths (compose _) middleq); clear middleq.
  refine (_ @ assoc' _ _ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ maponpaths (compose _) (functor_comp homLR1 _ _)).
  assert (# homLR1 (_ ⊗^{ E}_{l} # L f12 · braid _ _) =
            # homLR1 (braid (K (R2 ⊗_{ C} pr2 (R2,, S2))) (L (pr1 (R1,, S1))) · # L f12 ⊗^{ E}_{r} K (R2 ⊗_{ C} pr2 (R2,, S2)))) as topmiddleq.
  apply maponpaths.
  exact (! pr11 (pr221 E) _ _ _ _).
  refine (_ @ maponpaths (compose _) topmiddleq); clear topmiddleq.
  refine (_ @ maponpaths (compose _) (! functor_comp homLR1 _ _)).
  refine (_ @ assoc' _ _ _).
  assert (# homLR2 (braid (K (R2 ⊗_{ C} S2)) (L R2)) · internal_precomp (# L f12) (L R2 ⊗_{ E} K (R2 ⊗_{ C} S2)) =
            internal_precomp (# L f12) _ ·  # homLR1 (braid (K (R2 ⊗_{ C} S2)) (L R2))) as toprighteq.
  refine (maponpaths (postcompose _) (hom_onmorphisms_is_postcomp (L R2) _) @ _).
  refine (_ @ ! maponpaths (compose _) (hom_onmorphisms_is_postcomp (L R1) _)).
  exact (! internal_pre_post_comp_as_post_pre_comp _ _ @ internal_pre_post_comp_as_pre_post_comp _ _).
  refine (maponpaths (compose _) toprighteq @ _); clear toprighteq.
  refine (assoc _ _ _ @ _).
  apply (maponpaths (postcompose _)).
  refine (_ @ ! maponpaths (compose _) (hom_onmorphisms_is_postcomp _ _)).
  exact (! mon_closed_adj_natural E _ _ _ _). 
Qed.
  
