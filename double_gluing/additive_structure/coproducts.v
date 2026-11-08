Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Local Open Scope cat.

Require Import preliminaries.
Require Import double_pullbacks.
Require Import natural_contraction.

Require Import double_gluing.double_gluing.
(*
Require Import double_gluing.closed.adjunction. (* there is a lemma here that should be moved to double_gluing.v *) *)



Definition BinCoproduct_doublePullback_type {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E) {L : functor C E}
  {K : functor C (E ^opp)} (A B : double_glued_total_cat L K) : UU.
Proof.
  set (R := pr1 A); set (X := pr122 A); set (l' := pr222 A).
  set (S := pr1 B); set (Y := pr122 B); set (m' := pr222 B).
  use doublePullback.
  exact E.
  exact X.
  exact (K R).
  exact (K (copc R S)).
  exact (K S).
  exact Y.
  exact l'.
  apply (# K).
  apply BinCoproductIn1.
  apply (# K).
  apply BinCoproductIn2.
  exact m'.
Defined.

Definition BinCoproduct_doublePullback {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E) (dpb : doublePullbacks E)
  {L : functor C E} {K : functor C (E ^opp)} (A B : double_glued_total_cat L K) : BinCoproduct_doublePullback_type copc cope A B.
Proof.
  apply dpb.
Defined.

Definition double_glued_BinCoproductObj {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E) (dpb : doublePullbacks E)
  {L : functor C E} {K : functor C (E ^opp)} (A B : double_glued_total_cat L K) : double_glued_total_cat L K.
Proof.
  set (R := pr1 A); set (U := pr112 A); set (l := pr212 A).
  set (S := pr1 B); set (V := pr112 B); set (m := pr212 B).
  exists (copc R S).
  split.
  exists (cope U V).
  apply BinCoproductArrow.
  apply (compose l), (# L).
  apply BinCoproductIn1.
  apply (compose m), (# L).
  apply BinCoproductIn2.
  set (codpb := BinCoproduct_doublePullback copc cope dpb A B).
  exists (doublePullbackObject codpb).
  apply doublePullbackPrM.
Defined.

Definition double_glued_BinCoproduct_In1 {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E) (dpb : doublePullbacks E)
  {L : functor C E} {K : functor C (E ^opp)} (A B : double_glued_total_cat L K) : 
  double_glued_total_cat L K ⟦ A, double_glued_BinCoproductObj copc cope dpb A B ⟧.
Proof.
  use tpair.
  apply BinCoproductIn1.
  split; use tpair.
  apply BinCoproductIn1.
  apply BinCoproductIn1Commutes.
  apply doublePullbackPrL.
  apply pathsinv0.
  apply doublePullbackSqrLCommutes.
Defined.

Definition double_glued_BinCoproduct_In2 {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E) (dpb : doublePullbacks E)
  {L : functor C E} {K : functor C (E ^opp)} (A B : double_glued_total_cat L K) : 
  double_glued_total_cat L K ⟦ B, double_glued_BinCoproductObj copc cope dpb A B ⟧.
Proof.
  use tpair.
  apply BinCoproductIn2.
  split; use tpair.
  apply BinCoproductIn2.
  apply BinCoproductIn2Commutes.
  apply doublePullbackPrR.
  apply doublePullbackSqrRCommutes.
Defined.



Definition double_glued_CoprodisBinCoproduct_lemma1_type {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E)
  (dpb : doublePullbacks E) {L : functor C E} {K : functor C (E ^opp)} {A A' B : double_glued_total_cat L K}
  (tf1 : A --> B) (tf2 : A' --> B) : UU.
Proof.
  destruct A as (R, ((U, l), (X, l'))).
  destruct A' as (S, ((V, m), (Y, m'))).
  destruct B as (T, ((W, n), (Z, n'))).
  destruct tf1 as (f1, ((ϕ1, eqphi1), (ψ1, eqpsi1))).
  destruct tf2 as (f2, ((ϕ2, eqphi2), (ψ2, eqpsi2))).
  exact (BinCoproductArrow (cope U V) ϕ1 ϕ2 · n =
           BinCoproductArrow (cope U V) (l · # L (BinCoproductIn1 (copc R S))) (m · # L (BinCoproductIn2 (copc R S)))
             · # L (BinCoproductArrow (copc R S) f1 f2)).
Defined.

Lemma double_glued_CoprodisBinCoproduct_lemma1 {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E)
  (dpb : doublePullbacks E) {L : functor C E} {K : functor C (E ^opp)} {A A' B : double_glued_total_cat L K}
  (tf1 : A --> B) (tf2 : A' --> B) : double_glued_CoprodisBinCoproduct_lemma1_type copc cope dpb tf1 tf2.
Proof.
  destruct tf1 as (f1, ((ϕ1, eqphi1), (ψ1, eqpsi1))).
  destruct tf2 as (f2, ((ϕ2, eqphi2), (ψ2, eqpsi2))).
  apply BinCoproductArrowsEq.
  refine (assoc _ _ _ @ _ @ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply BinCoproductIn1Commutes.
  2 : {
    apply cancel_postcomposition.
    apply pathsinv0, BinCoproductIn1Commutes.
  }
  refine (eqphi1 @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ functor_comp L _ _).
  apply maponpaths.
  apply pathsinv0, BinCoproductIn1Commutes. 
  refine (assoc _ _ _ @ _ @ _ @ _ @ assoc' _ _ _).
  apply cancel_postcomposition.
  apply BinCoproductIn2Commutes.
  2 : {
    apply cancel_postcomposition.
    apply pathsinv0, BinCoproductIn2Commutes.
  }
  refine (eqphi2 @ _ @ assoc _ _ _).
  apply maponpaths.
  refine (_ @ functor_comp L _ _).
  apply maponpaths.
  apply pathsinv0, BinCoproductIn2Commutes.
Qed.

Lemma double_glued_CoprodisBinCoproduct_lemma2 {C E : category} (copc : BinCoproducts C) {K : functor C (E ^opp)} {R S T: C}
  {X Z: E} {l' : E ⟦ X, K R ⟧} {n' : E ⟦Z, K T⟧} {f1 : C ⟦ R, T ⟧} (f2 : C ⟦ S, T ⟧) {ψ1 : E ⟦ Z, X ⟧}  (eqpsi1 : # K f1 · n' = ψ1 · l') :
  ψ1 · l' = n' · # K (BinCoproductArrow (copc R S) f1 f2) · # K (BinCoproductIn1 (copc R S)).
Proof.
  refine (! eqpsi1 @ _).
  refine (_ @ assoc' _ _ _).
  apply cancel_postcomposition.
  refine (_ @ functor_comp K _ _).
  apply maponpaths.
  apply pathsinv0, BinCoproductIn1Commutes. 
Qed.

Lemma double_glued_CoprodisBinCoproduct_lemma3 {C E : category} (copc : BinCoproducts C) {K : functor C (E ^opp)} {R S T: C}
  {Y Z: E} {m' : E ⟦ Y, K S ⟧} {n' : E ⟦Z, K T⟧} (f1 : C ⟦ R, T ⟧) {f2 : C ⟦ S, T ⟧} {ψ2 : E ⟦ Z, Y ⟧} (eqpsi2 : # K f2 · n' = ψ2 · m') :
  n' · # K (BinCoproductArrow (copc R S) f1 f2) · # K (BinCoproductIn2 (copc R S)) = ψ2 · m'.
Proof.
  refine (_ @ eqpsi2).
  refine (assoc' (C:=E) _ _ _ @ _).
  apply (maponpaths (compose (C:=E) _)).
  refine (! functor_comp K _ _ @ _).
  apply maponpaths.
  apply BinCoproductIn2Commutes.
Qed.

Definition double_glued_BinCoproductArrow {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E)
  (dpb : doublePullbacks E) {L : functor C E} {K : functor C (E ^opp)} {A A' B : double_glued_total_cat L K}
  (tf1 : double_glued_total_cat L K ⟦ A, B ⟧) (tf2 : double_glued_total_cat L K ⟦ A', B ⟧):
  double_glued_total_cat L K ⟦ double_glued_BinCoproductObj copc cope dpb A A', B ⟧.
Proof.
  use tpair.
  apply BinCoproductArrow.
  apply tf1.
  apply tf2.
  split; use tpair.
  apply BinCoproductArrow.
  apply tf1.
  apply tf2.
  simpl.
  apply (double_glued_CoprodisBinCoproduct_lemma1 copc cope dpb tf1 tf2).
  destruct A as (R, ((U, l), (X, l'))).
  destruct A' as (S, ((V, m), (Y, m'))).
  destruct B  as (T, ((W, n), (Z, n'))).
  simpl.
  destruct tf1 as (f1, ((ϕ1, eqphi1), (ψ1, eqpsi1))).
  destruct tf2 as (f2, ((ϕ2, eqphi2), (ψ2, eqpsi2))).
  use doublePullbackArrow; try assumption.
  apply (compose (C:=E) n').
  apply (# K).
  apply BinCoproductArrow; assumption.
  apply (double_glued_CoprodisBinCoproduct_lemma2 copc f2 eqpsi1).
  apply (double_glued_CoprodisBinCoproduct_lemma3 copc f1 eqpsi2).
  simpl. (* necessary *)
  refine (! doublePullbackArrow_PrM _ _ _ _ _ _ _).
Defined.
                                                                                                                      
Lemma double_glued_BinCoproductArrowIn1Commutes {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E)
  (dpb : doublePullbacks E) {L : functor C E} {K : functor C (E ^opp)} (A A' B : double_glued_total_cat L K)
  (tf1 : double_glued_total_cat L K ⟦ A, B ⟧) (tf2 : double_glued_total_cat L K ⟦ A', B ⟧) :
    double_glued_BinCoproduct_In1 copc cope dpb A A' · double_glued_BinCoproductArrow copc cope dpb tf1 tf2 = tf1.
Proof.
  use total2_paths_f.
  apply BinCoproductIn1Commutes.
  apply dirprod_paths; apply subtypePath_prop;
    induction (BinCoproductIn1Commutes C (pr1 A) (pr1 A') (copc (pr1 A) (pr1 A')) (pr1 B) (pr1 tf1) (pr1 tf2)).
  apply BinCoproductIn1Commutes.
  apply (doublePullbackArrow_PrL (BinCoproduct_doublePullback copc cope dpb A A')).
Qed.

                                                                                                                      
Lemma double_glued_BinCoproductArrowIn2Commutes {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E)
  (dpb : doublePullbacks E) {L : functor C E} {K : functor C (E ^opp)} (A A' B : double_glued_total_cat L K)
  (tf1 : double_glued_total_cat L K ⟦ A, B ⟧) (tf2 : double_glued_total_cat L K ⟦ A', B ⟧) :
    double_glued_BinCoproduct_In2 copc cope dpb A A' · double_glued_BinCoproductArrow copc cope dpb tf1 tf2 = tf2.
Proof.
  use total2_paths_f.
  apply BinCoproductIn2Commutes.
  apply dirprod_paths; apply subtypePath_prop;
    induction (BinCoproductIn2Commutes C (pr1 A) (pr1 A') (copc (pr1 A) (pr1 A')) (pr1 B) (pr1 tf1) (pr1 tf2)).
  apply BinCoproductIn2Commutes.
  apply (doublePullbackArrow_PrR (BinCoproduct_doublePullback copc cope dpb A A')).
Qed.

Lemma double_glued_total_mor_eq_transp {C E : category} {L : functor C E} {K : functor C (E^opp)}
  {x y : ob (double_glued_total_cat L K)} (f g : x --> y) :
  (pr1 f = pr1 g) × (pr112 f = pr112 g) × (pr122 f = pr122 g) → f = g.
Proof.
  intros (eq1, (eq2, eq3)).
  use total2_paths_b.
  assumption.
  unfold transportb.
  apply (pr2 (double_glued_mor_eq_transp eq1 (pr2 f) (pr2 g))).
  exact (eq2,, eq3).
Qed.

Definition double_glued_CoprodisBinCoproduct {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E)
  (dpb : doublePullbacks E) {L : functor C E} {K : functor C (E ^opp)} (A A' : double_glued_total_cat L K) :
  isBinCoproduct (double_glued_total_cat L K) A A' (double_glued_BinCoproductObj copc cope dpb A A')
    (double_glued_BinCoproduct_In1 copc cope dpb A A') (double_glued_BinCoproduct_In2 copc cope dpb A A').
Proof.
  intros B. 
  intros tf1 tf2.
  use tpair.
  exists (double_glued_BinCoproductArrow copc cope dpb tf1 tf2).
  split.
  apply double_glued_BinCoproductArrowIn1Commutes.
  apply double_glued_BinCoproductArrowIn2Commutes.
  simpl.
  simpl.
  intros (t, (teq1, teq2)).
  apply subtypePath.
  intros t'.
  use isofhleveldirprod.
  apply (pr2 (double_glued_total_cat L K) _ _ _ tf1).
  apply (pr2 (double_glued_total_cat L K) _ _ _ tf2).
  simpl.
  apply (double_glued_total_mor_eq_transp (L:=L) (K:=K) (x:= double_glued_BinCoproductObj copc cope dpb A A') t _).
  assert (baseeq : pr1 t = pr1 (double_glued_BinCoproductArrow copc cope dpb tf1 tf2)).
  apply BinCoproductArrowUnique.
  simpl.
  apply (maponpaths pr1 teq1).
  apply (maponpaths pr1 teq2).
  split3.
  assumption.
  apply BinCoproductArrowUnique.
  simpl.
  refine (maponpaths (λ x, pr112 x) teq1).
  refine (maponpaths (λ x, pr112 x) teq2).  
  apply doublePullbackArrowUnique'.
  refine (maponpaths (λ x, pr122 x) teq1).
  2 : {
    refine (maponpaths (λ x, pr122 x) teq2).
  }
  refine (! pr222 t @ _).
  apply (cancel_precomposition E).
  apply maponpaths.
  assumption.
Qed.

Definition double_glued_BinCoproduct {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E) (dpb : doublePullbacks E)
  (L : functor C E) (K : functor C (E ^opp)) (A B : double_glued_total_cat L K) : BinCoproduct A B.
Proof.
  unfold BinCoproduct.
  use tpair.
  exists (double_glued_BinCoproductObj copc cope dpb A B).
  split.
  apply double_glued_BinCoproduct_In1.
  apply double_glued_BinCoproduct_In2.
  apply double_glued_CoprodisBinCoproduct.
Defined.

Definition double_glued_BinCoproducts  {C E : category} (copc : BinCoproducts C) (cope : BinCoproducts E) (dpb : doublePullbacks E)
  (L : functor C E) (K : functor C (E ^opp)) : BinCoproducts (double_glued_total_cat L K).
Proof.
  use double_glued_BinCoproduct; assumption.
Defined.
