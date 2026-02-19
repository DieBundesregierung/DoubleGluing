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


(* Pullback of cospans L1->M1<-LR LR->M2<-R2 *)
Definition doublePullback {C : category} {L1 M1 LR M2 R2: C} (pb : Pullbacks C) (f1 : C⟦L1, M1⟧) (g1 : C⟦LR, M1⟧) (f2 : C⟦LR, M2⟧) (g2 : C⟦R2, M2⟧) : UU. 
Proof.
  set (P1:= pb M1 L1 LR f1 g1).
  set (P2:= pb M2 LR R2 f2 g2).
  exact (Pullback (C:=C) (a:=LR) (b:= pr11 P1) (c:= pr11 P2) (pr221 P1) (pr121 P2)).
Defined.

Lemma doublePullback_exists {C : category} {L1 M1 LR M2 R2: C} (pb : Pullbacks C) (f1 : C⟦L1, M1⟧) (g1 : C⟦LR, M1⟧) (f2 : C⟦LR, M2⟧) (g2 : C⟦R2, M2⟧) :
  doublePullback pb f1 g1 f2 g2. 
Proof.
  apply pb.
Defined.

Definition doublePullbackObject {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : ob C := pr11 dpb.

Definition doublePullbackPb1 {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : Pullback f1 g1 := pb _ _ _ f1 g1.

Definition doublePullbackPb2 {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : Pullback f2 g2 := pb _ _ _ f2 g2.

Definition doublePullbackPrL {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : C ⟦doublePullbackObject dpb, L1⟧ := compose (PullbackPr1 _) (PullbackPr1 _).

Definition doublePullbackPr21 {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : C ⟦doublePullbackObject dpb, LR⟧ := compose (PullbackPr1 _) (PullbackPr2 _).

Definition doublePullbackPr12 {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : C ⟦doublePullbackObject dpb, LR⟧ := compose (PullbackPr2 _) (PullbackPr1 _).

Lemma doublePullbackPr12_eq_Pr21 {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : doublePullbackPr21 dpb = doublePullbackPr12 dpb.
Proof.
  exact (PullbackSqrCommutes dpb).
Qed.

Definition doublePullbackPrM {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : C ⟦doublePullbackObject dpb, LR⟧ := doublePullbackPr21 dpb.

Definition doublePullbackPrR {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : C ⟦doublePullbackObject dpb, R2⟧ := compose (PullbackPr2 _) (PullbackPr2 _).

Lemma doublePullbackSqrLCommutes {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : doublePullbackPrL dpb · f1 = doublePullbackPrM dpb · g1.
Proof.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (PullbackSqrCommutes _) @ _).
  exact (assoc _ _ _).
Qed.

Lemma doublePullbackSqrRCommutes {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) : doublePullbackPrM dpb · f2 = doublePullbackPrR dpb · g2.
Proof.
  rewrite doublePullbackPr12_eq_Pr21.
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (compose _) (PullbackSqrCommutes _) @ _).
  exact (assoc _ _ _).
Qed.

Definition doublePullbackSqrMCommutes {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) := doublePullbackPr12_eq_Pr21 dpb.

Definition doublePullback_universal_statement {C : category} {L1 M1 LR M2 R2: C} (pb : Pullbacks C) (f1 : C⟦L1, M1⟧) (g1 : C⟦LR, M1⟧) (f2 : C⟦LR, M2⟧) (g2 : C⟦R2, M2⟧) (dpb : doublePullback pb f1 g1 f2 g2) : UU.
Proof.
  refine (∏ X : C, ∏ arrows : C⟦ X, L1⟧ × C⟦ X, LR⟧ × C⟦ X, R2⟧, _ → ∃! f: C⟦ X, pr11 dpb⟧, _);
  destruct arrows as (fl1, (flr, fr2)).
  exact ((fl1 · f1 = flr · g1) × (flr · f2 = fr2 · g2)).
  set (pr121 dpb).
  set (pb1 := pb M1 L1 LR f1 g1).
  set (pb2 := pb M2 LR R2 f2 g2).
  exact ((fl1 = f · pr121 dpb · pr121 pb1) × (flr = f · pr121 dpb · pr221 pb1) × (flr = f · pr221 dpb · pr121 pb2) × (fr2 = f · pr221 dpb · pr221 pb2)).
Defined.

Definition doublePullback_universal {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback pb f1 g1 f2 g2) : doublePullback_universal_statement pb f1 g1 f2 g2 dpb.
Proof.
  set (pb1 := pb M1 L1 LR f1 g1).
  set (pb2 := pb M2 LR R2 f2 g2).
  intros X (fl1, (flr, fr2)) (comm1, comm2).
  set (fxp1 := pr11 (pr22 pb1 X fl1 flr comm1)).
  set (fxp2 := pr11 (pr22 pb2 X flr fr2 comm2)).
  set (dpbeq := pr221 (pr22 pb1 X fl1 flr comm1) @ ! pr121 (pr22 pb2 X flr fr2 comm2)).
  use tpair.
  use tpair.
  exact (pr11 (pr22 dpb X fxp1 fxp2 dpbeq)).
  set (arr1 := pr121 dpb).
  set (arr2 := pr221 dpb).
  split4.
  refine (! pr121 (pr22 pb1 X fl1 flr comm1) @ _).
  exact (! maponpaths (postcompose (pr121 pb1)) (pr121 (pr22 dpb X fxp1 fxp2 dpbeq))).
  refine (! pr121 (pr22 pb2 X flr fr2 comm2) @ _).
  refine (! maponpaths (postcompose (pr121 pb2)) (pr221 (pr22 dpb X fxp1 fxp2 dpbeq)) @ _).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  exact (maponpaths (compose _) (! pr12 dpb)).
  refine (! pr121 (pr22 pb2 X flr fr2 comm2) @ _).
  exact (! maponpaths (postcompose (pr121 pb2)) (pr221 (pr22 dpb X fxp1 fxp2 dpbeq))).
  refine (! pr221 (pr22 pb2 X flr fr2 comm2) @ _).
  exact (maponpaths (postcompose _) (! pr221 (pr22 dpb X fxp1 fxp2 dpbeq))).
  simpl.
  intros (f, comms).
  apply subtypePath.
  intros fxdpb.
  repeat try apply isapropdirprod; apply (pr2 C _ _).
  refine (maponpaths pr1 (pr2 (pr22 dpb X fxp1 fxp2 dpbeq) (f,, _))).
  split.
  refine (maponpaths pr1 (pr2 ((pr22 pb1) X fl1 flr comm1) (f · pr121 dpb,, _))).
  exact (! pr1 comms,, ! pr12 comms).
  refine (maponpaths pr1 (pr2 ((pr22 pb2) X flr fr2 comm2) (f · pr221 dpb,, _))).
  exact (! pr122 comms,, ! pr222 comms).
Qed.

Definition doublePullbackArrow {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1) (eq2 : hm · f2 = hr · g2) :
  C⟦X, doublePullbackObject dpb⟧.
Proof.
  use PullbackArrow.
  use PullbackArrow.
  exact hl.
  exact hm.
  exact eq1.
  use PullbackArrow.
  exact hm.
  exact hr.
  exact eq2.
  refine (PullbackArrow_PullbackPr2 (doublePullbackPb1 dpb) X hl hm eq1 @ _).
  exact (! PullbackArrow_PullbackPr1 (doublePullbackPb2 dpb) X hm hr eq2).
Defined.

Lemma doublePullbackArrowUnique {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧}
  (dpb : doublePullback pb f1 g1 f2 g2) (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (sqr1 : hl · f1 = hm · g1) (sqr2 : hm · f2 = hr · g2)
  (w : C⟦X, doublePullbackObject dpb⟧) (trian1 : w · doublePullbackPrL dpb = hl) (trian2 : w · doublePullbackPrM dpb = hm)
  (trian3 : w · doublePullbackPrR dpb = hr) :
  w = doublePullbackArrow dpb X hl hm hr sqr1 sqr2.
Proof.
  apply PullbackArrowUnique';
    apply PullbackArrowUnique';
    rewrite assoc'; try assumption.
  refine (_ @ trian2).
  apply maponpaths.
  exact (! doublePullbackSqrMCommutes dpb).
Qed.

Lemma doublePullbackArrow_PrL {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback pb f1 g1 f2 g2) (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1) (eq2 : hm · f2 = hr · g2) :
  doublePullbackArrow dpb X hl hm hr eq1 eq2 · doublePullbackPrL dpb = hl.
Proof.
  unfold doublePullbackArrow, doublePullbackPrL.
  rewrite assoc.
  refine (_ @ PullbackArrow_PullbackPr1 (doublePullbackPb1 dpb) X hl hm eq1).
  apply (maponpaths (postcompose _)).
  apply PullbackArrow_PullbackPr1.
Qed.

Lemma doublePullbackArrow_Pr21 {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback pb f1 g1 f2 g2) (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1) (eq2 : hm · f2 = hr · g2) :
  doublePullbackArrow dpb X hl hm hr eq1 eq2 · doublePullbackPr21 dpb = hm.
Proof.
  unfold doublePullbackArrow, doublePullbackPr21.
  rewrite assoc.
  refine (_ @ PullbackArrow_PullbackPr2 (doublePullbackPb1 dpb) X hl hm eq1).
  apply (maponpaths (postcompose _)).
  apply PullbackArrow_PullbackPr1.
Qed.

Lemma doublePullbackArrow_Pr12 {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback pb f1 g1 f2 g2) (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1) (eq2 : hm · f2 = hr · g2) :
  doublePullbackArrow dpb X hl hm hr eq1 eq2 · doublePullbackPr12 dpb = hm.
Proof.
  unfold doublePullbackArrow, doublePullbackPr12.
  rewrite assoc.
  refine (_ @ PullbackArrow_PullbackPr1 (doublePullbackPb2 dpb) X hm hr eq2).
  apply (maponpaths (postcompose _)).
  apply PullbackArrow_PullbackPr2.
Qed.

Lemma doublePullbackArrow_PrM {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback pb f1 g1 f2 g2) (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1) (eq2 : hm · f2 = hr · g2) :
  doublePullbackArrow dpb X hl hm hr eq1 eq2 · doublePullbackPrM dpb = hm.
Proof.
  apply doublePullbackArrow_Pr21.
Qed.

Lemma doublePullbackArrow_PrR {C : category} {L1 M1 LR M2 R2: C} {pb : Pullbacks C} {f1 : C⟦L1, M1⟧} {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback pb f1 g1 f2 g2) (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1) (eq2 : hm · f2 = hr · g2) :
  doublePullbackArrow dpb X hl hm hr eq1 eq2 · doublePullbackPrR dpb = hr.
Proof.
  unfold doublePullbackArrow, doublePullbackPrR.
  rewrite assoc.
  refine (_ @ PullbackArrow_PullbackPr2 (doublePullbackPb2 dpb) X hm hr eq2).
  apply (maponpaths (postcompose _)).
  apply PullbackArrow_PullbackPr2.
Qed.


