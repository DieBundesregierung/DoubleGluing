(**********************************************

This file contains definitions and results regarding double pullbacks.
The implementation is in style kept similar to UniMath.CategoryTheory.Limits.Pullbacks.

 **********************************************)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Local Open Scope cat.

Require Import preliminaries.


(* Pullback of cospans L1->M1<-LR LR->M2<-R2 *)

Definition isdoublePullback {C : category} {L M1 S M2 R P: C} (f1 : C⟦L, M1⟧) (g1 : C⟦S, M1⟧) (f2 : C⟦S, M2⟧) (g2 : C⟦R, M2⟧) (pl : C⟦P, L⟧) (pm : C⟦P, S⟧) (pr : C⟦P, R⟧) (Hl : pl · f1 = pm · g1) (Hr : pm · f2 = pr · g2) : UU :=
  ∏ Q (ql : C⟦Q, L⟧) (qm : C⟦Q, S⟧) (qr : C⟦Q, R⟧)
    (H1 : ql · f1 = qm · g1) (H2 : qm · f2 = qr · g2),
    ∃! qp : C⟦Q, P⟧, (qp · pl = ql) × (qp · pm = qm) × (qp · pr = qr).

Lemma isaprop_isdoublePullback {C : category} {L M1 S M2 R P: C} (f1 : C⟦L, M1⟧) (g1 : C⟦S, M1⟧) (f2 : C⟦S, M2⟧) (g2 : C⟦R, M2⟧) (pl : C⟦P, L⟧) (pm : C⟦P, S⟧) (pr : C⟦P, R⟧) (H1 : pl · f1 = pm · g1) (H2 : pm · f2 = pr · g2) :
       isaprop (isdoublePullback f1 g1 f2 g2 pl pm pr H1 H2).
Proof.
  repeat (apply impred; intro).
  apply isapropiscontr.
Qed.

Lemma doublePullbackArrowUnique {C : category} {L M1 S M2 R P: C} {f1 : C⟦L, M1⟧}
  {g1 : C⟦S, M1⟧} {f2 : C⟦S, M2⟧} {g2 : C⟦R, M2⟧} {pl : C⟦P, L⟧} {pm : C⟦P, S⟧}
  {pr : C⟦P, R⟧} {H1 : pl · f1 = pm · g1} {H2 : pm · f2 = pr · g2}
  (dp : isdoublePullback f1 g1 f2 g2 pl pm pr H1 H2) Q (ql : C⟦Q, L⟧) (qm : C⟦Q, S⟧)
  (qr : C⟦Q, R⟧) (H1' : ql · f1 = qm · g1) (H2' : qm · f2 = qr · g2) (qp : C⟦Q, P⟧)
  (Hl' : qp · pl = ql) (Hm : qp · pm = qm) (Hr : qp · pr = qr) :
  qp = (pr11 (dp Q ql qm qr H1' H2')).
Proof.
  refine (base_paths _ _ (pr2 (dp Q ql qm qr H1' H2') (qp,, _))).
  easy.
Qed.

Definition doublePullback {C : category} {L M1 S M2 R : C} (f1 : C⟦L, M1⟧) (g1 : C⟦S, M1⟧)
  (f2 : C⟦S, M2⟧) (g2 : C⟦R, M2⟧) : UU :=
  (∑ cosp : (∑ P : C, C⟦P, L⟧ × C⟦P, S⟧ × C⟦P, R⟧),
      ∑ (Hs : (pr12 cosp · f1 = pr122 cosp · g1) × (pr122 cosp · f2 = pr222 cosp · g2)),
      isdoublePullback f1 g1 f2 g2 (pr12 cosp) (pr122 cosp) (pr222 cosp) (pr1 Hs) (pr2 Hs)).

Definition doublePullbacks (C : category) : UU :=
  ∏ (L M1 S M2 R : C) (f1 : C⟦L, M1⟧) (g1 : C⟦S, M1⟧) (f2 : C⟦S, M2⟧) (g2 : C⟦R, M2⟧),
    doublePullback f1 g1 f2 g2.

Definition hasdoublePullbacks (C : category) : UU :=
  ∀ (L M1 S M2 R : C) (f1 : C⟦L, M1⟧) (g1 : C⟦S, M1⟧) (f2 : C⟦S, M2⟧) (g2 : C⟦R, M2⟧),
    ∥ doublePullback f1 g1 f2 g2 ∥.

Definition doublePullbackObject {C : category} {L M1 S M2 R: C} {f1 : C⟦L, M1⟧}
  {g1 : C⟦S, M1⟧} {f2 : C⟦S, M2⟧} {g2 : C⟦R, M2⟧} (dpb : doublePullback f1 g1 f2 g2) : ob C
  := pr11 dpb.

Definition doublePullbackPrL {C : category} {L M1 S M2 R: C} {f1 : C⟦L, M1⟧}
  {g1 : C⟦S, M1⟧} {f2 : C⟦S, M2⟧} {g2 : C⟦R, M2⟧} (dpb : doublePullback f1 g1 f2 g2) :
  C ⟦doublePullbackObject dpb, L⟧ := pr121 dpb.

Definition doublePullbackPrM {C : category} {L M1 S M2 R: C} {f1 : C⟦L, M1⟧}
  {g1 : C⟦S, M1⟧} {f2 : C⟦S, M2⟧} {g2 : C⟦R, M2⟧} (dpb : doublePullback f1 g1 f2 g2) :
  C ⟦doublePullbackObject dpb, S⟧ := pr1 (pr221 dpb).

Definition doublePullbackPrR {C : category} {L M1 S M2 R: C} {f1 : C⟦L, M1⟧}
  {g1 : C⟦S, M1⟧} {f2 : C⟦S, M2⟧} {g2 : C⟦R, M2⟧} (dpb : doublePullback f1 g1 f2 g2) :
  C ⟦doublePullbackObject dpb, R⟧ := pr2 (pr221 dpb).

Lemma doublePullbackSqrLCommutes {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2) :
  doublePullbackPrL dpb · f1 = doublePullbackPrM dpb · g1.
Proof.
  apply dpb.
Qed.

Lemma doublePullbackSqrRCommutes {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2) :
  doublePullbackPrM dpb · f2 = doublePullbackPrR dpb · g2.
Proof.
  apply dpb.
Qed.

Lemma isdoublePullback_doublePullback {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2) :
  isdoublePullback f1 g1 f2 g2 (doublePullbackPrL dpb) (doublePullbackPrM dpb)
    (doublePullbackPrR dpb) (doublePullbackSqrLCommutes dpb)
    (doublePullbackSqrRCommutes dpb).
Proof.
  apply dpb.
Qed.
(*
Definition doublePullbackArrowSqrL {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2)
  (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) := hl · f1 = hm · g1.

Definition doublePullbackArrowSqrR {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2)
  (X : C) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) := hm · f2 = hr · g2. *)

Definition doublePullbackArrow {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2)
  (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1)
  (eq2 : hm · f2 = hr · g2) : C⟦X, doublePullbackObject dpb⟧.
Proof.
  exact (pr11 (isdoublePullback_doublePullback dpb X hl hm hr eq1 eq2)).
Defined.

Lemma doublePullbackArrowUnique' {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2)
  (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (sqr1 : hl · f1 = hm · g1)
  (sqr2 : hm · f2 = hr · g2) (w : C⟦X, doublePullbackObject dpb⟧)
  (trian1 : w · doublePullbackPrL dpb = hl) (trian2 : w · doublePullbackPrM dpb = hm)
  (trian3 : w · doublePullbackPrR dpb = hr) :
  w = doublePullbackArrow dpb X hl hm hr sqr1 sqr2.
Proof.
  now apply doublePullbackArrowUnique.
Qed.

Lemma doublePullbackArrow_PrL {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2)
  (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1)
  (eq2 : hm · f2 = hr · g2) :
  doublePullbackArrow dpb X hl hm hr eq1 eq2 · doublePullbackPrL dpb = hl.
Proof.
  apply (pr1 (isdoublePullback_doublePullback dpb X hl hm hr eq1 eq2)).
Qed.

Lemma doublePullbackArrow_PrM {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2)
  (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1)
  (eq2 : hm · f2 = hr · g2) :
  doublePullbackArrow dpb X hl hm hr eq1 eq2 · doublePullbackPrM dpb = hm.
Proof.
  apply (pr1 (isdoublePullback_doublePullback dpb X hl hm hr eq1 eq2)).
Qed.

Lemma doublePullbackArrow_PrR {C : category} {L1 M1 LR M2 R2: C} {f1 : C⟦L1, M1⟧}
  {g1 : C⟦LR, M1⟧} {f2 : C⟦LR, M2⟧} {g2 : C⟦R2, M2⟧} (dpb : doublePullback f1 g1 f2 g2)
  (X : C) (hl : C⟦X, L1⟧) (hm : C⟦X, LR⟧) (hr : C⟦X, R2⟧) (eq1 : hl · f1 = hm · g1)
  (eq2 : hm · f2 = hr · g2) :
  doublePullbackArrow dpb X hl hm hr eq1 eq2 · doublePullbackPrR dpb = hr.
Proof.
  apply (pr1 (isdoublePullback_doublePullback dpb X hl hm hr eq1 eq2)).
Qed.

Lemma H1H2commute_from_twoPullbacks {C : category} {L M1 S M2 R : C}
  (f1 : C ⟦ L, M1 ⟧) (g1 : C ⟦ S, M1 ⟧) (f2 : C ⟦ S, M2 ⟧) (g2 : C ⟦ R, M2 ⟧)
  (pb1 : Pullback f1 g1) (pb2 : Pullback (PullbackPr2 pb1 · f2) g2) :
  PullbackPr1 pb2 · PullbackPr1 pb1 · f1 = PullbackPr1 pb2 · PullbackPr2 pb1 · g1 ×
  PullbackPr1 pb2 · PullbackPr2 pb1 · f2 = PullbackPr2 pb2 · g2.
Proof.
  split.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  exact (PullbackSqrCommutes pb1).
  refine (assoc' _ _ _ @ _).
  exact (PullbackSqrCommutes pb2).
Qed.

Lemma isdoublePullback_from_twoPullbacks {C : category} {L M1 S M2 R : C}
  (f1 : C ⟦ L, M1 ⟧) (g1 : C ⟦ S, M1 ⟧) (f2 : C ⟦ S, M2 ⟧) (g2 : C ⟦ R, M2 ⟧)
  (pb1 : Pullback f1 g1) (pb2 : Pullback (PullbackPr2 pb1 · f2) g2) :
  isdoublePullback f1 g1 f2 g2 (PullbackPr1 pb2 · PullbackPr1 pb1)
    (PullbackPr1 pb2 · PullbackPr2 pb1) (PullbackPr2 pb2)
    (pr1 (H1H2commute_from_twoPullbacks f1 g1 f2 g2 pb1 pb2))
    (pr2 (H1H2commute_from_twoPullbacks f1 g1 f2 g2 pb1 pb2)).
Proof.
  intros Q ql qm qr eq1 eq2.
  use tpair.
  use tpair.
  use PullbackArrow.
  use PullbackArrow; assumption.
  assumption.
  refine (assoc _ _ _ @ _ @ eq2).
  apply (maponpaths (postcompose _)).
  apply PullbackArrow_PullbackPr2.
  split3.
  refine (assoc _ _ _ @ _).
  refine (_ @ PullbackArrow_PullbackPr1 pb1 _ _ _ _).
  apply (maponpaths (postcompose _)).
  apply (PullbackArrow_PullbackPr1 pb2).
  refine (assoc _ _ _ @ _).
  refine (_ @ PullbackArrow_PullbackPr2 pb1 _ _ _ _).
  apply (maponpaths (postcompose _)).
  apply (PullbackArrow_PullbackPr1 pb2).
  apply PullbackArrow_PullbackPr2.
  simpl.
  intros (qp, (eql, (eqm, eqr))).
  apply subtypePath.
  intros h.
  use isofhleveltotal2.
  apply (pr2 C).
  intros x.
  use isofhleveltotal2.
  apply (pr2 C).
  intros x'.
  apply (pr2 C).
  use PullbackArrowUnique'.
  use PullbackArrowUnique'; refine (assoc' _ _ _ @ _); assumption.
  assumption.
Qed.

Definition doublePullback_from_twoPullbacks {C : category} {L M1 S M2 R : C}
  (f1 : C ⟦ L, M1 ⟧) (g1 : C ⟦ S, M1 ⟧) (f2 : C ⟦ S, M2 ⟧) (g2 : C ⟦ R, M2 ⟧)
  (pb1 : Pullback f1 g1) (pb2 : Pullback (PullbackPr2 pb1 · f2) g2) :
  doublePullback f1 g1 f2 g2.
Proof.
  use tpair.
  exists (PullbackObject pb2).
  exists (PullbackPr1 pb2 · PullbackPr1 pb1).
  exists (PullbackPr1 pb2 · PullbackPr2 pb1).
  exact (PullbackPr2 pb2).
  use tpair.
  exact (H1H2commute_from_twoPullbacks f1 g1 f2 g2 pb1 pb2).
  apply isdoublePullback_from_twoPullbacks.
Defined.

Arguments doublePullback_from_twoPullbacks : simpl never.

Definition doublePullbacks_from_Pullbacks {C : category} (pb : Pullbacks C) :
  doublePullbacks C.
Proof.
  intros L M1 S M2 R f1 g1 f2 g2.
  use doublePullback_from_twoPullbacks; apply pb.
Defined.

Definition hasdoublePullbacks_from_hasPullbacks {C : category} (pb : hasPullbacks C) :
  hasdoublePullbacks C.
Proof.
  intros L M1 S M2 R f1 g1 f2 g2.
  generalize (pb _ _ _ f1 g1); apply factor_through_squash.
  apply propproperty.
  intros pb1.
  generalize (pb _ _ _ (PullbackPr2 pb1 · f2) g2); apply hinhfun.
  intros pb2.
  use doublePullback_from_twoPullbacks; assumption.
Defined.

Lemma identity_is_doublePullbackArrow  {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) :
  identity (doublePullbackObject dP) =
    doublePullbackArrow dP (doublePullbackObject dP) (doublePullbackPrL dP)
      (doublePullbackPrM dP) (doublePullbackPrR dP) (doublePullbackSqrLCommutes dP)
      (doublePullbackSqrRCommutes dP).
Proof.
  apply doublePullbackArrowUnique'; apply id_left.
Qed.

Lemma doublePullback_twoPullbacks_Sqr {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (pb1 : Pullback f1 g1)
  (pb2 : Pullback (PullbackPr2 pb1 · f2) g2) :
  PullbackArrow pb1 (doublePullbackObject dP) (doublePullbackPrL dP)
    (doublePullbackPrM dP) (doublePullbackSqrLCommutes dP) · (PullbackPr2 pb1 · f2) =
    doublePullbackPrR dP · g2.
Proof.
  refine (assoc _ _ _ @ _ ).
  refine (_ @ doublePullbackSqrRCommutes dP).
  apply (maponpaths (postcompose f2)).
  apply (PullbackArrow_PullbackPr2 pb1).
Qed.

Definition doublePullbackObject_to_PullbackObject {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (pb1 : Pullback f1 g1)
  (pb2 : Pullback (PullbackPr2 pb1 · f2) g2) :
  C ⟦doublePullbackObject dP, PullbackObject pb2⟧. 
Proof.
  use PullbackArrow.
  use PullbackArrow.
  exact (doublePullbackPrL dP).
  exact (doublePullbackPrM dP).
  exact (doublePullbackSqrLCommutes dP).
  exact (doublePullbackPrR dP).
  apply doublePullback_twoPullbacks_Sqr; assumption.
Defined.

Definition PullbackObject_to_doublePullbackObject {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (pb1 : Pullback f1 g1)
  (pb2 : Pullback (PullbackPr2 pb1 · f2) g2) :
  C ⟦PullbackObject pb2, doublePullbackObject dP⟧.
Proof.
  use doublePullbackArrow.
  apply (compose (PullbackPr1 pb2)).
  apply PullbackPr1.
  apply (compose (PullbackPr1 pb2)).
  apply PullbackPr2.
  apply PullbackPr2.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  apply maponpaths.
  apply PullbackSqrCommutes.
  refine (_ @ PullbackSqrCommutes _).
  apply assoc'.
Defined.

Definition doublePullbackObject_to_Pullback_isiso {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (pb1 : Pullback f1 g1)
  (pb2 : Pullback (PullbackPr2 pb1 · f2) g2) :
  is_inverse_in_precat (doublePullbackObject_to_PullbackObject dP pb1 pb2)
    (PullbackObject_to_doublePullbackObject dP pb1 pb2).
Proof.
  split.
  refine (_ @ ! identity_is_doublePullbackArrow dP).
  apply doublePullbackArrowUnique'.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply doublePullbackArrow_PrL.
  refine (_ @ PullbackArrow_PullbackPr1 pb1 _ _ _ _).
  apply (maponpaths (postcompose _)).
  apply PullbackArrow_PullbackPr1.
  refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
  apply maponpaths.
  apply doublePullbackArrow_PrM.
  refine (_ @ PullbackArrow_PullbackPr2 pb1 _ _ _ _).
  apply (maponpaths (postcompose _)).
  apply PullbackArrow_PullbackPr1.
  refine (assoc' _ _ _ @ _ @ _).
  apply maponpaths.
  apply doublePullbackArrow_PrR.
  apply PullbackArrow_PullbackPr2.
  refine (PullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ _ @
            ! PullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  4 : {exact (id_left _).
  }
  4 : {exact (id_left _).
  }
  4 : {exact (PullbackPr1 pb2).
  }
  4 : {exact (PullbackPr2 pb2).
  }
  refine (assoc' _ _ _ @ _ @ _).
  apply maponpaths.
  apply (PullbackArrow_PullbackPr1 pb2).
  refine (PullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _ @ _ @
            ! PullbackArrowUnique' _ _ _ _ _ _ _ _ _ _ _).
  Unshelve.
  12 : {
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply (maponpaths (compose (PullbackPr1 pb2))).
    apply (PullbackSqrCommutes pb1).
  }
  12 : {
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply (maponpaths (compose (PullbackPr1 pb2))).
    apply (PullbackSqrCommutes pb1).
  }
  refine (assoc' _ _ _ @ _ @ _).
  apply maponpaths.
  apply PullbackArrow_PullbackPr1.
  apply doublePullbackArrow_PrL.
  refine (assoc' _ _ _ @ _ @ _).
  apply maponpaths.
  apply PullbackArrow_PullbackPr2.
  apply doublePullbackArrow_PrM.
  reflexivity.
  reflexivity.
  reflexivity.
  refine (assoc' _ _ _ @ _ @ _).
  apply maponpaths.
  apply PullbackArrow_PullbackPr2.
  apply doublePullbackArrow_PrR.
  reflexivity.
  apply (PullbackSqrCommutes pb2).
Qed.

Definition doublePullbackObject_is_PullbackObject {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (pb1 : Pullback f1 g1)
  (pb2 : Pullback (PullbackPr2 pb1 · f2) g2) :
  z_iso (doublePullbackObject dP) (PullbackObject pb2). 
Proof.
  exists (doublePullbackObject_to_PullbackObject dP pb1 pb2).
  exists (PullbackObject_to_doublePullbackObject dP pb1 pb2).
  apply doublePullbackObject_to_Pullback_isiso.
Defined.
(*
Definition twoPullbacks_from_doublePullback {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) :
  ∑ pb1 : Pullback f1 g1, Pullback (PullbackPr2 pb1 · f2) g2.
Proof.
  use tpair.
  exists (doublePullbackObject_to_PullbackObject dP pb1 pb2).
  exists (PullbackObject_to_doublePullbackObject dP pb1 pb2).
  apply doublePullbackObject_to_Pullback_isiso.
Defined. *)

Definition Pullbacks_from_doublePullbacks {C : category} (dpb : doublePullbacks C) :
  Pullbacks C.
Proof.
  intros M L R f g.
  set (dP := dpb L M R _ _ f g (identity _) (identity _)).
  use tpair.
  exists (doublePullbackObject dP).
  exists (doublePullbackPrL dP).
  exact (doublePullbackPrM dP).
  exists (doublePullbackSqrLCommutes dP).
  intros Q ql qr eq.
  use tpair.
  use tpair.
  use doublePullbackArrow; try assumption.
  reflexivity.
  split.
  apply (doublePullbackArrow_PrL dP).
  apply (doublePullbackArrow_PrM dP).
  intros (hk, (eq1, eq2)).
  apply subtypePath.
  intros h.
  use isofhleveltotal2.
  apply (pr2 C).
  intros x.
  apply (pr2 C).
  simpl.
  apply doublePullbackArrowUnique'; try assumption.
  revert eq1 eq2; simpl; intros eq1 eq2.
  refine (_ @ eq2).
  apply maponpaths.
  refine (! id_right _ @ _ @ id_right _).
  exact (! doublePullbackSqrRCommutes dP).

  (*
  exact (! eq).
  split.
  apply (doublePullbackArrow_PrL dP).
  apply (doublePullbackArrow_PrM dP).
  intros (hk, (eq1, eq2)).
  apply subtypePath.
  intros h.
  use isofhleveltotal2.
  apply (pr2 C).
  intros x.
  apply (pr2 C).
  simpl.
  apply doublePullbackArrowUnique'; try assumption.
  refine (_ @ eq1).
  apply maponpaths.
  unfold doublePullbackPrR, doublePullbackPrL.
  simpl.
  reflexivity.*)
Defined.

Definition make_doublePullback {C : category} {L M1 S M2 R : C} (f1 : C⟦L, M1⟧) (g1 : C⟦S, M1⟧)
  (f2 : C⟦S, M2⟧) (g2 : C⟦R, M2⟧) (P : C) (pl : C ⟦ P, L ⟧) (pm: C ⟦ P, S ⟧) (pr : C ⟦ P, R ⟧) (sql : pl · f1 = pm · g1) (sqr: pm · f2 = pr · g2) (isdp : isdoublePullback f1 g1 f2 g2 pl pm pr sql sqr): doublePullback f1 g1 f2 g2.
Proof.
  use tpair.
  exists P.
  exists pl.
  exists pm.
  exact pr.
  use tpair.
  exists sql.
  exact sqr.
  exact isdp.
Defined.

Definition make_isdoublePullback {C : category} {L M1 S M2 R : C} (f1 : C⟦L, M1⟧) (g1 : C⟦S, M1⟧)
  (f2 : C⟦S, M2⟧) (g2 : C⟦R, M2⟧) (P : C) (pl : C ⟦ P, L ⟧) (pm: C ⟦ P, S ⟧)
  (pr : C ⟦ P, R ⟧) (sql : pl · f1 = pm · g1) (sqr: pm · f2 = pr · g2) :
  (∏ (Q : C) (ql : C ⟦ Q, L ⟧) (qm : C ⟦ Q, S ⟧) (qr : C ⟦ Q, R ⟧),
  ql · f1 = qm · g1 → qm · f2 = qr · g2 → ∃! qp : C ⟦ Q, P ⟧, qp · pl = ql × qp · pm = qm × qp · pr = qr) →
  isdoublePullback f1 g1 f2 g2 pl pm pr sql sqr.
Proof.
  apply idfun.
Defined.

Definition identity_is_doublePullback_input {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) :
  ∑ hk : doublePullbackObject dP --> doublePullbackObject dP,
      (hk · doublePullbackPrL dP = doublePullbackPrL dP) ×
        (hk · doublePullbackPrM dP = doublePullbackPrM dP) × 
        (hk · doublePullbackPrR dP = doublePullbackPrR dP).
Proof.
  exists (identity _).
  split3; apply id_left.
Defined.

Lemma doublePullbackEndo_is_identity {C : category} {L M1 S M2 R : C} {f1 : C⟦L, M1⟧}
  {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧} (dP : doublePullback f1 g1 f2 g2)
  (k : doublePullbackObject dP --> doublePullbackObject dP)
  (kHL : k · doublePullbackPrL dP = doublePullbackPrL dP)
  (kHM : k · doublePullbackPrM dP = doublePullbackPrM dP)
  (kHR : k · doublePullbackPrR dP = doublePullbackPrR dP) :
  identity _ = k.
Proof.
  set (H1 := tpair ((fun hk : doublePullbackObject dP --> doublePullbackObject dP =>
                       (hk · _ = _) × (hk · _ = _) × (hk · _ = _)))
               k (kHL,,kHM,,kHR)).
  assert (H2 : identity_is_doublePullback_input dP = H1).
  - apply proofirrelevancecontr.
    apply (isdoublePullback_doublePullback dP).
    apply doublePullbackSqrLCommutes.
    apply doublePullbackSqrRCommutes.
  - apply (base_paths _ _ H2).
Qed.

Lemma doublePullbackEndos_are_equal {C : category} {L M1 S M2 R : C} {f1 : C⟦L, M1⟧}
  {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧} (dP : doublePullback f1 g1 f2 g2)
  (k k': doublePullbackObject dP --> doublePullbackObject dP)
  (kHL : k · doublePullbackPrL dP = doublePullbackPrL dP)
  (kHM : k · doublePullbackPrM dP = doublePullbackPrM dP)
  (kHR : k · doublePullbackPrR dP = doublePullbackPrR dP)
  (kHL' : k' · doublePullbackPrL dP = doublePullbackPrL dP)
  (kHM' : k' · doublePullbackPrM dP = doublePullbackPrM dP)
  (kHR' : k' · doublePullbackPrR dP = doublePullbackPrR dP) :  k = k'.
Proof.
  etrans.
  apply pathsinv0.
  apply doublePullbackEndo_is_identity; assumption.
  apply doublePullbackEndo_is_identity; assumption.
Qed.

Definition from_doublePullback_to_doublePullback {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP dP': doublePullback f1 g1 f2 g2) :
  doublePullbackObject dP --> doublePullbackObject dP'.
Proof.
  use doublePullbackArrow.
  apply doublePullbackPrL.
  apply doublePullbackPrM.
  apply doublePullbackPrR.
  apply doublePullbackSqrLCommutes.
  apply doublePullbackSqrRCommutes.
Defined.

Lemma are_inverses_from_doublePullback_to_doublePullback {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP dP': doublePullback f1 g1 f2 g2) :
is_inverse_in_precat (from_doublePullback_to_doublePullback dP dP')
  (from_doublePullback_to_doublePullback dP' dP).
Proof.
  split; apply pathsinv0;
  apply doublePullbackEndo_is_identity;
  rewrite <- assoc;
    unfold from_doublePullback_to_doublePullback;
    repeat rewrite (doublePullbackArrow_PrL dP);
    repeat rewrite (doublePullbackArrow_PrL dP');
    repeat rewrite (doublePullbackArrow_PrL dP);
    repeat rewrite (doublePullbackArrow_PrM dP);
    repeat rewrite (doublePullbackArrow_PrM dP');
    repeat rewrite (doublePullbackArrow_PrM dP);
    repeat rewrite (doublePullbackArrow_PrR dP);
    repeat rewrite (doublePullbackArrow_PrR dP');
    repeat rewrite (doublePullbackArrow_PrR dP);
    reflexivity.
Qed.

Lemma isziso_from_doublePullback_to_doublePullback {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
   (dP dP': doublePullback f1 g1 f2 g2) :
      is_z_isomorphism (from_doublePullback_to_doublePullback dP dP').
Proof.
  exists (from_doublePullback_to_doublePullback dP' dP).
  apply are_inverses_from_doublePullback_to_doublePullback.
Defined.


Definition z_iso_from_doublePullback_to_doublePullback {C : category} {L M1 S M2 R : C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP dP': doublePullback f1 g1 f2 g2) :
  z_iso (doublePullbackObject dP) (doublePullbackObject dP') :=
  _ ,, isziso_from_doublePullback_to_doublePullback dP dP'.

Definition doublePullback_CompetitorArrowL {C : category} {L M1 S M2 R: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (X : C) := C⟦X, L⟧.

Definition doublePullback_CompetitorArrowM {C : category} {L M1 S M2 R: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (X : C) := C⟦X, S⟧.

Definition doublePullback_CompetitorArrowR {C : category} {L M1 S M2 R: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (X : C) := C⟦X, R⟧.

Definition doublePullback_CompetitorSqrL {C : category} {L M1 S M2 R: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (X : C)
  (kL : C⟦X, L⟧) (kM : C⟦X, S⟧) : UU := kL · f1 = kM · g1.

Definition doublePullback_CompetitorSqrR {C : category} {L M1 S M2 R: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (X : C)
  (kM : C⟦X, S⟧) (kR : C⟦X, R⟧) : UU := kM · f2  = kR · g2.

Definition doublePullback_CompetitorArrows {C : category} {L M1 S M2 R: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (X : C) :=
  ∑ (ars : C⟦X, L⟧ × C⟦X, S⟧ × C⟦X, R⟧),
    ((pr1 ars) · f1 = (pr12 ars) · g1  ×  (pr12 ars) · f2  = (pr22 ars) · g2).

Definition doublePullback_CompetitorTriangleL {C : category} {L M1 S M2 R: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (X : C) (k : C⟦X, doublePullbackObject dP⟧)
  (kL : C⟦X, L⟧) : UU := k · doublePullbackPrL dP = kL.

Definition doublePullback_CompetitorTriangleM {C : category} {L M1 S M2 R: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (X : C) (k : C⟦X, doublePullbackObject dP⟧)
  (kM : C⟦X, S⟧) : UU := k · doublePullbackPrM dP = kM.

Definition doublePullback_CompetitorTriangleR {C : category} {L M1 S M2 R: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (X : C) (k : C⟦X, doublePullbackObject dP⟧)
  (kR : C⟦X, R⟧) : UU := k · doublePullbackPrR dP = kR.

Lemma arrows_into_doublePullback_equal {C : category} {L M1 S M2 R X: C}
  {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧} {g2 : C ⟦ R, M2 ⟧}
  (dP : doublePullback f1 g1 f2 g2) (k1 k2 : C⟦X, doublePullbackObject dP⟧)
  (kL : C⟦X, L⟧)  (kM : C⟦X, S⟧) (kR : C⟦X, R⟧)
  (sqrL : kL · f1 = kM · g1) (sqrR : kM · f2 = kR · g2)
  (trianL1 : k1 · doublePullbackPrL dP = kL) (trianM1 : k1 · doublePullbackPrM dP = kM)
  (trianR1 : k1 · doublePullbackPrR dP = kR) (trianL2 : k2 · doublePullbackPrL dP = kL)
  (trianM2 : k2 · doublePullbackPrM dP = kM) (trianR2 : k2 · doublePullbackPrR dP = kR) :
  k1 = k2.
Proof.
  refine (doublePullbackArrowUnique' dP X kL kM kR _ _ _ _ _ _  @
            ! doublePullbackArrowUnique' dP _ _ _ _ _ _ _ _ _ _);
    assumption.
Qed.

Definition match_doublePullback_to_object {C : category} {L M1 S M2 R : C} {f1 : C⟦L, M1⟧} {g1 : C ⟦ S, M1 ⟧} {f2 : C ⟦ S, M2 ⟧}
  {g2 : C ⟦ R, M2 ⟧} {dP : doublePullback f1 g1 f2 g2} (P : C)  (eq : P = doublePullbackObject dP) : doublePullback f1 g1 f2 g2.
Proof.
  assumption.
Defined.



(*
Lemma doublePullback_idMR {C : category} (pb : Pullbacks C) {L M1 S R : C}
  (f1 : C⟦L, M1⟧) (g1 : C ⟦ S, M1 ⟧) (f2 : C ⟦ S, R ⟧) (dP : doublePullback f1 g1 f2 (identity R)) : z_iso (doublePullbackObject dP) S.
Proof.
  refine (z_iso_comp
            (doublePullbackObject_is_PullbackObject dP (pb _ _ _ _ _) (pb _ _ _ _ _)) _).
  use tpair.
  apply (compose (PullbackPr1 _)).
  apply PullbackPr2.
  use tpair.
  use PullbackArrow.
  use PullbackArrow.
  refine (compose _ (doublePullbackPrL dP)).
  use doublePullbackArrow.
  
Qed.

Lemma doublePullback_idMR {C : category} (pb : Pullbacks C) {L M1 S R : C}
  (f1 : C⟦L, M1⟧) (g1 : C ⟦ S, M1 ⟧) (g2 : C ⟦ R, S ⟧) (dP : doublePullback f1 g1 (identity S) g2) : z_iso (doublePullbackObject dP) R.
Proof.
  refine (z_iso_comp
            (doublePullbackObject_is_PullbackObject dP (pb _ _ _ _ _) (pb _ _ _ _ _)) _).
  use tpair.
  apply PullbackPr2.
  use tpair.
  use PullbackArrow.
  2 : {exact (identity R).
  }
Qed.
  
Lemma doublePullback_idMR {C : category} {L M1 S R : C}
  (f1 : C⟦L, M1⟧) (g1 : C ⟦ S, M1 ⟧) (g2 : C ⟦ R, S ⟧) (dP : doublePullback f1 g1 (identity S) g2) : doublePullbackPrM dP = doublePullbackPrR dP · g2.
Proof.
  refine (! id_right _ @ _).
  apply (doublePullbackSqrRCommutes dP).
Qed.

Lemma doublePullback_idL {C : category} {M1 S M2 R : C}
  (g1 : C ⟦ S, M1 ⟧) (f2 : C ⟦ S, M2 ⟧) (g2 : C ⟦ R, M2 ⟧) (dP : doublePullback (identity M1) g1 f2 g2) : doublePullbackPrM dP = doublePullbackPrL dP.
Proof.
  

Qed.

*)


(*
Definition doublePullback {C : category} {L1 M1 LR M2 R2: C} (pb : Pullbacks C) (f1 : C⟦L1, M1⟧) (g1 : C⟦LR, M1⟧) (f2 : C⟦LR, M2⟧) (g2 : C⟦R2, M2⟧) : UU. 
Proof.
  set (P1:= pb M1 L1 LR f1 g1).
  set (P2:= pb M2 LR R2 f2 g2).
  exact (Pullback (C:=C) (a:=LR) (b:= pr11 P1) (c:= pr11 P2) (pr221 P1) (pr121 P2)).
Defined.

Lemma doublePullback_exists {C : category} {L1 M1 LR M2 R2: C} (pb : Pullbacks C) (f1 : C⟦L1, M1⟧) (g1 : C⟦LR, M1⟧) (f2 : C⟦LR, M2⟧) (g2 : C⟦R2, M2⟧) :
  doublePullback pb f1 g1 f2 g2. 
Proof.
  exact (pb LR (pr11 (pb M1 L1 LR f1 g1)) (pr11 (pb M2 LR R2 f2 g2)) 
           (pr221 (pb M1 L1 LR f1 g1)) (pr121 (pb M2 LR R2 f2 g2))).
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

*)


