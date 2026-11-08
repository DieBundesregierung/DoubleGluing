Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.CategoryEquality.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import preliminaries.
Require Import double_pullbacks.
Require Import natural_contraction.
Require Import double_gluing.double_gluing.

Require Import double_gluing.monoidal.symmetry.
Require Import double_gluing.additive_structure.coproducts.
Require Import double_gluing.additive_structure.products.

Import BifunctorNotations.
Import MonoidalNotations.

Section homfunctors.

  Context (FC : sym_monoidal_cat).

  Definition fmonoidal_data_cov_homSet_functor :
    fmonoidal_data FC HSet_SMC (cov_homSet_functor (monoidal_unit FC)).
  Proof using Type.
    split.
    intros B C (f, g).
    exact (luinv^{FC}_{I_{FC}} · (f ⊗^{FC} g)).
    intros u.
    apply identity.
  Defined.
  
  Lemma fmonoidal_laws_cov_homSet_functor :
    fmonoidal_laxlaws fmonoidal_data_cov_homSet_functor.
  Proof using Type.
    split5.
    intros X Y1 Y2 f.
    apply funextfun.
    intros (gx, gy).
    refine (_ @ assoc (C:=FC) _ _ _).
    refine (_ @ ! id_left _).
    refine (_ @ assoc _ _ _).
    apply (maponpaths (compose (C:=FC) _)).
    refine (_ @ assoc _ _ _).
    apply (maponpaths (compose _)).
    refine (_ @ bifunctor_leftcomp FC _ _ _ _ _ _).
    apply maponpaths.
    apply cancel_postcomposition.
    apply (id_left (C:=FC)).
    intros X1 X2 Y f.
    apply funextfun.
    intros (gx, gy).
    refine (_ @ assoc (C:=FC) _ _ _).
    refine (_ @ ! id_left _).
    refine (_ @ assoc _ _ _).
    apply (maponpaths (compose (C:=FC) _)).
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths, (bifunctor_equalwhiskers FC).
    }
    apply cancel_postcomposition.
    refine (maponpaths _ _ @ _).
    2 : {
      apply (bifunctor_rightcomp FC).
    }
    apply cancel_postcomposition, (id_left (C:=FC)).
    intros X Y Z.
    apply funextfun.
    intros ((gx, gy), gz).
    refine (assoc'(C:=FC)  _ _ _ @ _).
    refine (id_left (C:=FC) _ @ _).
    refine (assoc' _ _ _ @ _).
    apply (maponpaths (compose (C:=FC) _)).
    refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_associatornatleft FC).
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    apply (bifunctor_rightcomp FC).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply (bifunctor_rightcomp FC).
    apply maponpaths.
    apply pathsinv0, (monoidal_associatornatleftright FC).
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply pathsinv0, (monoidal_associatornatright FC).
    refine (_ @ assoc' _ _ _ @ _).
    2 : {
      apply (maponpaths (compose (C:=FC) _)).
      apply pathsinv0, (bifunctor_leftcomp FC).
    }
    refine (_ @ assoc _ _ _ @ _).
    2 : {
      apply cancel_postcomposition.
      apply pathsinv0, (bifunctor_equalwhiskers FC).
    }
    apply map_on_two_paths.
    refine (_ @ id_right _).
    refine (maponpaths (λ f, f · _) _ @ _).
    2 : {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply (monoidal_associatorisolaw FC).
    }
    apply pathsinv0.
    refine (monoidal_triangle_identity_inv FC _ _ @ _).
    apply maponpaths.
    apply pathsinv0.
    apply unitorsinv_coincide_on_unit.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0, (bifunctor_leftcomp FC).
    intros X.
    apply funextfun.
    intros gx.
    refine (_ @ assoc' (C:=FC) _ _ _ @ _).
    apply cancel_postcomposition.
    refine (id_left _ @ _ @ monoidal_leftunitorinvnat FC _ _ _).
    apply (maponpaths (compose (C:=FC) _)).
    apply (when_bifunctor_becomes_leftwhiskering FC).
    refine (_ @ id_right _).
    apply (maponpaths (compose (C:=FC) _)).
    apply (monoidal_leftunitorisolaw FC).
    intros X.
    apply funextfun.
    intros gx.
    refine (assoc' (C:=FC) _ _ _ @ _ @ assoc _ _ _ @ _).
    refine (id_left _ @ _).
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (_ @ monoidal_rightunitornat FC _ _ _).
    apply cancel_postcomposition.
    apply (when_bifunctor_becomes_rightwhiskering FC).
    refine (_ @ id_left _ ).
    apply cancel_postcomposition.
    rewrite unitorsinv_coincide_on_unit.
    apply (monoidal_rightunitorisolaw FC).
  Qed.
  
  Definition fmonoidal_cov_homSet_functor :
    fmonoidal_lax FC HSet_SMC (cov_homSet_functor (monoidal_unit FC)).
  Proof.
    exists fmonoidal_data_cov_homSet_functor.
    apply fmonoidal_laws_cov_homSet_functor.
  Defined.  

  Definition monoidal_cov_homSet_functor : lax_monoidal_functor FC HSet_SMC.
  Proof.
    use tpair.
    2 : apply fmonoidal_cov_homSet_functor.
  Defined.

  Lemma is_symmetric_monoidal_cov_homSet :
    is_symmetric_monoidal_functor FC HSet_SMC monoidal_cov_homSet_functor.
  Proof using Type.
    intros X Y.
    apply funextfun.
    intros (gx, gy).
    refine (_ @ assoc (C:=FC) _ _ _).
    refine (_ @ ! id_left _).
    refine (_ @ assoc (C:=FC) _ _ _).
    apply (maponpaths (compose _)).
    refine (! id_left _ @ _).
    refine (_ @ ! tensor_sym_mon_braiding FC _ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply sym_mon_braiding_id.
  Qed.
  
  Definition sym_mon_cov_homSet_functor : symmetric_lax_monoidal_functor FC HSet_SMC.
  Proof.
    use tpair.
    apply monoidal_cov_homSet_functor.
    apply is_symmetric_monoidal_cov_homSet.
  Defined.

  Definition fmonoidal_data_contra_homSet_functor :
    fmonoidal_data (monoidal_opp FC) HSet_SMC (contra_homSet_functor (monoidal_unit FC)).
  Proof using Type.
    split.
    intros B C (f, g).
    exact ((f ⊗^{FC} g) · lu^{FC}_{I_{FC}}).
    intros u.
    apply identity.
  Defined.
  
  Lemma fmonoidal_laws_contra_homSet_functor :
    fmonoidal_laxlaws fmonoidal_data_contra_homSet_functor.
  Proof using Type.
    split5.
    intros X Y1 Y2 f21.
    apply funextfun.
    simpl.
    intros (gx, gy).
    refine (_ @ ! id_right _).
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (_ @ assoc' _ _ _ @ _).
    2 : {
      apply maponpaths, pathsinv0, (bifunctor_equalwhiskers FC).
    }
    refine (bifunctor_equalwhiskers FC _ _ _ _ _ _ @ _).
    apply cancel_postcomposition.
    refine (_ @ bifunctor_leftcomp FC _ _ _ _ _ _).
    apply maponpaths.
    apply id_right.
    intros X1 X2 Y f21.
    apply funextfun.
    intros (gx, gy).
    refine (_ @ ! id_right _).
    refine (_ @ assoc' (C:=FC) _ _ _).
    apply cancel_postcomposition.
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (_ @ bifunctor_rightcomp FC _ _ _ _ _ _).
    apply maponpaths.
    apply id_right.
    intros X Y Z.
    apply funextfun.
    intros ((gx, gy), gz).
    refine (id_right (C:=FC) _ @ _).
    refine (assoc (C:=FC)  _ _ _ @ _).
    apply cancel_postcomposition.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths.
    apply (bifunctor_rightcomp FC).
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths.
    apply (bifunctor_rightcomp FC).
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (monoidal_associatorinvnatright FC).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply (monoidal_associatorinvnatleftright FC).
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply maponpaths.
    apply (bifunctor_equalwhiskers FC).
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (monoidal_associatorinvnatleft FC).
    refine (_ @ assoc' _ _ _ @ _).
    2 : {
      apply (maponpaths (compose (C:=FC) _)).
      apply pathsinv0, (bifunctor_leftcomp FC).
    }
    apply (map_on_two_paths (compose (C:=FC))).
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0, (bifunctor_leftcomp FC).
    refine (maponpaths (compose _) _ @ _).
    apply pathsinv0, right_whisker_with_lunitor.
    refine (assoc _ _ _ @ _ @ id_left _).
    apply map_on_two_paths.
    apply (monoidal_associatorisolaw FC).
    refine (! id_right _ @ _ @ id_left _).
    refine (maponpaths _ _ @ _).
    2 : {
      refine (assoc _ _ _ @ _).
      apply cancel_postcomposition.
      apply (monoidal_leftunitorisolaw FC).
    }
    refine (_ @ ! monoidal_leftunitorinvnat FC _ _ _).
    apply pathsinv0, (monoidal_leftunitorisolaw FC).
    intros X.
    apply funextfun.
    intros gx.
    refine (id_right (C:=FC) _ @ _).
    refine (assoc (C:=FC) _ _ _ @ _ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    refine (assoc _ _ _ @ _ @ _).
    apply cancel_postcomposition.
    refine (_ @ id_right _).
    apply maponpaths.
    apply (bifunctor_rightid FC).
    apply (monoidal_leftunitorinvnat FC).
    refine (_ @ id_right (C:=FC) _).
    apply maponpaths.
    apply (monoidal_leftunitorisolaw FC).
    intros X.
    apply funextfun.
    intros gx.
    refine (assoc'  _ _ _ @ _ @ assoc _ _ _ @ _).
    apply maponpaths.
    apply id_right.
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    refine (assoc _ _ _ @ _  @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    apply (monoidal_rightunitorinvnat FC).
    apply maponpaths.
    refine (_ @ id_right _).
    apply maponpaths.
    apply (bifunctor_leftid FC).
    refine (_ @ id_right _).
    apply maponpaths.
    rewrite unitors_coincide_on_unit.
    apply (monoidal_rightunitorisolaw FC).
  Qed.
  
  Definition fmonoidal_contra_homSet_functor :
    fmonoidal_lax (monoidal_opp FC) HSet_SMC (contra_homSet_functor (monoidal_unit FC)).
  Proof.
    exists fmonoidal_data_contra_homSet_functor.
    apply fmonoidal_laws_contra_homSet_functor.
  Defined.  

  Definition monoidal_contra_homSet_functor :
    lax_monoidal_functor (_,, monoidal_opp FC) HSet_SMC.
  Proof.
    use tpair.
    2 : apply fmonoidal_contra_homSet_functor.
  Defined.
  
  Lemma is_symmetric_monoidal_contra_homSet :
    is_symmetric_monoidal_functor (symmetric_opp FC) HSet_SMC monoidal_contra_homSet_functor.
  Proof using Type.
    intros X Y.
    apply funextfun.
    intros (gx, gy).
    refine (_ @ ! id_right (C:=FC) _).
    refine (_ @ assoc' (C:=FC) _ _ _).
    apply (cancel_postcomposition (C:=FC)).
    refine (_ @ tensor_sym_mon_braiding FC _ _).
    refine (! id_right (C:=FC) _ @ _).
    apply maponpaths.
    apply pathsinv0.
    apply sym_mon_braiding_id.
  Qed.
  
  Definition sym_mon_contra_homSet_functor :
    symmetric_lax_monoidal_functor (sym_monoidal_opp_cat FC) HSet_SMC.
  Proof.
    use tpair.
    apply monoidal_contra_homSet_functor.
    apply is_symmetric_monoidal_contra_homSet.
  Defined.

  Definition alt_contra_functor_data {C D : category} (F : functor_data (C ^opp) D) : functor_data C (D ^opp).
  Proof.
    use tpair.
    apply F.
    intros a b.
    apply F.
  Defined.

  Lemma alt_contra_is_functor {C D : category} (F : functor (C ^opp) D) : is_functor (alt_contra_functor_data F).
  Proof using Type.
    split.
    apply F.
    intros x y z f g.
    apply F.
  Qed.

  Definition alt_contra_functor {C D : category} (F : functor (C ^opp) D) : functor C (D ^opp).
  Proof.
    exists (alt_contra_functor_data F).
    apply alt_contra_is_functor.
  Defined.
  
  Definition natural_contraction_data_hom_functors (X Y : FC) :
    HSet_SMC ⟦ sym_mon_cov_homSet_functor X ⊗_{ HSet_SMC} alt_contra_functor (contra_homSet_functor I_{ FC}) (X ⊗_{ FC} Y),
        alt_contra_functor (contra_homSet_functor I_{ FC}) Y ⟧.
    (* FC ⟦ I_{ FC}, X ⟧ × FC ⟦ X ⊗_{ FC} Y, I_{ FC} ⟧ → FC ⟦ Y, I_{ FC} ⟧. *)
  Proof.
    intros (f, g).
    refine (compose _ g).
    refine (compose (luinv^{FC}_{Y}) _).
    apply (f ⊗^{FC}_{r} Y).
  Defined.
  
  Lemma is_natural_contraction_hom_functors : is_natural_contraction (natural_contraction_data_hom_functors).
  Proof using Type.
    split4.
    intros X Y Z f.
    apply funextfun.
    intros (gx, gxy).
    refine (assoc (C:=FC) _ _ _ @ _ ).
    apply cancel_postcomposition.
    refine (assoc (C:=FC) _ _ _ @ _ @ assoc' (C:=FC) _ _ _).
    apply cancel_postcomposition.
    refine (assoc' (C:=FC) _ _ _ @ _ @ assoc (C:=FC) _ _ _ @ _).
    apply maponpaths.
    apply (bifunctor_equalwhiskers FC).
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply (monoidal_leftunitorinvnat FC).
    intros X Y Z f.
    apply funextfun.
    intros (gy, gzx).
    refine (assoc (C:=FC) _ _ _ @ _ ).
    refine (id_right _ @ _).
    refine (assoc (C:=FC) _ _ _ @ _ ).
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (! bifunctor_rightcomp FC _ _ _ _ _ _ @ _).
    apply maponpaths.
    apply cancel_postcomposition.
    apply pathsinv0, (id_left (C:=FC)).
    intros X.
    apply funextfun.
    intros (t, g).
    refine (! id_left _ @ _  @ assoc' _ _ _).
    refine (_ @ ! id_right _).
    refine (_ @ assoc' _ _ _).
    apply (cancel_postcomposition (C:=FC)).
    refine (_ @ maponpaths (λ f, f · _) _).
    apply pathsinv0, (monoidal_leftunitorisolaw FC).
    refine (! id_right _ @ _).
    apply maponpaths.
    apply pathsinv0, (bifunctor_rightid FC).
    intros X Y Z.
    simpl.
    apply funextfun.
    intros ((f, g), h).
    refine (assoc' (C:=FC) _ _ _ @ _ @ assoc (C:=FC) _ _ _).
    apply maponpaths.
    refine (assoc (C:=FC) _ _ _ @ _).
    refine (_ @ assoc' (C:=FC) _ _ _).
    refine (id_right (C:=FC) _ @ _).
    refine (assoc (C:=FC) _ _ _ @ _).
    apply cancel_postcomposition.
    unfold postcompose.
    refine (_ @ assoc _ _ _ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply (monoidal_leftunitorinvnat FC).
    }
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply (bifunctor_rightcomp FC).
    apply maponpaths.
    refine (_ @ assoc' _ _ _ @ _ @ assoc _ _ _ @ _).
    apply cancel_postcomposition.
    apply (bifunctor_rightcomp FC).
    apply maponpaths.
    apply pathsinv0, (monoidal_associatornatleftright FC).
    refine (_ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply pathsinv0, (monoidal_associatornatright FC).
    apply map_on_two_paths.
    refine (! id_right _ @ _ ).
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0.
    refine (_ @ bifunctor_leftid FC _ _).
    refine (! bifunctor_leftcomp FC _ _ _ _ _ _ @ _).
    apply maponpaths.
    apply (pr1 (monoidal_leftunitorisolaw FC _)).
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) _).
    apply monoidal_triangleidentity.
    refine (assoc _ _ _ @ _ @ id_left _).
    apply map_on_two_paths.
    refine (! bifunctor_rightcomp FC _ _ _ _ _ _ @ _).
    refine (_ @ bifunctor_rightid FC _ _).
    apply maponpaths.
    rewrite <- unitors_coincide_on_unit.
    apply monoidal_leftunitorisolaw.
    refine (! id_right _ @ _ @ id_left _).
    refine (_ @ maponpaths (λ f, f · _) _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    apply pathsinv0.
    apply monoidal_leftunitorisolaw.
    refine (monoidal_leftunitornat FC _ _ _ @ _ ).
    apply monoidal_leftunitorisolaw.
    apply (bifunctor_equalwhiskers FC).
  Qed.
  
  Definition natural_contraction_hom_functors :
    natural_contraction HSet_SMC sym_mon_cov_homSet_functor (alt_contra_functor (contra_homSet_functor I_{ FC})).
  Proof.
    use tpair.
    apply natural_contraction_data_hom_functors.
    apply is_natural_contraction_hom_functors.
  Defined.

End homfunctors.

Section preserving_coproducts.
  
  (* Results about functors that preserve Coproducts *)
    
  Lemma functor_preserves_In1 {C D : category} (copC : BinCoproducts C) (copD : BinCoproducts D) (F : functor C D) (X Y : C) :
    # F (BinCoproductIn1 (copC X Y)) =  BinCoproductIn1 (copD (F X) (F Y)) · bincoprod_antidistributor copC copD F X Y.
  Proof.
    apply pathsinv0.
    apply BinCoproductIn1Commutes.
  Qed.
    
  Lemma functor_preserves_In2 {C D : category} (copC : BinCoproducts C) (copD : BinCoproducts D) (F : functor C D) (X Y : C) :
    # F (BinCoproductIn2 (copC X Y)) =  BinCoproductIn2 (copD (F X) (F Y)) · bincoprod_antidistributor copC copD F X Y.
  Proof.
    apply pathsinv0.
    apply BinCoproductIn2Commutes.
  Qed.
    
  Lemma functor_preserves_In1' {C D : category} (copC : BinCoproducts C) (copD : BinCoproducts D) (F : functor C D)
    (df : bincoprod_distributor copC copD F) (X Y : C) :
    # F (BinCoproductIn1 (copC X Y)) · (df X Y) =  BinCoproductIn1 (copD (F X) (F Y)).
  Proof.
    refine (_ @ id_right _).
    refine (maponpaths (λ f, f · _) _ @ _).
    apply pathsinv0.
    apply BinCoproductIn1Commutes.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply df.
  Qed.
    
  Lemma functor_preserves_In2' {C D : category} (copC : BinCoproducts C) (copD : BinCoproducts D) (F : functor C D)
    (df : bincoprod_distributor copC copD F) (X Y : C) :
    # F (BinCoproductIn2 (copC X Y)) · (df X Y) =  BinCoproductIn2 (copD (F X) (F Y)).
  Proof.
    refine (_ @ id_right _).
    refine (maponpaths (λ f, f · _) _ @ _).
    apply pathsinv0.
    apply BinCoproductIn2Commutes.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply df.
  Qed.

  Lemma bincoprod_distributor_unique {C D : category} {copC : BinCoproducts C} {copD : BinCoproducts D} {F : functor C D}
    (df df' : bincoprod_distributor copC copD F) : df = df'.
  Proof.
    apply subtypePath.
    unfold bincoprod_distributor_iso_law.
    intros x.
    apply impred; intros c.
    apply impred; intros c'.
    apply isaprop_is_inverse_in_precat.
    apply funextsec.
    intros X.
    apply funextsec.
    intros Y.
    apply (inverse_unique_precat _ _ (bincoprod_antidistributor copC copD F X Y)).
    split; apply df.
    split; apply df'.
  Qed.
  
  Definition bincoprod_distributor_composed_data {C D E : category} {copC : BinCoproducts C} {copD : BinCoproducts D}
    {copE : BinCoproducts E} {F : functor C D} {G : functor D E} (df : bincoprod_distributor copC copD F)
    (dg : bincoprod_distributor copD copE G) :
    bincoprod_distributor_data copC copE (functor_composite F G).
  Proof.
    intros X Y.
    refine (compose (# G _) _).
    apply df.
    apply dg.
  Defined.
  
  Lemma bincoprod_distributor_composed_isolaw {C D E : category} {copC : BinCoproducts C} {copD : BinCoproducts D}
    {copE : BinCoproducts E} {F : functor C D} {G : functor D E} (df : bincoprod_distributor copC copD F)
    (dg : bincoprod_distributor copD copE G) :
    bincoprod_distributor_iso_law copC copE (F ∙ G) (bincoprod_distributor_composed_data df dg).
  Proof.
    intros X Y.
    split.
    refine (assoc' _ _ _ @ _).
    refine (_ @ ! functor_comp G _ _ @ _ @ functor_id G _).
    apply maponpaths.
    2 : {
      apply maponpaths.
      apply df.
    }
    refine (_ @ id_left _).
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths.
    2 : {
      apply cancel_postcomposition.
      apply dg.
    }
    apply BinCoproductArrowsEq.
    refine (_ @ _).
    apply BinCoproductIn1Commutes.
    refine (_ @ assoc' _ _ _).
    refine (_ @ _).
    2 : {
      apply cancel_postcomposition, pathsinv0.
      apply BinCoproductIn1Commutes.
    }
    refine (_ @ functor_comp G _ _).
    apply (maponpaths (# G)).
    apply pathsinv0, BinCoproductIn1Commutes.
    refine (_ @ _).
    apply BinCoproductIn2Commutes.
    refine (_ @ assoc' _ _ _).
    refine (_ @ _).
    2 : {
      apply cancel_postcomposition, pathsinv0.
      apply BinCoproductIn2Commutes.
    }
    refine (_ @ functor_comp G _ _).
    apply (maponpaths (# G)).
    apply pathsinv0, BinCoproductIn2Commutes.
    apply pathsinv0, BinCoproduct_endo_is_identity;
      refine (assoc _ _ _ @ _);
      refine (_ @ _).
    apply cancel_postcomposition.
    apply BinCoproductIn1Commutes.
    refine (assoc _ _ _ @ _ @ id_right _).
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    2 : apply maponpaths, dg.
    refine (_ @ _).
    2 : apply pathsinv0, BinCoproductIn1Commutes.
    refine (! functor_comp G _ _ @ _).
    apply (maponpaths (# G)).
    refine (_ @ id_right _).
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    2 : apply maponpaths, df.
    apply pathsinv0, BinCoproductIn1Commutes.
    apply cancel_postcomposition.
    apply BinCoproductIn2Commutes.
    refine (assoc _ _ _ @ _ @ id_right _).
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    2 : apply maponpaths, dg.
    refine (_ @ _).
    2 : apply pathsinv0, BinCoproductIn2Commutes.
    refine (! functor_comp G _ _ @ _).
    apply (maponpaths (# G)).
    refine (_ @ id_right _).
    refine (_ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    2 : apply maponpaths, df.
    apply pathsinv0, BinCoproductIn2Commutes.
  Qed.
  
  Definition bincoprod_distributor_composed {C D E : category} {copC : BinCoproducts C} {copD : BinCoproducts D}
    {copE : BinCoproducts E} {F : functor C D} {G : functor D E} (df : bincoprod_distributor copC copD F)
    (dg : bincoprod_distributor copD copE G) :
    bincoprod_distributor copC copE (functor_composite F G).
  Proof.
    use tpair.
    apply (bincoprod_distributor_composed_data df dg).
    apply bincoprod_distributor_composed_isolaw.
  Defined.
  
  Definition identity_bincoprod_distributor_data {C : category} (copC : BinCoproducts C)  :
    bincoprod_distributor_data copC copC (functor_identity C).
  Proof.
    intros X Y.
    apply identity.
  Defined.
  
  Lemma identity_bincoprod_distributor_isolaw {C : category} (copC : BinCoproducts C) :
    bincoprod_distributor_iso_law _ _ (functor_identity C) (identity_bincoprod_distributor_data copC).
  Proof.
    intros X Y.
    split.
    refine (id_left _ @ _).
    apply pathsinv0, BinCoproduct_endo_is_identity.
    apply BinCoproductIn1Commutes.
    apply BinCoproductIn2Commutes.
    refine (id_right _ @ _).
    apply pathsinv0, BinCoproduct_endo_is_identity.
    apply BinCoproductIn1Commutes.
    apply BinCoproductIn2Commutes.
  Qed.
  
  Definition identity_bincoprod_distributor {C : category} (copC : BinCoproducts C) :
    bincoprod_distributor copC copC (functor_identity C).
  Proof.
    use tpair.
    apply identity_bincoprod_distributor_data.
    apply identity_bincoprod_distributor_isolaw.
  Defined.
  
  Lemma nattrans_bincoprod_antidistributors {C D : category} (copC : BinCoproducts C) (copD : BinCoproducts D) {F G : functor C D}
    (ϕ : nat_trans F G) :
    ∏ X Y : C, BinCoproductOfArrows _ (copD (F X) (F Y)) _ (ϕ X) (ϕ Y) · bincoprod_antidistributor copC copD G X Y =
                 bincoprod_antidistributor copC copD F X Y · ϕ (copC X Y).
  Proof.
    intros X Y.
    apply BinCoproductArrowsEq.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    apply BinCoproductIn1Commutes.
    etrans.
    apply maponpaths.
    apply BinCoproductIn1Commutes.
    apply pathsinv0.
    refine (assoc _ _ _ @ _).
    etrans.
    apply cancel_postcomposition.
    apply BinCoproductIn1Commutes.
    apply ϕ.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    apply BinCoproductIn2Commutes.
    etrans.
    apply maponpaths.
    apply BinCoproductIn2Commutes.
    apply pathsinv0.
    refine (assoc _ _ _ @ _).
    etrans.
    apply cancel_postcomposition.
    apply BinCoproductIn2Commutes.
    apply ϕ.
  Qed.

  Lemma nattrans_bincoprod_distributors {C D : category} {copC : BinCoproducts C} {copD : BinCoproducts D} {F G : functor C D}
    (df : bincoprod_distributor copC copD F) (dg : bincoprod_distributor copC copD G) (ϕ : nat_trans F G) : 
    ∏ X Y : C, df X Y · BinCoproductOfArrows _ (copD (F X) (F Y)) _ (ϕ X) (ϕ Y) = ϕ (copC X Y) · dg X Y.
  Proof.
    intros X Y.
    refine (_ @ id_left _).
    refine (_ @ assoc _ _ _ @ _).
    2 : {
      apply cancel_postcomposition.
      apply df.
    }
    apply maponpaths.
    refine (! id_right _ @ _ @ assoc' _ _ _).
    refine (_ @ assoc _ _ _ @ _).
    2 : {
      apply cancel_postcomposition.
      apply nattrans_bincoprod_antidistributors.
    }
    apply maponpaths.
    apply pathsinv0.
    apply dg.
  Qed.
  
End preserving_coproducts.



Definition dpbs_set : doublePullbacks hset_category.
Proof.
  apply doublePullbacks_from_Pullbacks.
  apply PullbacksHSET.
Defined.


Section indecomposability.

  Context (FC : sym_monoidal_cat) (cop_fc : BinCoproducts FC).
  
  Definition dg_cat : sym_monoidal_cat.
  Proof.
    use double_glued_total_sym_monoidal_cat.
    apply FC.
    exact HSet_SMC.
    apply doublePullbacks_from_Pullbacks.
    apply PullbacksHSET.
    apply sym_mon_cov_homSet_functor.
    apply alt_contra_functor.
    apply contra_homSet_functor.
    apply (monoidal_unit FC).
    apply natural_contraction_hom_functors.
  Defined.
  
  Definition forgetful_functor_dg_cat : functor dg_cat FC.
  Proof.
    apply double_glued_forgetful_functor.
  Defined.

  Context (functor_FC_DG : symmetric_strong_monoidal_functor FC dg_cat)
    (distributor_functor_FC_DG : bincoprod_distributor cop_fc
                                            (double_glued_BinCoproducts cop_fc BinCoproductsHSET dpbs_set _ _) functor_FC_DG)
    (functor_comp_is_id : nat_z_iso (functor_composite functor_FC_DG forgetful_functor_dg_cat) (functor_identity FC)).

  Definition forgetful_functor_dg_cat_bincoprod_distributor :
    bincoprod_distributor (double_glued_BinCoproducts cop_fc BinCoproductsHSET dpbs_set _ _)
      cop_fc forgetful_functor_dg_cat.
  Proof.
    use tpair.
    intros X Y.
    apply identity.
    split; [refine (id_left _ @ _) | 
             refine (id_right _ @ _)];
      apply pathsinv0;
      apply BinCoproductArrowUnique;
      apply id_right.
  Defined.
  
  Definition functor_comp_bincoprod_distributor_data :
    bincoprod_distributor_data cop_fc cop_fc (functor_FC_DG ∙ forgetful_functor_dg_cat).
  Proof.
    intros X Y.
    refine (compose _ _).
    apply functor_comp_is_id.
    apply BinCoproductOfArrows;
      apply functor_comp_is_id.
  Defined.
  
  Lemma functor_comp_bincoprod_distributor_isolaw :
    bincoprod_distributor_iso_law _ _ (functor_FC_DG ∙ forgetful_functor_dg_cat) functor_comp_bincoprod_distributor_data.
  Proof.
    intros X Y.
    split.
    refine (assoc' _ _ _ @ _).
    apply pathsinv0.
    refine (_ @ _).
    apply pathsinv0, (pr2 functor_comp_is_id).
    apply maponpaths.
    apply BinCoproductArrowsEq.
    refine (_ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply pathsinv0, BinCoproductIn1Commutes.
    }
    refine (_ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths.
      apply pathsinv0, BinCoproductIn1Commutes.
    }
    apply (pr21 (nat_z_iso_inv functor_comp_is_id)).
    refine (_ @ _ @ assoc' _ _ _).
    2 : {
      apply cancel_postcomposition.
      apply pathsinv0, BinCoproductIn2Commutes.
    }
    refine (_ @ _ @ assoc _ _ _).
    2 : {
      apply maponpaths.
      apply pathsinv0, BinCoproductIn2Commutes.
    }
    apply (pr21 (nat_z_iso_inv functor_comp_is_id)).
    apply BinCoproductArrowsEq.
    refine (assoc _ _ _ @ _ @ _ @ ! id_right _).
    apply cancel_postcomposition.
    apply BinCoproductIn1Commutes.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    apply (pr1 functor_comp_is_id).
    refine (_ @ assoc _ _ _ @ _  @ id_left _).
    apply maponpaths.
    apply BinCoproductIn1Commutes.
    apply cancel_postcomposition.
    apply (pr2 functor_comp_is_id).
    refine (assoc _ _ _ @ _ @ _ @ ! id_right _).
    apply cancel_postcomposition.
    apply BinCoproductIn2Commutes.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    apply (pr1 functor_comp_is_id).
    refine (_ @ assoc _ _ _ @ _  @ id_left _).
    apply maponpaths.
    apply BinCoproductIn2Commutes.
    apply cancel_postcomposition.
    apply (pr2 functor_comp_is_id).
  Qed.
  
  Definition functor_comp_bincoprod_distributor :
    bincoprod_distributor cop_fc cop_fc (functor_FC_DG ∙ forgetful_functor_dg_cat).
  Proof.
    use tpair.
    apply functor_comp_bincoprod_distributor_data.
    apply functor_comp_bincoprod_distributor_isolaw.
  Defined.

  Lemma functor_comp_bincoprod_distributor_eq (X Y : FC) :
    pr1 (pr1 distributor_functor_FC_DG X Y) = functor_comp_bincoprod_distributor X Y.
  Proof.
    intermediate_path (bincoprod_distributor_composed distributor_functor_FC_DG forgetful_functor_dg_cat_bincoprod_distributor X Y).
    apply pathsinv0, id_right.
    apply (maponpaths (λ d, pr1 d X Y)).
    apply bincoprod_distributor_unique.
  Qed.

  (* Can be replaced by assuming that functor_comp_is_id is a monoidal transformation, but that would be a stronger assumption *)
  Definition preserves_tensorunit_FC_DG_is_id_type : UU.
  Proof.
    refine (pr1 (fmonoidal_preservesunit functor_FC_DG) = _).
    apply functor_comp_is_id.
  Defined.
  Context (preserves_tensorunit_FC_DG_is_id : preserves_tensorunit_FC_DG_is_id_type).  (*last assumption*)

  
  Definition bincoprod_distributor_natiso_commute_type {C : category} (copc : BinCoproducts C) {F: functor C C}
    (n : nat_z_iso F (functor_identity C)) (df : bincoprod_distributor copc copc F) (X Y : C) : UU.
  Proof.
    apply (paths (A:=F (copc X Y) --> copc X Y)).
    apply n.
    apply (compose (df X Y)).
    apply BinCoproductOfArrows; apply n.
  Defined.

  Lemma bincoprod_distributor_natiso_commute {C : category} (copc : BinCoproducts C) {F: functor C C}
    (n : nat_z_iso F (functor_identity C)) (df : bincoprod_distributor copc copc F) (X Y : C) :
    bincoprod_distributor_natiso_commute_type copc n df X Y.
  Proof.
    unfold bincoprod_distributor_natiso_commute_type.
    refine (! id_left _ @ _ @ assoc' _ _ _ @ _).
    apply cancel_postcomposition.
    apply pathsinv0.
    apply df.
    apply maponpaths.
    apply BinCoproductArrowUnique.
    refine (assoc _ _ _ @ _ @ _).
    apply cancel_postcomposition.
    apply BinCoproductIn1Commutes.
    apply (pr1 n).
    refine (assoc _ _ _ @ _ @ _).
    apply cancel_postcomposition.
    apply BinCoproductIn2Commutes.
    apply (pr1 n).
  Qed.
  
  Definition indecomposability_invmor (X Y : FC) :
    SET ⟦ cov_homSet_functor I_{ FC} (cop_fc X Y), BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y) ⟧.
  Proof.
    set (FX := functor_FC_DG X).
    set (FY := functor_FC_DG Y).
    intros gxy.
    use (BinCoproductOfArrows _ (BinCoproductsHSET (pr112 FX) (pr112 FY))).
    refine (pr212 FX · _).
    apply (# (sym_mon_cov_homSet_functor FC)).
    apply functor_comp_is_id.
    refine (pr212 FY · _).
    apply (# (sym_mon_cov_homSet_functor FC)).
    apply functor_comp_is_id.
    exact (pr112 (fmonoidal_preservesunit functor_FC_DG · # functor_FC_DG gxy · distributor_functor_FC_DG X Y) tt).
  Defined.
  
  Lemma indecomposability_invmor_isrightinverse (X Y : FC) :
    bincoprod_antidistributor cop_fc BinCoproductsHSET (cov_homSet_functor I_{ FC}) X Y · indecomposability_invmor X Y =
      identity (BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y)).
  Proof.
    apply funextfun.
    intros f.
    change (indecomposability_invmor X Y
              (bincoprod_antidistributor cop_fc BinCoproductsHSET (cov_homSet_functor I_{ FC}) X Y f)  = f).
    induction f as [f | f].
    refine (maponpaths _ _ @ _).
    refine (assoc' _ _ _ @ _).
    use id_left.
    simpl.
    change (indecomposability_invmor X Y (f · BinCoproductIn1 (cop_fc X Y)) =
              (λ t : unit, inl f) tt).
    refine (_ @ maponpaths (λ g, g tt) _).
    Unshelve.
    4 : {
      change (HSet_SMC⟦I_{HSet_SMC}, BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y)⟧).
      apply (compose (pr112 (fmonoidal_preservesunit (functor_FC_DG) · # (pr1 functor_FC_DG) (f · BinCoproductIn1 (cop_fc X Y))
      · distributor_functor_FC_DG X Y))).
      apply BinCoproductOfArrows;
        apply (compose (pr212 (pr1 functor_FC_DG _)));
        apply (# (sym_mon_cov_homSet_functor FC));
        apply functor_comp_is_id.
    }
    reflexivity.
    (* unfortunately this amount of verbosity is necessary here *)
    refine (maponpaths (λ g : HSet_SMC ⟦ pr112 I_{ dg_cat},
      pr112 (pr11 (double_glued_BinCoproducts cop_fc BinCoproductsHSET dpbs_set (sym_mon_cov_homSet_functor FC)
               (alt_contra_functor (contra_homSet_functor I_{ FC})) (functor_FC_DG X) (functor_FC_DG Y)))
      ⟧, compose (C:=HSet_SMC) g (BinCoproductOfArrows SET (BinCoproductsHSET (pr112 (functor_FC_DG X)) (pr112 (functor_FC_DG Y)))
      (BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y))
      (pr212 (pr1 functor_FC_DG X) · # (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id X))
      (pr212 (pr1 functor_FC_DG Y) · # (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id Y)))) _ @ _).
    refine (assoc' _ _ _ @ _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    intermediate_path (pr112 ((pr211 (pr1 functor_FC_DG)) I_{ FC} (cop_fc X Y) (f · BinCoproductIn1 (cop_fc X Y)) · distributor_functor_FC_DG X Y)).
    reflexivity.
    refine (maponpaths (t1:= (pr211 (pr1 functor_FC_DG)) I_{ FC} (cop_fc X Y) (f · BinCoproductIn1 (cop_fc X Y)) · distributor_functor_FC_DG X Y) (λ g, pr112 g) _).
    refine (_ @ assoc' (C:= dg_cat) _ _ _ @ _).
    apply cancel_postcomposition.
    apply functor_comp.
    apply maponpaths.
    apply functor_preserves_In1'.
    rewrite id_right.
    refine (assoc' (C:=SET) (pr112 (fmonoidal_preservesunit (functor_FC_DG))) _
              (BinCoproductOfArrows SET (BinCoproductsHSET (pr112 (functor_FC_DG X)) (pr112 (functor_FC_DG Y)))
      (BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y))
      (pr212 (pr1 functor_FC_DG X) · # (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id X))
      (pr212 (pr1 functor_FC_DG Y) · # (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id Y))) @ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply BinCoproductIn1Commutes.
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply (pr212 (# (pr11 functor_FC_DG) f)).
    refine (_ @ _).
    apply cancel_postcomposition.
    apply (pr212 (fmonoidal_preservesunit functor_FC_DG)).
    apply funextfun.
    intros t; induction t.
    apply (maponpaths inl).
    refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    do 2 refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    do 2 refine (assoc' _ _ _ @ _).
    do 2 refine (id_left _ @ _).
    refine (_ @ assoc _ _ _ @ _ @ id_left _).
    apply maponpaths.
    apply (pr1 functor_comp_is_id).
    apply cancel_postcomposition.
    refine (maponpaths (λ g, g · _) preserves_tensorunit_FC_DG_is_id @ _).
    apply (pr2 functor_comp_is_id).
    (* completes inl-case *)
    (* inr-case : *)
    refine (maponpaths _ _ @ _).
    refine (assoc' _ _ _ @ _).
    use id_left.
    simpl.
    change (indecomposability_invmor X Y (f · BinCoproductIn2 (cop_fc X Y)) =
              (λ t : unit, inr f) tt).
    refine (_ @ maponpaths (λ g, g tt) _).
    Unshelve.
    3 : {
      change (HSet_SMC⟦I_{HSet_SMC}, BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y)⟧).
      apply (compose (pr112 (fmonoidal_preservesunit (functor_FC_DG) · # (pr1 functor_FC_DG) (f · BinCoproductIn2 (cop_fc X Y))
      · distributor_functor_FC_DG X Y))).
      apply BinCoproductOfArrows;
        apply (compose (pr212 (pr1 functor_FC_DG _)));
        apply (# (sym_mon_cov_homSet_functor FC));
        apply functor_comp_is_id.
    }
    reflexivity.
    (* unfortunately this amount of verbosity is necessary here *)
    refine (maponpaths (λ g : HSet_SMC ⟦ pr112 I_{ dg_cat},
      pr112 (pr11 (double_glued_BinCoproducts cop_fc BinCoproductsHSET dpbs_set (sym_mon_cov_homSet_functor FC)
               (alt_contra_functor (contra_homSet_functor I_{ FC})) (functor_FC_DG X) (functor_FC_DG Y)))
      ⟧, compose (C:=HSet_SMC) g (BinCoproductOfArrows SET (BinCoproductsHSET (pr112 (functor_FC_DG X)) (pr112 (functor_FC_DG Y)))
      (BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y))
      (pr212 (pr1 functor_FC_DG X) · # (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id X))
      (pr212 (pr1 functor_FC_DG Y) · # (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id Y)))) _ @ _).
    refine (assoc' _ _ _ @ _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    intermediate_path (pr112 ((pr211 (pr1 functor_FC_DG)) I_{ FC} (cop_fc X Y) (f · BinCoproductIn2 (cop_fc X Y)) · distributor_functor_FC_DG X Y)).
    reflexivity.
    refine (maponpaths (t1:= (pr211 (pr1 functor_FC_DG)) I_{ FC} (cop_fc X Y) (f · BinCoproductIn2 (cop_fc X Y)) · distributor_functor_FC_DG X Y) (λ g, pr112 g) _).
    refine (_ @ assoc' (C:= dg_cat) _ _ _ @ _).
    apply cancel_postcomposition.
    apply functor_comp.
    apply maponpaths.
    apply functor_preserves_In2'.
    rewrite id_right.
    refine (assoc' (C:=SET) (pr112 (fmonoidal_preservesunit (functor_FC_DG))) _
              (BinCoproductOfArrows SET (BinCoproductsHSET (pr112 (functor_FC_DG X)) (pr112 (functor_FC_DG Y)))
      (BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y))
      (pr212 (pr1 functor_FC_DG X) · # (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id X))
      (pr212 (pr1 functor_FC_DG Y) · # (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id Y))) @ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply BinCoproductIn2Commutes.
    refine (_ @ assoc _ _ _ @ _).
    apply maponpaths.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    apply cancel_postcomposition.
    apply (pr212 (# (pr11 functor_FC_DG) f)).
    refine (_ @ _).
    apply cancel_postcomposition.
    apply (pr212 (fmonoidal_preservesunit functor_FC_DG)).
    apply funextfun.
    intros t; induction t.
    apply (maponpaths inr).
    refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    do 2 refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    do 2 refine (assoc' _ _ _ @ _).
    do 2 refine (id_left _ @ _).
    refine (_ @ assoc _ _ _ @ _ @ id_left _).
    apply maponpaths.
    apply (pr1 functor_comp_is_id).
    apply cancel_postcomposition.
    refine (maponpaths (λ g, g · _) preserves_tensorunit_FC_DG_is_id @ _).
    apply (pr2 functor_comp_is_id).
  Qed.


  Lemma indecomposability_invmor_isleftinverse (X Y : FC) :
    indecomposability_invmor X Y · bincoprod_antidistributor cop_fc BinCoproductsHSET (cov_homSet_functor I_{ FC}) X Y =
      identity (cov_homSet_functor I_{ FC} (cop_fc X Y)).
  Proof.
    apply funextfun.
    intros f.
    change (bincoprod_antidistributor cop_fc BinCoproductsHSET (cov_homSet_functor I_{ FC}) X Y (indecomposability_invmor X Y f) = f).
    etrans.
    Unshelve.
    3 : {
      generalize tt.
      change (HSet_SMC ⟦I_{HSet_SMC}, cov_homSet_functor I_{ FC} (cop_fc X Y)⟧).
      refine (compose (pr212 (I_{dg_cat})) _).
      refine (compose (b:= sym_mon_cov_homSet_functor FC
                             ((functor_FC_DG ∙ forgetful_functor_dg_cat) I_{FC})) _ _).
      apply (# (sym_mon_cov_homSet_functor FC)).
      apply functor_comp_is_id.
      refine (compose (b:= sym_mon_cov_homSet_functor FC
                             ((functor_FC_DG ∙ forgetful_functor_dg_cat) (cop_fc X Y))) _ _).
      apply (# (sym_mon_cov_homSet_functor FC)).
      apply (# _ f).
      refine (compose (b:= sym_mon_cov_homSet_functor FC
                             (cop_fc ((functor_FC_DG ∙ forgetful_functor_dg_cat) X)
                                ((functor_FC_DG ∙ forgetful_functor_dg_cat) Y))) _ _).
      apply (# (sym_mon_cov_homSet_functor FC)).
      apply distributor_functor_FC_DG.
      apply (# (sym_mon_cov_homSet_functor FC)).
      apply BinCoproductOfArrows;
        apply functor_comp_is_id.
    }
    refine (_ @ maponpaths (λ g, g tt) _).
    Unshelve.
    unfold indecomposability_invmor.
    simpl.
    4 : {
      change (HSet_SMC ⟦I_{HSet_SMC}, cov_homSet_functor I_{ FC} (cop_fc X Y)⟧).
      apply (compose (((pr112 (fmonoidal_preservesunit functor_FC_DG · # functor_FC_DG f
                                 · (distributor_functor_FC_DG X Y)))))).
      refine (compose _ _).
      use (BinCoproductOfArrows SET).
      4 : {
        apply (compose (pr212 (functor_FC_DG X))).
        simpl. (*necessary*)
        use (# (sym_mon_cov_homSet_functor FC)).
        2 : apply functor_comp_is_id.
      }
      3 : {
        apply (compose (pr212 (functor_FC_DG Y))).
        use (# (sym_mon_cov_homSet_functor FC)).
        2 : apply functor_comp_is_id.
      }
      exact (BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y)).
      apply (bincoprod_antidistributor cop_fc BinCoproductsHSET).      
    }
    simpl. (*necessary*)
    reflexivity.
    refine (assoc' (pr112 (fmonoidal_preservesunit (functor_FC_DG)) · pr112 (# (functor_FC_DG) f)) _
              (BinCoproductOfArrows SET (BinCoproductsHSET (pr112 (functor_FC_DG X)) (pr112 (functor_FC_DG Y)))
       (BinCoproductsHSET (cov_homSet_functor I_{ FC} X) (cov_homSet_functor I_{ FC} Y))
       (pr212 (functor_FC_DG X)
        · (# (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id X)))
       (pr212 (functor_FC_DG Y) · # (sym_mon_cov_homSet_functor FC) (pr11 functor_comp_is_id Y))
     · bincoprod_antidistributor cop_fc BinCoproductsHSET (cov_homSet_functor I_{ FC}) X Y) @ _).    
    refine (assoc' _ _ _ @ _).
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ g, g · _) _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    2 : {
      refine (pr212 (fmonoidal_preservesunit functor_FC_DG) @ _).
      apply maponpaths, maponpaths.
      apply preserves_tensorunit_FC_DG_is_id.
    }
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ g, g · _) (pr212 (# functor_FC_DG f))).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ g, g · _) (pr212 (distributor_functor_FC_DG X Y))).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    use (BinCoproductArrowsEq SET _ _
           (BinCoproductsHSET (pr112 (functor_FC_DG X)) (pr112 (functor_FC_DG Y)))
           (cov_homSet_functor I_{ FC} (cop_fc X Y)));
      refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    refine (maponpaths (λ g, g · _) (BinCoproductIn1Commutes _ _ _ _ _ _ _) @ _).
    refine (_ @ ! maponpaths (λ g, g · _) (BinCoproductIn1Commutes _ _ _ _ _ _ _)).
    do 2 refine (assoc' _ _ _ @ _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ functor_comp _ _ _).
    refine (maponpaths (compose _) _ @ _).
    apply BinCoproductIn1Commutes.
    refine (! functor_comp _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0, BinCoproductIn1Commutes.
    refine (maponpaths (λ g, g · _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
    refine (_ @ ! maponpaths (λ g, g · _) (BinCoproductIn2Commutes _ _ _ _ _ _ _)).
    do 2 refine (assoc' _ _ _ @ _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (_ @ functor_comp _ _ _).
    refine (maponpaths (compose _) _ @ _).
    apply BinCoproductIn2Commutes.
    refine (! functor_comp _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0, BinCoproductIn2Commutes.
    refine (maponpaths (λ g, g tt) _ @ _).
    refine (assoc (C:=SET) (pr212 I_{ dg_cat}) _ (# (sym_mon_cov_homSet_functor FC) (# (functor_FC_DG ∙ forgetful_functor_dg_cat) f)
        · (# (sym_mon_cov_homSet_functor FC) (pr1 (pr1 distributor_functor_FC_DG X Y))
           · # (sym_mon_cov_homSet_functor FC)
               (BinCoproductOfArrows FC
                  (cop_fc ((functor_FC_DG ∙ forgetful_functor_dg_cat) X) ((functor_FC_DG ∙ forgetful_functor_dg_cat) Y)) 
                  (cop_fc X Y) (pr11 functor_comp_is_id X) (pr11 functor_comp_is_id Y)))) @ _).
    apply cancel_postcomposition.
    simpl. (* necessary *)
    refine (maponpaths (λ g, (λ _ : unit, g)) _).
    refine (_ @ id_left _).
    apply cancel_postcomposition.
    simpl. (* necessary *)
    apply id_left.
    refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    do 2 refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    do 2 refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    refine (assoc _ _ _ @ _ @ assoc' _ _ _ @ _ @ id_right _).
    apply cancel_postcomposition.
    apply pathsinv0, (nat_z_iso_to_trans_inv functor_comp_is_id).
    apply maponpaths.
    refine (assoc _ _ _ @ _ @ _).
    apply cancel_postcomposition.
    Unshelve.
    3 : {
      apply BinCoproductOfArrows;
      apply functor_comp_is_id.
    }
    simpl.
    refine (maponpaths (compose _) (functor_comp_bincoprod_distributor_eq X Y) @ _).
    refine (! nattrans_bincoprod_distributors (identity_bincoprod_distributor cop_fc) functor_comp_bincoprod_distributor
              (nat_z_iso_to_trans_inv functor_comp_is_id) X Y @ _).
    refine (id_left _ @ _).
    easy.
    etrans.
    apply BinCoproductOfArrows_comp.
    apply pathsinv0, BinCoproductArrowUnique;
      refine (id_right _ @ ! id_left _ @ _);
      apply cancel_postcomposition;
      apply pathsinv0;
      apply (pr2 functor_comp_is_id).
  Qed.
    
  Lemma indecomposability_invmor_isinverse (X Y : FC) :
    is_inverse_in_precat (bincoprod_antidistributor cop_fc BinCoproductsHSET (cov_homSet_functor I_{ FC}) X Y)
      (indecomposability_invmor X Y).
  Proof.
    split.
    apply indecomposability_invmor_isrightinverse.
    apply indecomposability_invmor_isleftinverse.
  Qed.
  
  Definition indecomposability (X Y : FC) :
    z_iso (BinCoproductsHSET (cov_homSet_functor (monoidal_unit FC) X) (cov_homSet_functor (monoidal_unit FC) Y))
      (cov_homSet_functor (monoidal_unit FC) (cop_fc X Y)).
  Proof.
    use tpair.
    apply (bincoprod_antidistributor cop_fc BinCoproductsHSET).
    use tpair.
    2 : apply indecomposability_invmor_isinverse.
  Defined.
  
End indecomposability.

Lemma fully_faithful_comp {C D E : category} (F : catiso C D) (G : catiso D E) : fully_faithful (F ∙ G).
Proof.
  intros x y.
  apply twooutof3c.
  apply F.
  apply G.
Qed.

Definition catiso_comp {C D E : category} (F : catiso C D) (G : catiso D E) : catiso C E.
Proof.
  exists (functor_composite F G).
  split.
  apply fully_faithful_comp.
  apply twooutof3c.
  apply F.
  apply G.
Defined.


(* (* Incomplete : *)
Section coindecomposability.
  

  Context (FC : sym_monoidal_cat) (pfc : BinProducts FC).

  Context (functor_FC_DG : symmetric_strong_monoidal_functor FC (dg_cat FC)).

  (*
    (distributor_functor_FC_DG : bincoprod_distributor cop_fc
                                            (double_glued_BinCoproducts cop_fc BinCoproductsHSET dpbs_set _ _) functor_FC_DG)
    (functor_comp_is_id : nat_z_iso (functor_composite functor_FC_DG forgetful_functor_dg_cat) (functor_identity FC)).*)

  Definition dg_cat_op : sym_monoidal_cat.
  Proof.
    use double_glued_total_sym_monoidal_cat.
    apply (sym_monoidal_opp_cat FC).
    exact HSet_SMC.
    apply doublePullbacks_from_Pullbacks.
    apply PullbacksHSET.
    apply sym_mon_cov_homSet_functor.
    apply alt_contra_functor.
    apply contra_homSet_functor.
    apply (monoidal_unit FC).
    use natural_contraction_hom_functors.
  Defined.

  Definition symcatop_functor_data :
    functor_data dg_cat_op
      (double_glued_total_altopp (sym_mon_cov_homSet_functor FC) (alt_contra_functor (contra_homSet_functor I_{ FC}))).
  Proof.
    use tpair.
    apply idfun.
    intros A B (f, df).
    exists f.
    use tpair.
    exists (pr11 df).
    refine (pr21 df @ _).
    apply maponpaths, funextfun; intros h.
    apply (assoc (C:=FC)).
    exists (pr12 df).
    refine (_ @ pr22 df).
    apply cancel_postcomposition, funextfun; intros h.
    apply (assoc' (C:=FC)).
  Defined.

  Lemma symcatop_functorlaws : is_functor symcatop_functor_data.
  Proof.
    split.
    intros A.
    apply double_glued_total_mor_eq_transp; split3; apply idpath.
    intros A B C f g.
    apply double_glued_total_mor_eq_transp; split3; apply idpath.
  Qed.

  Definition symcataltop_functor : functor dg_cat_op (double_glued_total_altopp (sym_mon_cov_homSet_functor FC) (alt_contra_functor (contra_homSet_functor I_{ FC}))).
  Proof.
    use tpair.
    apply symcatop_functor_data.
    apply symcatop_functorlaws.
  Defined.

  Lemma symcataltop_functor_isiso : is_catiso symcataltop_functor.
  Proof.
    split.
    intros A B F.
    use tpair.
    use tpair.
    exists (pr1 F).
    split.
    exists (pr112 F).
    refine (pr212 F @ _).
    apply maponpaths, funextfun; intros h.
    apply (assoc' (C:=FC)).
    exists (pr122 F).
    refine (_ @ pr222 F).
    apply cancel_postcomposition, funextfun; intros h.
    apply (assoc (C:=FC)).
    apply double_glued_total_mor_eq_transp; split3; apply idpath.
    intros (t, eq).
    induction eq.
    apply subtypePath.
    intros x; apply homset_property.
    apply double_glued_total_mor_eq_transp; split3; apply idpath.
    intros A.
    use tpair.
    use tpair.
    apply A.
    apply idpath.
    intros (B, eq).
    induction eq.
    apply idpath.
  Qed.
  
  Definition symcataltop_iso :
    catiso (dg_cat_op)
      (double_glued_total_altopp (sym_mon_cov_homSet_functor FC) (alt_contra_functor (contra_homSet_functor I_{ FC}))).
  Proof.
    use tpair.
    apply symcataltop_functor.
    apply symcataltop_functor_isiso.
  Defined.
  
  Definition symcatop_iso :
    catiso (dg_cat_op) (sym_monoidal_opp_cat (dg_cat FC)).
  Proof.
    use catiso_comp.
    2 : apply symcataltop_iso.
    apply double_glued_general_opp_iso.
  Defined.
  (*
  Definition symcatop_fmonoidal_data : fmonoidal_data dg_cat_op (sym_monoidal_opp_cat (dg_cat FC)) symcatop_iso.
  Proof.
    split.
    intros (R1, ((U1, l1), (X1, l1'))) (R2, ((U2, l2), (X2, l2'))).
    use tpair.
    apply identity.
    split; use tpair.
    intros ((((a1, a2), a3), a4), a5).
    revert a1 a2 a3 a4 a5; simpl; intros a1 a2 a3 a4 a5.
    split.
    apply a4.
    revert a1 eq; simpl; intros a1 eq.
    intros ((x1, x2), y).
    apply doublePullbackArrow.
    simpl.
  Defined.
  
  Definition symcatop_fmonoidal_lax : fmonoidal_lax dg_cat_op (sym_monoidal_opp_cat (dg_cat FC)) symcatop_iso.
  Proof.
    use tpair.
  Defined.
  
  Definition symcatop_fmonoidal : fmonoidal dg_cat_op (sym_monoidal_opp_cat (dg_cat FC)) symcatop_iso.
  Proof.
    use tpair.
  Defined.
  
  Lemma symcatop_eq : dg_cat_op = sym_monoidal_opp_cat (dg_cat FC).
  Proof.
    use total2_paths_f.
    use total2_paths_f. 
    apply catiso_is_path_cat.
    use catiso_comp.
    2 : apply symcataltop_iso.
    apply double_glued_general_opp_iso.
    apply subtypePath.
    intros M; apply isaprop_monoidal_laws.
    use total2_paths_f.
    use total2_paths_f.
    simpl.
  Qed.
  
  Definition functor_FC_DG_op : symmetric_strong_monoidal_functor (sym_monoidal_opp_cat FC) . *)
  
  Definition coindecomposability (X Y : FC) :
    z_iso (BinCoproductsHSET (contra_homSet_functor (monoidal_unit FC) X) (contra_homSet_functor (monoidal_unit FC) Y))
      (contra_homSet_functor (monoidal_unit FC) (pfc X Y)).
  Proof.
    use (indecomposability (sym_monoidal_opp_cat FC) pfc).
    
  Defined.

  

  Context (functor_FC_DG : symmetric_strong_monoidal_functor FC (dg_cat FC))
    (distributor_functor_FC_DG : bincoprod_distributor cop_fc
                                            (double_glued_BinCoproducts cop_fc BinCoproductsHSET dpbs_set _ _) functor_FC_DG)
    (functor_comp_is_id : nat_z_iso (functor_composite functor_FC_DG forgetful_functor_dg_cat) (functor_identity FC)).

End coindecomposability. *)
