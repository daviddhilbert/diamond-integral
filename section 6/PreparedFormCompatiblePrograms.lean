import «section 6».PromotedFormCompatiblePrograms

/-! Prepared form-compatible actual chains promote to one complete
measured program, including terminal Gamma constancy and every
intermediate contracted-core form condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_promoted_prepared_form_compatible_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (a : Fin p → M) (hsmall : Cardinal.mk ↥(S ∪ Set.range a) < κ)
    (hΓ : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M))
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} {f : Map (A.fibre a) B}
    (ω : Map (A.fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (h : FormCompatibleSynchronizedChain (G := G) (Fin k) (A.fibre a) B f (fun i => (P i).fibre a) ω)
    (hARV : IsRVPullback (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hPA i)).image.carrier)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (hConst : ∀ t u : A.fibre a,(f t).val.2=(f u).val.2 → (ω t).val=(ω u).val) :
    ∃ T : CentripetalProgramTemplate (M := M) S p n r s,a ∈ T.measuredFormGood A P W ∧
      {z | Sum.elim a z ∈ (T.transition A).graph}=
        (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph := by
  obtain ⟨T,ha,hCore,hGraph⟩ := exists_promoted_form_compatible_program h00 hc linear hκ hs hv a hsmall hΓ
    h A P W rfl (fun _ => rfl) hARV hW
  have hPreparedGood : a ∈ T.preparedGood A P := by
    refine ⟨ha,Set.mem_iInter.mpr (fun i => ?_)⟩
    apply (mem_rvPullbackParameterLocus_iff (T.pieceTarget A (P i)).typedGraph a
      ((T.pieceTarget A (P i)).fibre a) ((T.pieceTarget A (P i)).fibre_code a).symm).mpr
    have hPiece : (T.pieceTarget A (P i)).fibre a=(f.restrict (hPA i)).image :=
      mixedRelationImageTemplate_at_restriction (P i) (T.transition A).graph (T.transition A).definable
        a f (hPA i) hGraph
    rw [hPiece]
    exact hPrepared i
  exact ⟨T,⟨⟨hPreparedGood,(gammaTransitionConstantParameterLocus_iff a _ _ f ω hGraph hW).mpr hConst⟩,hCore⟩,hGraph⟩

end DiamondIntegral.Section6
