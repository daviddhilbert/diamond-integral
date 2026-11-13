import «section 3».MeasuredTensorRankLayerMatchCovers
import «section 3».TensorRankLayerTwoSidedCovers
import «section 3».TensorLocalMatchReversal
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k m : ℕ}

/-- The same finite matrix of local matches covers maximal-rank charts
in both directions away from finite proper old-ground hyperplanes. -/
structure GammaGroundMeasuredTensorRankLayerTwoSidedCover
    (L R : GammaGroundMeasuredTensorRankLayer hc B k m)
    (F : GammaGroundBijection L.object.underlying.domain R.object.underlying.domain) where
  patches : ∀ i j, Finset (GammaGroundMeasuredTensorLocalMatch F
    (L.residue i) (L.gamma i) (L.unmeasured.topMap i) (L.weight i) (L.weight_definable i)
    (R.residue j) (R.gamma j) (R.unmeasured.topMap j) (R.weight j) (R.weight_definable j))
  sourceHyperplanes : Fin L.topCount → Finset (GammaGroundCharacterHyperplane B m)
  targetHyperplanes : Fin R.topCount → Finset (GammaGroundCharacterHyperplane B m)
  source_cover : ∀ i (u : gammaGroundNativeProductDomain (L.residue i) (L.gamma i)),
    (∃ j E, E ∈ patches i j ∧ u.val ∈ E.source.source.carrier) ∨
      ∃ h ∈ sourceHyperplanes i, rvUnitTupleValues u.val.1 ∈ h.carrier
  target_cover : ∀ j (v : gammaGroundNativeProductDomain (R.residue j) (R.gamma j)),
    (∃ i E, E ∈ patches i j ∧ v.val ∈ E.target.source.carrier) ∨
      ∃ h ∈ targetHyperplanes j, rvUnitTupleValues v.val.1 ∈ h.carrier

theorem gammaGroundMeasuredTensorRankLayer_two_sided_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (L R : GammaGroundMeasuredTensorRankLayer hc B k m)
    (F : GammaGroundBijection L.object.underlying.domain R.object.underlying.domain)
    (hF : ∀ x, L.object.combinedWeight x = R.object.combinedWeight (F.map x)) :
    Nonempty (GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) := by
  have hf (i : Fin L.topCount) := gammaGroundMeasuredTensorRankLayer_top_match_cover hκ hs h00 hsmall hγsmall hΓ L R F hF i
  have hb (j : Fin R.topCount) := gammaGroundMeasuredTensorRankLayer_top_match_cover hκ hs h00 hsmall hγsmall hΓ R L F.symm
    (fun y => (congrArg R.object.combinedWeight (F.map.apply_inverse F.bijective y)).symm.trans (hF (F.symm.map y)).symm) j
  choose K J hK using hf
  choose Q H hQ using hb
  let E := fun i j => positiveSigmaFinsetFibre (K i) j ∪
    (positiveSigmaFinsetFibre (Q j) i).image (fun e => e.unsymm F)
  refine ⟨⟨E,J,H,?_,?_⟩⟩
  · intro i u
    rcases hK i u with ⟨⟨j,e⟩,he,hu⟩ | hu
    · exact Or.inl ⟨j,e,Finset.mem_union_left _ ((positiveSigmaFinsetFibre_mem _ _ _).mpr he),hu⟩
    · exact Or.inr hu
  · intro j v
    rcases hQ j v with ⟨⟨i,e⟩,he,hv⟩ | hv
    · refine Or.inl ⟨i,e.unsymm F,Finset.mem_union_right _ ?_,hv⟩
      exact Finset.mem_image.mpr ⟨e,(positiveSigmaFinsetFibre_mem _ _ _).mpr he,rfl⟩
    · exact Or.inr hv
end DiamondIntegral.Section3
