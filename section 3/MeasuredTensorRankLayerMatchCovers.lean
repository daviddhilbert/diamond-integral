import «section 3».MeasuredTensorRankLayerAtlas
import «section 3».MeasuredNativeProductMatchCovers
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

abbrev GammaGroundMeasuredTensorRankLayerMatchEntry
    (L R : GammaGroundMeasuredTensorRankLayer hc B k m)
    (F : GammaGroundBijection L.object.underlying.domain R.object.underlying.domain)
    (i : Fin L.topCount) :=
  Σ j : Fin R.topCount, GammaGroundMeasuredTensorLocalMatch F
    (L.residue i) (L.gamma i) (L.unmeasured.topMap i) (L.weight i) (L.weight_definable i)
    (R.residue j) (R.gamma j) (R.unmeasured.topMap j) (R.weight j) (R.weight_definable j)

/-- Every maximal-rank source chart has a finite old-ground cover by
actual two-sided product matches and proper character hyperplanes.
The lower-rank target branches contribute only hyperplanes. -/
theorem gammaGroundMeasuredTensorRankLayer_top_match_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (L R : GammaGroundMeasuredTensorRankLayer hc B k m)
    (F : GammaGroundBijection L.object.underlying.domain R.object.underlying.domain)
    (hF : ∀ x, L.object.combinedWeight x = R.object.combinedWeight (F.map x))
    (i : Fin L.topCount) :
    ∃ K : Finset (GammaGroundMeasuredTensorRankLayerMatchEntry L R F i),
      ∃ J : Finset (GammaGroundCharacterHyperplane B m),
      ∀ u : gammaGroundNativeProductDomain (L.residue i) (L.gamma i),
        (∃ E ∈ K, u.val ∈ E.2.source.source.carrier) ∨
          ∃ h ∈ J, rvUnitTupleValues u.val.1 ∈ h.carrier := by
  have ht (j : Fin R.topCount) := gammaGroundMeasuredNativeProductTransition_square_match_cover
    hκ hs h00 hsmall hγsmall hΓ F L.object.combinedWeight R.object.combinedWeight hF (L.residue i) (L.gamma i) (L.unmeasured.topMap i) (L.unmeasured.topMap_injective i)
      (R.residue j) (R.gamma j) (R.unmeasured.topMap j) (R.unmeasured.topMap_injective j)
      (L.weight i) (R.weight j) (L.weight_definable i) (R.weight_definable j)
        (L.topMap_weight i) (R.topMap_weight j)
  choose K J hcov using ht
  have hl (j : Fin R.lower.length) := gammaGroundNativeProductTransition_lower_arity_cover
    hκ hs h00 hsmall hγsmall hΓ F (L.residue i) (L.gamma i) (L.unmeasured.topMap i) (L.unmeasured.topMap_injective i)
      (R.lower.get j).residue (R.lower.get j).gamma (R.unmeasured.lowerMap j) (R.unmeasured.lowerMap_injective j) (R.unmeasured.lower_rank_at j)
  choose Q hlow using hl
  let allK : Finset (GammaGroundMeasuredTensorRankLayerMatchEntry L R F i) :=
    Finset.univ.biUnion (fun j => (K j).image (fun E => ⟨j,E⟩))
  let allJ := (Finset.univ.biUnion J) ∪ (Finset.univ.biUnion Q)
  refine ⟨allK,allJ,?_⟩
  intro u
  rcases R.unmeasured.cover (F.map (L.unmeasured.topMap i u)) with ⟨j,v,hv⟩ | ⟨j,v,hv⟩
  · have hu : u.val ∈ (gammaGroundChartTransitionDomain F (L.unmeasured.topMap i) (R.unmeasured.topMap j)).carrier :=
      ⟨u,rfl,v,congrArg (fun z : R.object.underlying.domain => z.val) hv⟩
    rcases hcov j ⟨u.val,hu⟩ with ⟨E,hE,he⟩ | ⟨h,hh,he⟩
    · apply Or.inl
      refine ⟨⟨j,E⟩,?_,he⟩
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,Finset.mem_image.mpr ⟨E,hE,rfl⟩⟩
    · exact Or.inr ⟨h,Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hh⟩),he⟩
  · have hu : u.val ∈ (gammaGroundChartTransitionDomain F (L.unmeasured.topMap i) (R.unmeasured.lowerMap j)).carrier :=
      ⟨u,rfl,v,congrArg (fun z : R.object.underlying.domain => z.val) hv⟩
    obtain ⟨h,hh,he⟩ := hlow j ⟨u.val,hu⟩
    exact Or.inr ⟨h,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hh⟩),he⟩
end DiamondIntegral.Section3
