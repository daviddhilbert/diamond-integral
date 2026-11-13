import «section 3».TensorRankLayerAtlas
import «section 3».NativeProductMatchCovers
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

abbrev GammaGroundTensorRankLayerMatchEntry
    (L R : GammaGroundTensorRankLayer hc B k m)
    (F : GammaGroundBijection L.object.domain R.object.domain) (i : Fin L.topCount) :=
  Σ j : Fin R.topCount, GammaGroundTensorLocalMatch F
    (L.residue i) (L.gamma i) (L.topMap i) (R.residue j) (R.gamma j) (R.topMap j)

/-- Every maximal-rank source chart has a finite old-ground cover by
actual two-sided product matches and proper character hyperplanes.
The lower-rank target branches contribute only hyperplanes. -/
theorem gammaGroundTensorRankLayer_top_match_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (L R : GammaGroundTensorRankLayer hc B k m)
    (F : GammaGroundBijection L.object.domain R.object.domain) (i : Fin L.topCount) :
    ∃ K : Finset (GammaGroundTensorRankLayerMatchEntry L R F i),
      ∃ J : Finset (GammaGroundCharacterHyperplane B m),
      ∀ u : gammaGroundNativeProductDomain (L.residue i) (L.gamma i),
        (∃ E ∈ K, u.val ∈ E.2.source.source.carrier) ∨
          ∃ h ∈ J, rvUnitTupleValues u.val.1 ∈ h.carrier := by
  have ht (j : Fin R.topCount) := gammaGroundNativeProductTransition_square_match_cover
    hκ hs h00 hsmall hγsmall hΓ F (L.residue i) (L.gamma i) (L.topMap i) (L.topMap_injective i)
      (R.residue j) (R.gamma j) (R.topMap j) (R.topMap_injective j)
  choose K J hcov using ht
  have hl (j : Fin R.lower.length) := gammaGroundNativeProductTransition_lower_arity_cover
    hκ hs h00 hsmall hγsmall hΓ F (L.residue i) (L.gamma i) (L.topMap i) (L.topMap_injective i)
      (R.lower.get j).residue (R.lower.get j).gamma (R.lowerMap j) (R.lowerMap_injective j) (R.lower_rank_at j)
  choose Q hlow using hl
  let allK : Finset (GammaGroundTensorRankLayerMatchEntry L R F i) :=
    Finset.univ.biUnion (fun j => (K j).image (fun E => ⟨j,E⟩))
  let allJ := (Finset.univ.biUnion J) ∪ (Finset.univ.biUnion Q)
  refine ⟨allK,allJ,?_⟩
  intro u
  rcases R.cover (F.map (L.topMap i u)) with ⟨j,v,hv⟩ | ⟨j,v,hv⟩
  · have hu : u.val ∈ (gammaGroundChartTransitionDomain F (L.topMap i) (R.topMap j)).carrier :=
      ⟨u,rfl,v,congrArg (fun z : R.object.domain => z.val) hv⟩
    rcases hcov j ⟨u.val,hu⟩ with ⟨E,hE,he⟩ | ⟨h,hh,he⟩
    · apply Or.inl
      refine ⟨⟨j,E⟩,?_,he⟩
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,Finset.mem_image.mpr ⟨E,hE,rfl⟩⟩
    · exact Or.inr ⟨h,Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hh⟩),he⟩
  · have hu : u.val ∈ (gammaGroundChartTransitionDomain F (L.topMap i) (R.lowerMap j)).carrier :=
      ⟨u,rfl,v,congrArg (fun z : R.object.domain => z.val) hv⟩
    obtain ⟨h,hh,he⟩ := hlow j ⟨u.val,hu⟩
    exact Or.inr ⟨h,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hh⟩),he⟩
end DiamondIntegral.Section3
