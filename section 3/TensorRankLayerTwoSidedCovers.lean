import «section 3».TensorRankLayerMatchCovers
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

def positiveSigmaFinsetFibre {J : Type} {E : J → Type}
    (K : Finset (Σ j, E j)) (j : J) : Finset (E j) :=
  K.preimage (Sigma.mk j) (by intro a _ b _ h; simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h)

@[simp] theorem positiveSigmaFinsetFibre_mem {J : Type} {E : J → Type}
    (K : Finset (Σ j, E j)) (j : J) (e : E j) :
    e ∈ positiveSigmaFinsetFibre K j ↔ Sigma.mk j e ∈ K := Finset.mem_preimage

/-- The same finite matrix of local matches covers maximal-rank charts
in both directions away from finite proper old-ground hyperplanes. -/
structure GammaGroundTensorRankLayerTwoSidedCover
    (L R : GammaGroundTensorRankLayer hc B k m)
    (F : GammaGroundBijection L.object.domain R.object.domain) where
  patches : ∀ i j, Finset (GammaGroundTensorLocalMatch F
    (L.residue i) (L.gamma i) (L.topMap i) (R.residue j) (R.gamma j) (R.topMap j))
  sourceHyperplanes : Fin L.topCount → Finset (GammaGroundCharacterHyperplane B m)
  targetHyperplanes : Fin R.topCount → Finset (GammaGroundCharacterHyperplane B m)
  source_cover : ∀ i (u : gammaGroundNativeProductDomain (L.residue i) (L.gamma i)),
    (∃ j E, E ∈ patches i j ∧ u.val ∈ E.source.source.carrier) ∨
      ∃ h ∈ sourceHyperplanes i, rvUnitTupleValues u.val.1 ∈ h.carrier
  target_cover : ∀ j (v : gammaGroundNativeProductDomain (R.residue j) (R.gamma j)),
    (∃ i E, E ∈ patches i j ∧ v.val ∈ E.target.source.carrier) ∨
      ∃ h ∈ targetHyperplanes j, rvUnitTupleValues v.val.1 ∈ h.carrier

theorem gammaGroundTensorRankLayer_two_sided_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (L R : GammaGroundTensorRankLayer hc B k m)
    (F : GammaGroundBijection L.object.domain R.object.domain) :
    Nonempty (GammaGroundTensorRankLayerTwoSidedCover L R F) := by
  have hf (i : Fin L.topCount) := gammaGroundTensorRankLayer_top_match_cover hκ hs h00 hsmall hγsmall hΓ L R F i
  have hb (j : Fin R.topCount) := gammaGroundTensorRankLayer_top_match_cover hκ hs h00 hsmall hγsmall hΓ R L F.symm j
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
