import «section 3».GammaMeasuredSchemaPromotion
import «section 3».GammaMeasuredRowPresentations

/-! For an actual full-weight row the existing essential schema retains
the entire row. This bridges measured chart promotion to the checked
native isomorphism-promotion theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaSchemaRepresents_essential_of_full
    (U : GammaObjectAt C Set.univ k) (hU : GammaFullWeightAt U)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object.obj) k sp) (z : Fin p → M)
    (hF : gammaSchemaRepresents U.toGamma F z) :
    gammaSchemaRepresents U.toGamma (essentialFiniteVolumeSchema F) z := by
  have hn (u : rvObjectDomain U.object.obj) (i : Fin k) :
      ((rvObjectVolume U.object.obj u).val i).val ≠ @iRVZero M sM := by
    intro hz
    exact (gammaFullWeightAt_iff_nonzero U).mp hU u i
      (hz.trans (CanonicalStructure.sortZero_normalize .rv).symm)
  apply gammaSchemaRepresents_of_typed
  · intro x
    rw [essentialFiniteVolumeSchema_rowDomain]
    constructor
    · rintro ⟨y,hy,_⟩
      obtain ⟨u,hu,_⟩ := (gammaSchemaRepresents_volume U.toGamma F z hF x y).mp hy
      exact hu ▸ u.property
    · intro hx
      let u : rvObjectDomain U.object.obj := ⟨x,hx⟩
      exact ⟨(rvObjectVolume U.object.obj u).val,
        (gammaSchemaRepresents_volume U.toGamma F z hF _ _).mpr ⟨u,rfl,rfl⟩,hn u⟩
  · intro x y
    rw [essentialFiniteVolumeSchema_rowVolume]
    constructor
    · exact fun h => (gammaSchemaRepresents_volume U.toGamma F z hF x y).mp h.1
    · intro h
      obtain ⟨u,hu,hv⟩ := h
      refine ⟨(gammaSchemaRepresents_volume U.toGamma F z hF x y).mpr ⟨u,hu,hv⟩,?_⟩
      intro i
      exact congrArg (fun v => (v i).val) hv ▸ hn u i

end DiamondIntegral.Section3
