import «section 3».GammaGroundLemma33
import «section 3».GammaGroundRVFibreComparison
import «section 3».GammaGroundRVFibreInvariance
import Section4.EarlierRVInputs
import «section 3».GammaGroundRVDimensionConsequences
import «section 3».GammaGroundRVFibreDimension
import «section 3».RVFibreDimension
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r : ℕ}

theorem gammaGroundRVFibreDim_ofReal
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hS : Cardinal.mk ground.real < κ)
    (A : DefSet (rawMixedSpace (M := M) n r) ground.real) :
    gammaGroundRVFibreDim (GammaGroundDefSet.ofReal (hc := hc) (ground := ground) A) = rvFibreDim A := by
  change (⨆ a : A, gammaGroundRVDim (gammaGroundFixedVFFibre (GammaGroundDefSet.ofReal (hc := hc) (ground := ground) A) a.val.1)) = ⨆ a : A, rvDim (fixedVFFibre A a.val.1)
  apply congrArg (fun f : A → ℕ => iSup f)
  funext a
  change gammaGroundRVDim (GammaGroundDefSet.ofReal (hc := hc)
    (ground := ⟨ground.real ∪ Set.range (vfValues a.val.1), ground.gamma⟩) (fixedVFFibre A a.val.1)) = _
  exact gammaGroundRVDim_ofReal (rvExchangeInput_of_earlier hκ hs h00) hκ hs
    (gammaRVAlgebraicityInput_of_earlier hκ hs h00)
    (small_union_range hκ ground.real hS (vfValues a.val.1)) _

theorem gammaGroundRVFibreDimension_ofReal
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hS : Cardinal.mk ground.real < κ)
    (A : DefSet (rawMixedSpace (M := M) n r) ground.real) :
    gammaGroundRVFibreDimension (GammaGroundDefSet.ofReal (hc := hc) (ground := ground) A) = rvFibreDimension A := by
  unfold gammaGroundRVFibreDimension rvFibreDimension
  rw [gammaGroundRVFibreDim_ofReal hκ hs h00 hS]
  rfl

end DiamondIntegral.Section3
