import «section 3».GammaGroundRVCharacterSymmetry
import Section4.ResidueScaledFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 400000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M))
variable (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)

def rvCharacterResidueScalar (a : (CanonicalRV.RVSort M)ˣ) : (RVResidueField M)ˣ :=
  χ (QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom a))

theorem rvOriginalGroundCharacterTwist_formula (a : (CanonicalRV.RVSort M)ˣ) :
    rvOriginalGroundCharacterTwist B χ a = residueUnitToRV (rvCharacterResidueScalar B χ a) * a := rfl

/-- Proof-only normalization converts the actual RV twist into the
expected diagonal residue-field action. -/
theorem rvOriginalGroundCharacterTwistZero_normalized
    (a : (CanonicalRV.RVSort M)ˣ) (x : ModelResidue M) :
    rvOriginalGroundCharacterTwistZero B χ ((a : CanonicalRV.RVSort M) * residueRV x) =
      (a : CanonicalRV.RVSort M) * residueRV ((rvCharacterResidueScalar B χ a : ModelResidue M) * x) := by
  rw [map_mul,rvOriginalGroundCharacterTwistZero_residue,rvOriginalGroundCharacterTwistZero_coe]
  rw [rvOriginalGroundCharacterTwist_formula,Units.val_mul]
  have hr : (residueUnitToRV (rvCharacterResidueScalar B χ a) : CanonicalRV.RVSort M) =
      residueRV (rvCharacterResidueScalar B χ a : ModelResidue M) := rfl
  rw [hr,residueRV_mul]
  ac_rfl

/-- The normalized graph is invariant under every character of the
original-ground quotient, with the same original RV relation. -/
theorem gammaGroundNormalizedRelation_character_invariant
    {hc : CanonicalStructure.IsCanonical (M := M)} {ι : Type} [Finite ι]
    (A : Set (ι → M)) (hA : GammaGroundRawDefinable hc B A)
    (hproper : ∀ z ∈ A, ∀ i, iRV (z i))
    (a : ι → (CanonicalRV.RVSort M)ˣ) (x : ι → ModelResidue M) :
    (fun i => ((a i : CanonicalRV.RVSort M) * residueRV (x i)).val) ∈ A ↔
      (fun i => ((a i : CanonicalRV.RVSort M) *
        residueRV ((rvCharacterResidueScalar B χ (a i) : ModelResidue M) * x i)).val) ∈ A := by
  have h := gammaGroundRawRV_character_invariant B χ A hA hproper
    (fun i => (a i : CanonicalRV.RVSort M) * residueRV (x i))
  simpa only [rvOriginalGroundCharacterTwistZero_normalized] using h

end DiamondIntegral.Section3
