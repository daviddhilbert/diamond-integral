import «section 3».GammaGroundGammaRVSemiringMonicity
import «section 3».GammaGroundFiniteGammaRESMonicity
import «section 3».GammaGroundContext
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The only additional cited input for C002, specialized to the actual
residue coefficient fields and exact original-ground weight groups.
Residue characteristic zero is discharged from the context here. -/
abbrev GammaGroundCoefficientClassification (C : GammaGroundContext M) : Prop := by
  letI : CharZero (ModelResidue M) := rvResidueField_charZero C.model00
  exact ∀ (n : ℕ) (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
    ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
      ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup C.base a b)

/-- Both horizontal arrows of the actual positive coefficient square
are monomorphisms in the manuscript's VF/Gamma-generated context.
The approved diagonal classification is the only extra cited input. -/
theorem gammaGroundContext_coefficient_monomorphisms
    (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (RY : GammaGroundCoefficientClassification C) :
    Function.Injective (gammaGroundGammaToRVSemiring (hc := hc) (ground := C.base)) ∧
      Function.Injective (gammaGroundFiniteGammaToRESSemiring (hc := hc) (ground := C.base)) := by
  letI : CharZero (ModelResidue M) := rvResidueField_charZero C.model00
  exact ⟨gammaGroundGammaToRVSemiring_injective C.uncountable C.saturated C.model00 C.small_real C.small_gamma RY,
    gammaGroundFiniteGammaToRESSemiring_injective C.uncountable C.saturated C.model00 C.small_real C.small_gamma RY⟩

/-- Both homogeneous positive arrows retain their original degree. -/
theorem gammaGroundContext_coefficient_monomorphisms_degree
    (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (RY : GammaGroundCoefficientClassification C) (n : ℕ) :
    Function.Injective (gammaGroundGammaToRVKPlus (hc := hc) (ground := C.base) (k := n)) ∧
      Function.Injective (gammaGroundFiniteGammaToRESKPlus (hc := hc) (ground := C.base) (k := n)) := by
  letI : CharZero (ModelResidue M) := rvResidueField_charZero C.model00
  exact ⟨gammaGroundGammaToRVKPlus_injective C.uncountable C.saturated C.model00 C.small_real C.small_gamma (RY n),
    gammaGroundFiniteGammaToRESKPlus_injective C.uncountable C.saturated C.model00 C.small_real C.small_gamma (RY n)⟩

end DiamondIntegral.Section3
