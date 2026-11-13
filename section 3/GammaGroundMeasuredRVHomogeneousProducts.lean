import «section 3».GammaGroundMeasuredRVIsomorphismClasses
import «section 3».GammaGroundMeasuredRVProductMorphisms
import «section 3».GammaGroundMeasuredRVSemiring

/-! Actual homogeneous products on the fixed-degree positive RV
scissors, independent of the choice of object representatives. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundMeasuredRVRepresentative (a : GammaGroundMeasuredRVKPlus hc ground k) : GammaGroundMeasuredRVObject hc ground k :=
  Classical.choose (gammaGroundMeasuredRVClass_surjective a)

@[simp] theorem gammaGroundMeasuredRVRepresentative_class (a : GammaGroundMeasuredRVKPlus hc ground k) :
    gammaGroundMeasuredRVClass (gammaGroundMeasuredRVRepresentative a) = a := Classical.choose_spec (gammaGroundMeasuredRVClass_surjective a)

def gammaGroundMeasuredRVClassMul (a : GammaGroundMeasuredRVKPlus hc ground k) (b : GammaGroundMeasuredRVKPlus hc ground l) :
    GammaGroundMeasuredRVKPlus hc ground (k + l) := gammaGroundMeasuredRVClass ((gammaGroundMeasuredRVRepresentative a).product (gammaGroundMeasuredRVRepresentative b))

@[simp] theorem gammaGroundMeasuredRVClassMul_class (U : GammaGroundMeasuredRVObject hc ground k) (V : GammaGroundMeasuredRVObject hc ground l) :
    gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRVClass U) (gammaGroundMeasuredRVClass V) = gammaGroundMeasuredRVClass (U.product V) := by
  obtain ⟨e⟩ := gammaGroundMeasuredRVClass_eq_iff_iso.mp (gammaGroundMeasuredRVRepresentative_class (gammaGroundMeasuredRVClass U))
  obtain ⟨f⟩ := gammaGroundMeasuredRVClass_eq_iff_iso.mp (gammaGroundMeasuredRVRepresentative_class (gammaGroundMeasuredRVClass V))
  exact gammaGroundMeasuredRVClass_iso (gammaGroundMeasuredRVProductIso e f)

theorem gammaGroundMeasuredRVKPlusToSemiring_mul (a : GammaGroundMeasuredRVKPlus hc ground k) (b : GammaGroundMeasuredRVKPlus hc ground l) :
    gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClassMul a b) =
      gammaGroundMeasuredRVKPlusToSemiring a * gammaGroundMeasuredRVKPlusToSemiring b := by
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredRVClass_surjective b
  rw [gammaGroundMeasuredRVClassMul_class, gammaGroundMeasuredRVKPlusToSemiring_class,
    gammaGroundMeasuredRVKPlusToSemiring_class, gammaGroundMeasuredRVKPlusToSemiring_class, gammaGroundMeasuredRVSemiringClass_product]

end DiamondIntegral.Section3
