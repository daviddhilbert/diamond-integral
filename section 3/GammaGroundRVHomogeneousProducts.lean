import «section 3».GammaGroundRVIsomorphismClasses
import «section 3».GammaGroundRVProductMorphisms
import «section 3».GammaGroundRVSemiring

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

def gammaGroundRVRepresentative (a : GammaGroundRVKPlus hc ground k) : GammaGroundRVObject hc ground k :=
  Classical.choose (gammaGroundRVClass_surjective a)

@[simp] theorem gammaGroundRVRepresentative_class (a : GammaGroundRVKPlus hc ground k) :
    gammaGroundRVClass (gammaGroundRVRepresentative a) = a := Classical.choose_spec (gammaGroundRVClass_surjective a)

def gammaGroundRVClassMul (a : GammaGroundRVKPlus hc ground k) (b : GammaGroundRVKPlus hc ground l) :
    GammaGroundRVKPlus hc ground (k + l) := gammaGroundRVClass ((gammaGroundRVRepresentative a).product (gammaGroundRVRepresentative b))

@[simp] theorem gammaGroundRVClassMul_class (U : GammaGroundRVObject hc ground k) (V : GammaGroundRVObject hc ground l) :
    gammaGroundRVClassMul (gammaGroundRVClass U) (gammaGroundRVClass V) = gammaGroundRVClass (U.product V) := by
  obtain ⟨e⟩ := gammaGroundRVClass_eq_iff_iso.mp (gammaGroundRVRepresentative_class (gammaGroundRVClass U))
  obtain ⟨f⟩ := gammaGroundRVClass_eq_iff_iso.mp (gammaGroundRVRepresentative_class (gammaGroundRVClass V))
  exact gammaGroundRVClass_iso (gammaGroundRVProductIso e f)

theorem gammaGroundRVKPlusToSemiring_mul (a : GammaGroundRVKPlus hc ground k) (b : GammaGroundRVKPlus hc ground l) :
    gammaGroundRVKPlusToSemiring (gammaGroundRVClassMul a b) =
      gammaGroundRVKPlusToSemiring a * gammaGroundRVKPlusToSemiring b := by
  obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundRVClass_surjective b
  rw [gammaGroundRVClassMul_class, gammaGroundRVKPlusToSemiring_class,
    gammaGroundRVKPlusToSemiring_class, gammaGroundRVKPlusToSemiring_class, gammaGroundRVSemiringClass_product]

end DiamondIntegral.Section3
