import «section 3».RVUnitSpace
import «section 3».RVMonomialSyntax
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem rvIntegerMonomialRawMap_unitValues (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    rvIntegerMonomialRawMap A (rvUnitValues x) = rvUnitValues (integerMonomialMap A x) := by
  funext i
  have ht := rvIntegerMonomialTerm_realize (A i) (fun j => (x j : CanonicalRV.RVSort M))
  change (rvIntegerMonomialTerm (A i)).realize (rvUnitValues x) =
    (((∏ j, (x j) ^ A i j : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M)).val
  change (rvIntegerMonomialTerm (A i)).realize (rvUnitValues x) = (∏ j, (x j : CanonicalRV.RVSort M) ^ A i j).val at ht
  rw [ht]
  congr 1
  simp only [Units.coe_prod,Units.val_zpow_eq_zpow_val]
end DiamondIntegral.Section3
