import «section 3».GammaMeasuredElementaryObject

/-! The numerical Gamma weight of an elementary structural label is its
original weight times the new parameter value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section6
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {k : ℕ}

theorem gammaRadiusProduct_blowup (t : Fin k → CanonicalRV.RVSort M)
    (i : Fin k) (s : CanonicalRV.RVSort M) :
    (∏ j, Values.vrv (blowupValue i t s j)) = Values.vrv s * ∏ j, Values.vrv (t j) := by
  have hmem : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
  have he : ∏ j ∈ Finset.univ.erase i, Values.vrv (blowupValue i t s j) =
      ∏ j ∈ Finset.univ.erase i, Values.vrv (t j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [blowupValue_other i t s j (Finset.ne_of_mem_erase hj)]
  calc
    _ = Values.vrv (blowupValue i t s i) * ∏ j ∈ Finset.univ.erase i, Values.vrv (blowupValue i t s j) :=
      (Finset.mul_prod_erase _ _ hmem).symm
    _ = Values.vrv s * (Values.vrv (t i) * ∏ j ∈ Finset.univ.erase i, Values.vrv (t j)) := by
      rw [he,blowupValue_same,RVOperations.vrv_mul,mul_assoc]
    _ = _ := congrArg (Values.vrv s * ·)
      (Finset.mul_prod_erase Finset.univ (fun j => Values.vrv (t j)) hmem)

end DiamondIntegral.Section3
