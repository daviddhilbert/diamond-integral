import «section 4».GammaIntegerFamilies

/-! Actual characteristic functions in every finite Gamma arity, including
their scissor identity in the original-base additive function group. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaIndicators
open GammaOrderLogic GammaFamilyIntegration GammaIntegerFamilies

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem indicator_definable (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin n → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    IntegerFamilyDefinable B (fun z => if z ∈ R then (1 : ℤ) else 0) := by
  refine ⟨(Set.toFinite ({0, 1} : Set ℤ)).subset ?_, ?_⟩
  · rintro m ⟨z, rfl⟩
    by_cases hz : z ∈ R <;> simp [hz]
  · intro m
    by_cases hm1 : m = 1
    · subst m
      convert hR using 1
      ext z
      by_cases hz : z ∈ R <;> simp [hz]
    · by_cases hm0 : m = 0
      · subst m
        convert GammaRelationLogic.complement_definable_base B R hR using 1
        ext z
        by_cases hz : z ∈ R <;> simp [hz]
      · convert empty_definable_base B n using 1
        ext z
        by_cases hz : z ∈ R <;> simp [hz, Ne.symm hm1, Ne.symm hm0]

def indicatorFamily (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin n → Values.Gamma (M := M))) (hR : GammaDefinable B R) : familySubgroup B n :=
  ⟨(fun z => if z ∈ R then 1 else 0), indicator_definable B R hR⟩

theorem indicator_scissor (B : Base (M := M)) {n : ℕ}
    (R S : Set (Fin n → Values.Gamma (M := M))) (hR : GammaDefinable B R) (hS : GammaDefinable B S)
    (hU : GammaDefinable B (R ∪ S)) (hI : GammaDefinable B (R ∩ S)) :
    indicatorFamily B (R ∪ S) hU + indicatorFamily B (R ∩ S) hI =
      indicatorFamily B R hR + indicatorFamily B S hS := by
  apply Subtype.ext
  funext z
  simp only [AddSubgroup.coe_add, Pi.add_apply, indicatorFamily]
  by_cases hr : z ∈ R <;> by_cases hs : z ∈ S <;> simp [hr, hs]

end DiamondIntegral.Section4.GammaIndicators
