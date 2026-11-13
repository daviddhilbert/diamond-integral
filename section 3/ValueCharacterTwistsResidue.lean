import «section 3».ValueCharacterTwistsWithZero
import Section4.ResidueScaledFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M))
variable (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)

@[simp] theorem rvOriginalGroundCharacterTwistZero_zero :
    rvOriginalGroundCharacterTwistZero B χ 0 = 0 := map_zero _

/-- All residue-field points are fixed, not only old-ground points. -/
theorem rvOriginalGroundCharacterTwistZero_residue (x : ModelResidue M) :
    rvOriginalGroundCharacterTwistZero B χ (residueRV x) = residueRV x := by
  by_cases hx : x = 0
  · simp [hx]
  · let u := residueUnitToRV (Units.mk0 x hx)
    have hu : (u : CanonicalRV.RVSort M) = residueRV x := rfl
    rw [← hu,rvOriginalGroundCharacterTwistZero_coe]
    apply congrArg Units.val
    apply valueCharacterTwistEquiv_fixed
    have hv : rvUnitValueHom u = 1 := residueUnitToRV_value_one _
    change χ (QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom u)) = 1
    rw [hv,map_one,map_one]

/-- The total residue predicate is invariant under the character twist. -/
theorem rvOriginalGroundCharacterTwistZero_inK (u : CanonicalRV.RVSort M) :
    ValuedModelMap.inK (rvOriginalGroundCharacterTwistZero B χ u) ↔ ValuedModelMap.inK u := by
  rw [RVOperations.inK_iff,RVOperations.inK_iff]
  have hv : RVOperations.absoluteHom (rvOriginalGroundCharacterTwistZero B χ u) =
      RVOperations.absoluteHom u :=
    congrArg (Values.valueEquiv Values.presentationValuation Values.presentation_compatible)
      (rvOriginalGroundCharacterTwistZero_value B χ u)
  rw [hv]
  have hz : rvOriginalGroundCharacterTwistZero B χ u = 0 ↔ u = 0 := by
    constructor
    · intro he
      exact (rvOriginalGroundCharacterTwistZero B χ).injective
        (he.trans (rvOriginalGroundCharacterTwistZero_zero B χ).symm)
    · rintro rfl
      exact rvOriginalGroundCharacterTwistZero_zero B χ
  rw [hz]

/-- The named total residue addition, including its junk branch, is
preserved by the actual original-ground character twist. -/
theorem rvOriginalGroundCharacterTwistZero_addK (u v : CanonicalRV.RVSort M) :
    rvOriginalGroundCharacterTwistZero B χ (ValuedModelMap.addK u v) =
      ValuedModelMap.addK (rvOriginalGroundCharacterTwistZero B χ u)
        (rvOriginalGroundCharacterTwistZero B χ v) := by
  by_cases h : ValuedModelMap.inK u ∧ ValuedModelMap.inK v
  · obtain ⟨x,rfl⟩ := exists_residueRV h.1
    obtain ⟨y,rfl⟩ := exists_residueRV h.2
    rw [← residueRV_add,rvOriginalGroundCharacterTwistZero_residue,
      rvOriginalGroundCharacterTwistZero_residue,rvOriginalGroundCharacterTwistZero_residue,
      residueRV_add]
  · have h' : ¬ (ValuedModelMap.inK (rvOriginalGroundCharacterTwistZero B χ u) ∧
        ValuedModelMap.inK (rvOriginalGroundCharacterTwistZero B χ v)) := by
      simpa only [rvOriginalGroundCharacterTwistZero_inK] using h
    rw [ValuedModelMap.addK_junk _ _ (not_and_or.mp h),ValuedModelMap.addK_junk _ _ (not_and_or.mp h'),
      RVOperations.zeroRV_eq,rvOriginalGroundCharacterTwistZero_zero]

theorem rvOriginalGroundCharacterTwistZero_negK (u : CanonicalRV.RVSort M) :
    rvOriginalGroundCharacterTwistZero B χ (ValuedModelMap.negK u) =
      ValuedModelMap.negK (rvOriginalGroundCharacterTwistZero B χ u) := by
  by_cases h : ValuedModelMap.inK u
  · obtain ⟨x,rfl⟩ := exists_residueRV h
    rw [← residueRV_neg,rvOriginalGroundCharacterTwistZero_residue,
      rvOriginalGroundCharacterTwistZero_residue,residueRV_neg]
  · have h' : ¬ ValuedModelMap.inK (rvOriginalGroundCharacterTwistZero B χ u) :=
      fun hi => h ((rvOriginalGroundCharacterTwistZero_inK B χ u).mp hi)
    rw [ValuedModelMap.negK_junk _ h,ValuedModelMap.negK_junk _ h',
      RVOperations.zeroRV_eq,rvOriginalGroundCharacterTwistZero_zero]

end DiamondIntegral.Section3
