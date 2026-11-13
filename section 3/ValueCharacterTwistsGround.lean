import «section 3».ValueCharacterTwistsResidue
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M))
variable (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)

/-- Every old-ground RV point, including zero, is fixed. -/
theorem rvOriginalGroundCharacterTwistZero_fixes_ground
    (u : CanonicalRV.RVSort M) (hu : DefinableClosureAtBase B .rv u.val) :
    rvOriginalGroundCharacterTwistZero B χ u = u := by
  by_cases hz : u = 0
  · subst u
    exact rvOriginalGroundCharacterTwistZero_zero B χ
  · let t := Units.mk0 u hz
    change rvOriginalGroundCharacterTwistZero B χ (t : CanonicalRV.RVSort M) = _
    rw [rvOriginalGroundCharacterTwistZero_coe,rvOriginalGroundCharacterTwist_fixes_ground B χ t hu]
    rfl

/-- Applying rv to any old-ground definable VF point produces a fixed
RV point; this handles the only VF-to-RV language symbol. -/
theorem rvOriginalGroundCharacterTwistZero_rv
    (a : VFType (M := M)) (ha : DefinableClosureAtBase B .vf a.val) :
    rvOriginalGroundCharacterTwistZero B χ (CanonicalRV.encodedRv a) = CanonicalRV.encodedRv a := by
  apply rvOriginalGroundCharacterTwistZero_fixes_ground
  exact definableClosureAtBase_function_symbol B Fn.rvMap ![a.val]
    (by intro i; fin_cases i; exact a.property)
    (by intro i; fin_cases i; exact ha)

theorem rvOriginalGroundCharacterTwistZero_le (u v : CanonicalRV.RVSort M) :
    iLe (rvOriginalGroundCharacterTwistZero B χ u).val (rvOriginalGroundCharacterTwistZero B χ v).val ↔
      iLe u.val v.val := by
  rw [← Values.vrv_le_iff,← Values.vrv_le_iff,
    rvOriginalGroundCharacterTwistZero_value,rvOriginalGroundCharacterTwistZero_value]

theorem rvOriginalGroundCharacterTwistZero_units (u : CanonicalRV.RVSort M) :
    iUnits (rvOriginalGroundCharacterTwistZero B χ u).val ↔ iUnits u.val := by
  by_cases hu : u = 0
  · subst u
    rw [rvOriginalGroundCharacterTwistZero_zero]
  · have he : rvOriginalGroundCharacterTwistZero B χ u ≠ 0 := by
      intro hh
      apply hu
      exact (rvOriginalGroundCharacterTwistZero B χ).injective
        (hh.trans (rvOriginalGroundCharacterTwistZero_zero B χ).symm)
    rw [RVOperations.units_iff_absolute_one _ he,RVOperations.units_iff_absolute_one _ hu]
    change Values.valueEquiv Values.presentationValuation Values.presentation_compatible
      (Values.vrv (rvOriginalGroundCharacterTwistZero B χ u)) = 1 ↔ _
    rw [rvOriginalGroundCharacterTwistZero_value]
    rfl

end DiamondIntegral.Section3
