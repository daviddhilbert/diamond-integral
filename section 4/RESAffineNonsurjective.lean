import «section 4».RESHomogeneousGrowth
import «section 4».FieldGrowthSeparation
import «section 4».RESAffineSeparation
import Section4.EarlierRVInputs

/-! Remark 4.4: the affine line is outside the image of the natural
homogeneous-to-ungraded affine-localization comparison. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RESAffineNonsurjective
open RESAffineLocalization RESOrdinaryResidueTrace RESAffineSeparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
  [Infinite (ModelResidue M)] [IsAlgClosed (ModelResidue M)] [CharZero (ModelResidue M)]
  {κ : Cardinal} (hs : Saturated M κ) (B : Base (M := M))
  (hsmall : Cardinal.mk (commonRealNames B) < κ)

include hc hex hs hsmall

theorem affine_not_mem_range :
    algebraMap (RESDimensionFreeReduction.Ring B) (Target B) (dimensionFreeAffine B) ∉
      Set.range (comparison B) := by
  rintro ⟨z, hz⟩
  obtain ⟨n, x, hx, he⟩ := HomogeneousLocalization.Away.mk_surjective
    (RESReductionGradings.ordinaryPiece B) (affine_mem B) z
  have hx' : x ∈ RESReductionGradings.ordinaryPiece B n := by
    simpa only [smul_eq_mul, mul_one] using hx
  have hze : fraction B n x hx' = z := he
  rw [← hze] at hz
  have hspec : comparison B (fraction B n x hx') *
      algebraMap (RESDimensionFreeReduction.Ring B) (Target B) (dimensionFreeAffine B ^ n) =
        algebraMap (RESDimensionFreeReduction.Ring B) (Target B)
          (RESDimensionFreeReduction.fromGradedReduced B x) := by
    rw [comparison_fraction, Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_spec (Target B)
      (RESDimensionFreeReduction.fromGradedReduced B x)
      (⟨dimensionFreeAffine B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (dimensionFreeAffine B))
  have hpower : algebraMap (RESDimensionFreeReduction.Ring B) (Target B)
      (dimensionFreeAffine B ^ (n + 1)) =
      algebraMap (RESDimensionFreeReduction.Ring B) (Target B)
        (RESDimensionFreeReduction.fromGradedReduced B x) := by
    rw [hz, ← map_mul] at hspec
    simpa only [pow_succ, mul_comm (dimensionFreeAffine B)] using hspec
  have hzero : algebraMap (RESDimensionFreeReduction.Ring B) (Target B)
      (RESDimensionFreeReduction.fromGradedReduced B x - dimensionFreeAffine B ^ (n + 1)) = 0 := by
    rw [map_sub, hpower, sub_self]
  have hfield := congrArg (localizationTrace hc B) hzero
  rw [localizationTrace_algebraMap, map_zero] at hfield
  change algebraMap (FieldDefinableRing.Ring (ModelResidue M)) (FieldTarget (M := M))
    (dimensionFreeTrace hc B (RESDimensionFreeReduction.fromGradedReduced B x -
      dimensionFreeAffine B ^ (n + 1))) = 0 at hfield
  rw [map_sub, dimensionFreeTrace_fromGraded, map_pow, dimensionFreeTrace_affine] at hfield
  obtain ⟨s, hs'⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (FieldDefinableRing.affineClass (ModelResidue M)))
    (FieldTarget (M := M)) _).mp hfield
  obtain ⟨m, hm⟩ := s.property
  have hg := RESHomogeneousGrowth.reduced_mem hc hex hs B hsmall hx'
  exact FieldGrowthSeparation.affine_power_separated (ModelResidue M) hg m
    (by simpa only [← hm] using hs')

theorem not_surjective : ¬ Function.Surjective (comparison B) := by
  intro h
  exact affine_not_mem_range hc hex hs B hsmall
    (h (algebraMap (RESDimensionFreeReduction.Ring B) (Target B) (dimensionFreeAffine B)))

omit hex hsmall [Infinite (ModelResidue M)] [IsAlgClosed (ModelResidue M)] [CharZero (ModelResidue M)] in
theorem remark_4_4 (h00 : M ⊨ Axioms.ACVF00) (hκ : Cardinal.aleph0 ≤ κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) :
    ¬ Function.Surjective (comparison B) := by
  letI : IsAlgClosed (SpecialTransformations.Milestone0.Transfer.VFType (M := M)) :=
    VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  letI : CharZero (ModelResidue M) := SpecialTransformations.Section7.residueField_charZero_of_model00
    Values.presentationValuation Values.presentation_compatible h00
  exact not_surjective hc (rvExchangeInput_of_earlier hκ hs h00) hs B
    (commonRealNames_small hκ B hr hγ)

end DiamondIntegral.Section4.RESAffineNonsurjective
