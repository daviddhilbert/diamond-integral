import «section 4».RVMeasuredPQuotient
import «section 4».RESWeightEmbedding

/-! The measured P quotient preserves every degree-zero coefficient.
Its bounded-radius comparison is an isomorphism on the entire zero-degree
subrings. This does not establish nonvanishing of the degree-one point. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVMeasuredPDegreeZero
open RVMeasuredPQuotient
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem ideal_le_zero_ker (B : Base (M := M)) :
    pIdeal B ≤ RingHom.ker (RVGrading.gradingCoaction B).zeroProjection := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x = RVMeasuredSpecialClasses.pClass B := hx
  subst x
  exact (RVGrading.gradingCoaction B).zeroProjection_of_positive_mem (by decide : (1 : ℕ) ≠ 0)
    (RVMeasuredSpecialClasses.pClass_mem B)

def zeroEquiv (B : Base (M := M)) :
    RVZeroDegreeEquivalences.resZero B ≃+* (coaction B).zeroSubring :=
  (RVZeroDegreeEquivalences.fullEquiv B).trans
    ((RVGrading.gradingCoaction B).quotientZeroEquiv (pIdeal B)
      (ideal_coefficients B) (ideal_le_zero_ker B))

theorem zeroEquiv_apply (B : Base (M := M)) (x : RVZeroDegreeEquivalences.resZero B) :
    (zeroEquiv B x).val = ofRES B x.val := rfl

theorem ofRES_injective_on_degree_zero (B : Base (M := M)) :
    Set.InjOn (ofRES B) (RESRingCoaction.gradedPiece B 0) := by
  intro x hx y hy h
  have hs : zeroEquiv B ⟨x, hx⟩ = zeroEquiv B ⟨y, hy⟩ := Subtype.ext h
  exact congrArg Subtype.val ((zeroEquiv B).injective hs)

def radiusZeroEquiv (B : Base (M := M)) :
    (RVRadiusQuotient.coaction B).zeroSubring ≃+* (coaction B).zeroSubring :=
  (ReductionDegreeZero.radiusEquiv B).symm.trans (zeroEquiv B)

theorem radiusZeroEquiv_apply (B : Base (M := M)) (x : (RVRadiusQuotient.coaction B).zeroSubring) :
    (radiusZeroEquiv B x).val = forget B x.val := by
  obtain ⟨r, rfl⟩ := (ReductionDegreeZero.radiusEquiv B).surjective x
  rw [radiusZeroEquiv, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  change ofRES B r.val = forget B (RVRadiusQuotient.ofRES B r.val)
  exact (RingHom.congr_fun (forget_ofRES B) r.val).symm

def weightMap (B : Base (M := M)) : GammaNamesSubgroup.DefinableGammaGroupRing B →+* Ring B :=
  (ofRES B).comp (RESWeightEmbedding.weightMap B)

theorem weightMap_injective (B : Base (M := M)) : Function.Injective (weightMap B) := by
  intro x y h
  exact RESWeightEmbedding.weightMap_injective B
    (ofRES_injective_on_degree_zero B (RESWeightEmbedding.weightMap_mem B x) (RESWeightEmbedding.weightMap_mem B y) h)

theorem zero_ne_one (B : Base (M := M)) : (0 : Ring B) ≠ 1 := by
  intro h
  have he : weightMap B 0 = weightMap B 1 := by simpa only [map_zero, map_one] using h
  exact _root_.zero_ne_one (weightMap_injective B he)

end DiamondIntegral.Section4.RVMeasuredPDegreeZero
