import «section 4».RVZeroWeightedCount
import «section 4».ReductionDegreeZero
import «section 4».GammaUnboundedSpecialization
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! The actual definable-Gamma weight group ring embeds in degree-zero
measured RES, including after the measured fibre/affine quotient. Finite
weighted counts prove injectivity without an RV lift of a Gamma weight. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESWeightEmbedding
open GammaNamesSubgroup GammaDefinableEuler
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def nativeName (B : Base (M := M)) : Multiplicative (additiveNames B) →* Values.Gamma (M := M) where
  toFun a := toPaperGamma.symm (Multiplicative.toAdd a).val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem nativeName_injective (B : Base (M := M)) : Function.Injective (nativeName B) := by
  intro a b h
  have he : (Multiplicative.toAdd a).val = (Multiplicative.toAdd b).val := toPaperGamma.symm.injective h
  exact congrArg Multiplicative.ofAdd (Subtype.ext he)

def nativeMap (B : Base (M := M)) : DefinableGammaGroupRing B →+* RVFiniteWeightedCounts.Target M :=
  (MonoidAlgebra.mapDomainRingHom ℤ (nativeName B)).comp
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℤ ℤ (additiveNames B)).toRingHom

theorem nativeMap_single (B : Base (M := M)) (a : additiveNames B) (z : ℤ) :
    nativeMap B (AddMonoidAlgebra.single a z) = MonoidAlgebra.single (toPaperGamma.symm a.val) z := by
  change MonoidAlgebra.mapDomain (nativeName B)
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℤ ℤ (additiveNames B) (AddMonoidAlgebra.single a z)) = _
  rw [AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, MonoidAlgebra.mapDomain_single]
  rfl

theorem nativeMap_injective (B : Base (M := M)) : Function.Injective (nativeMap B) :=
  (MonoidAlgebra.mapDomain_injective (nativeName_injective B)).comp
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℤ ℤ (additiveNames B)).injective

def weightMap (B : Base (M := M)) : DefinableGammaGroupRing B →+* RESChartRing.Ring B :=
  GammaUnboundedSpecialization.weightCharacter B (RESWeightCharacter.weightCharacter B)

theorem weightMap_single (B : Base (M := M)) (a : additiveNames B) (z : ℤ) :
    weightMap B (AddMonoidAlgebra.single a z) =
      z • RESChartRing.objectClass (RVMeasuredCharts.weightedRESUnit B (toPaperGamma.symm a.val) a.property) :=
  GammaUnboundedSpecialization.weightCharacter_single B (RESWeightCharacter.weightCharacter B) a z

theorem count_weightMap (B : Base (M := M)) :
    (RVZeroWeightedCount.res B).comp (weightMap B) = nativeMap B := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro z
    exact RingHom.congr_fun (show ((RVZeroWeightedCount.res B).comp (weightMap B)).comp
      AddMonoidAlgebra.singleZeroRingHom = (nativeMap B).comp AddMonoidAlgebra.singleZeroRingHom from Subsingleton.elim _ _) z
  · intro a
    change RVZeroWeightedCount.res B (weightMap B (AddMonoidAlgebra.single a 1)) = _
    rw [weightMap_single, one_zsmul, nativeMap_single]
    exact RVZeroWeightedCount.res_weightedUnit B (toPaperGamma.symm a.val) a.property

theorem weightMap_injective (B : Base (M := M)) : Function.Injective (weightMap B) := by
  intro x y h
  apply nativeMap_injective B
  have he := congrArg (RVZeroWeightedCount.res B) h
  change ((RVZeroWeightedCount.res B).comp (weightMap B)) x = ((RVZeroWeightedCount.res B).comp (weightMap B)) y at he
  rwa [count_weightMap] at he

theorem weightMap_mem (B : Base (M := M)) (x : DefinableGammaGroupRing B) :
    weightMap B x ∈ RESRingCoaction.gradedPiece B 0 := by
  rw [show weightMap B x = x.coeff.sum (fun a z => z • RESWeightCharacter.weightCharacter B (Multiplicative.ofAdd a)) from
    AddMonoidAlgebra.lift_apply (RESWeightCharacter.weightCharacter B) x]
  unfold Finsupp.sum
  apply (RESRingCoaction.gradedPiece B 0).sum_mem
  intro a ha
  apply (RESRingCoaction.gradedPiece B 0).zsmul_mem
  exact RESRingCoaction.class_mem_gradedPiece B _

def reducedWeightMap (B : Base (M := M)) : DefinableGammaGroupRing B →+* RESMeasuredReduction.ReducedRing B :=
  (RESMeasuredReduction.quotient B).comp (weightMap B)

theorem reducedWeightMap_injective (B : Base (M := M)) : Function.Injective (reducedWeightMap B) := by
  intro x y h
  apply weightMap_injective B
  exact (RESGrading.gradingCoaction B).quotient_injective_on_zero (RESMeasuredReduction.reductionIdeal B)
    (ReductionDegreeZero.measured_ideal_le_zero_ker B) (weightMap_mem B x) (weightMap_mem B y) h

theorem reducedWeightMap_eq_character (B : Base (M := M)) : reducedWeightMap B =
    GammaUnboundedSpecialization.weightCharacter B (RESMeasuredReduction.weightCharacter B) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro z
    exact RingHom.congr_fun (show (reducedWeightMap B).comp AddMonoidAlgebra.singleZeroRingHom =
      (GammaUnboundedSpecialization.weightCharacter B (RESMeasuredReduction.weightCharacter B)).comp
        AddMonoidAlgebra.singleZeroRingHom from Subsingleton.elim _ _) z
  · intro a
    change RESMeasuredReduction.quotient B (weightMap B (AddMonoidAlgebra.single a 1)) = _
    rw [weightMap_single, one_zsmul, GammaUnboundedSpecialization.weightCharacter_single, one_zsmul]
    rfl

theorem reduced_character_injective (B : Base (M := M)) : Function.Injective
    (GammaUnboundedSpecialization.weightCharacter B (RESMeasuredReduction.weightCharacter B)) := by
  rw [← reducedWeightMap_eq_character]
  exact reducedWeightMap_injective B

theorem reduced_zero_ne_one (B : Base (M := M)) : (0 : RESMeasuredReduction.ReducedRing B) ≠ 1 := by
  intro h
  have he : reducedWeightMap B 0 = reducedWeightMap B 1 := by simpa only [map_zero, map_one] using h
  exact zero_ne_one (reducedWeightMap_injective B he)

def radiusWeightMap (B : Base (M := M)) : DefinableGammaGroupRing B →+* RVRadiusQuotient.Ring B :=
  (RVRadiusQuotient.ofRES B).comp (weightMap B)

theorem radiusWeightMap_injective (B : Base (M := M)) : Function.Injective (radiusWeightMap B) := by
  intro x y h
  have he : ReductionDegreeZero.radiusEquiv B ⟨weightMap B x, weightMap_mem B x⟩ =
      ReductionDegreeZero.radiusEquiv B ⟨weightMap B y, weightMap_mem B y⟩ := Subtype.ext h
  exact weightMap_injective B (congrArg Subtype.val ((ReductionDegreeZero.radiusEquiv B).injective he))

end DiamondIntegral.Section4.RESWeightEmbedding
