import «section 4».PointLocalizationEquivalence
import «section 4».RESDimensionFreeReduction
import «section 4».RESReductionGradings

/-! The actual dimension-free ordinary RES fibre quotient is the
degree-zero localization of the actual graded ordinary RES fibre
quotient at its degree-one point. A chart of degree k has the proved
fraction [U]/[1]^k. Finite-coproduct category identification is separate. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESPointLocalization
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem point_mem (B : Base (M := M)) :
    RESDimensionFreeReduction.pointClass B ∈ RESReductionGradings.ordinaryPiece B 1 :=
  RESReductionGradings.ordinary_class_mem B (RESFibreObjects.point B)

def Ring (B : Base (M := M)) := HomogeneousLocalization.Away
    (RESReductionGradings.ordinaryPiece B) (RESDimensionFreeReduction.pointClass B)
  deriving CommRing

def normalizedEquiv (B : Base (M := M)) : RESDimensionFreeReduction.Normalized B ≃+* Ring B :=
  PointLocalizationEquivalence.equiv (RESReductionGradings.ordinaryCoaction B)
    (RESDimensionFreeReduction.pointClass B) (point_mem B)

def dimensionFreeEquiv (B : Base (M := M)) : RESDimensionFreeReduction.Ring B ≃+* Ring B :=
  (RESDimensionFreeReduction.normalizationEquiv B).symm.trans (normalizedEquiv B)

def chartFraction (B : Base (M := M)) {k : ℕ} (a : RVMeasuredCharts.RESChart B k) : Ring B :=
  HomogeneousLocalization.Away.mk (RESReductionGradings.ordinaryPiece B) (point_mem B) k
    (RESOrdinaryReduction.quotient B (RESOrdinaryRing.objectClass a)) (by
      simpa only [smul_eq_mul, mul_one] using RESReductionGradings.ordinary_class_mem B a)

theorem dimensionFreeEquiv_object (B : Base (M := M)) {k : ℕ} (a : RVMeasuredCharts.RESChart B k) :
    dimensionFreeEquiv B (RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a)) = chartFraction B a := by
  let z : RESDimensionFreeReduction.Normalized B := Ideal.Quotient.mk (RESDimensionFreeReduction.pointIdeal B)
    (RESOrdinaryReduction.quotient B (RESOrdinaryRing.objectClass a))
  have hz : RESDimensionFreeReduction.normalizationEquiv B z =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) :=
    RESDimensionFreeReduction.normalizationEquiv_raw B (RESOrdinaryRing.objectClass a)
  have he : (RESDimensionFreeReduction.normalizationEquiv B).symm
      (RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a)) = z :=
    (congrArg (RESDimensionFreeReduction.normalizationEquiv B).symm hz).symm.trans
      ((RESDimensionFreeReduction.normalizationEquiv B).symm_apply_apply z)
  exact (congrArg (normalizedEquiv B) he).trans ((PointLocalizationEquivalence.equiv_mk (RESReductionGradings.ordinaryCoaction B)
    (RESDimensionFreeReduction.pointClass B) (point_mem B)
    (RESOrdinaryReduction.quotient B (RESOrdinaryRing.objectClass a))).trans
      (PointLocalizationNormalization.normalize_homogeneous (RESReductionGradings.ordinaryCoaction B)
        (RESDimensionFreeReduction.pointClass B) (point_mem B) (RESReductionGradings.ordinary_class_mem B a)))

theorem point_fraction_one (B : Base (M := M)) : chartFraction B (RESFibreObjects.point B) = 1 := by
  have he := PointLocalizationNormalization.normalize_homogeneous (RESReductionGradings.ordinaryCoaction B)
    (RESDimensionFreeReduction.pointClass B) (point_mem B) (point_mem B)
  exact he.symm.trans (PointLocalizationNormalization.normalize_point (RESReductionGradings.ordinaryCoaction B)
    (RESDimensionFreeReduction.pointClass B) (point_mem B))

end DiamondIntegral.Section4.RESPointLocalization
