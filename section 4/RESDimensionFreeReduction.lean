import «section 4».RESDimensionFreeRing
import «section 4».RESOrdinaryReduction

/-! Forgetting degree commutes with the actual ordinary value-fibre
quotient. Its source after fibre reduction is quotiented exactly by the
degree-one point minus one. The affine-line class is retained. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESDimensionFreeReduction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def fibreIdeal (B : Base (M := M)) : Ideal (RESDimensionFreeRing.Ring B) :=
  Ideal.map (RESDimensionFreeRing.quotient B) (RESOrdinaryReduction.fibreIdeal B)

def Ring (B : Base (M := M)) := RESDimensionFreeRing.Ring B ⧸ fibreIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RESDimensionFreeRing.Ring B →+* Ring B := Ideal.Quotient.mk (fibreIdeal B)

def fromOrdinary (B : Base (M := M)) : RESOrdinaryRing.Ring B →+* Ring B :=
  (quotient B).comp (RESDimensionFreeRing.quotient B)

theorem kernel_fromOrdinary (B : Base (M := M)) :
    RingHom.ker (fromOrdinary B) = RESDimensionFreeRing.degreeIdeal B ⊔ RESOrdinaryReduction.fibreIdeal B :=
  DoubleQuot.ker_quotQuotMk _ _

def pointClass (B : Base (M := M)) : RESOrdinaryReduction.ReducedRing B :=
  RESOrdinaryReduction.quotient B (RESOrdinaryRing.objectClass (RESFibreObjects.point B))

def pointIdeal (B : Base (M := M)) : Ideal (RESOrdinaryReduction.ReducedRing B) :=
  Ideal.span {pointClass B - 1}

theorem degreeImage_eq_pointIdeal (B : Base (M := M)) :
    Ideal.map (RESOrdinaryReduction.quotient B) (RESDimensionFreeRing.degreeIdeal B) = pointIdeal B := by
  rw [RESDimensionFreeRing.degreeIdeal_eq_pointIdeal, RESDimensionFreeRing.pointIdeal_eq_manuscript,
    Ideal.map_span, Set.image_singleton, map_sub, map_one]
  rfl

def Normalized (B : Base (M := M)) := RESOrdinaryReduction.ReducedRing B ⧸ pointIdeal B
  deriving CommRing

def normalizationEquiv (B : Base (M := M)) : Normalized B ≃+* Ring B :=
  (Ideal.quotEquivOfEq (degreeImage_eq_pointIdeal B).symm).trans
    (DoubleQuot.quotQuotEquivComm (RESOrdinaryReduction.fibreIdeal B) (RESDimensionFreeRing.degreeIdeal B))

theorem normalizationEquiv_raw (B : Base (M := M)) (x : RESOrdinaryRing.Ring B) :
    normalizationEquiv B (Ideal.Quotient.mk (pointIdeal B) (RESOrdinaryReduction.quotient B x)) = fromOrdinary B x := rfl

def fromGradedReduced (B : Base (M := M)) : RESOrdinaryReduction.ReducedRing B →+* Ring B :=
  (normalizationEquiv B).toRingHom.comp (Ideal.Quotient.mk (pointIdeal B))

theorem fromGradedReduced_raw (B : Base (M := M)) (x : RESOrdinaryRing.Ring B) :
    fromGradedReduced B (RESOrdinaryReduction.quotient B x) = fromOrdinary B x := rfl

theorem kernel_fromGradedReduced (B : Base (M := M)) : RingHom.ker (fromGradedReduced B) = pointIdeal B := by
  ext x
  change normalizationEquiv B (Ideal.Quotient.mk (pointIdeal B) x) = 0 ↔ x ∈ pointIdeal B
  constructor
  · intro hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((normalizationEquiv B).injective (hx.trans (map_zero (normalizationEquiv B)).symm))
  · intro hx
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact map_zero (normalizationEquiv B)

end DiamondIntegral.Section4.RESDimensionFreeReduction
