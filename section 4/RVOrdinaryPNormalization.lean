import «section 4».RVOrdinaryRadius

/-! The actual ordinary RV quotient P=1 and its natural map from the
bounded measured radius quotient. This quotient mixes degrees; no graded
structure on it or comparison from the measured P=0 quotient is asserted. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryPNormalization
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pClass (B : Base (M := M)) : RVOrdinaryRing.Ring B :=
  RVOrdinaryRing.objectClass (RESFibreObjects.point B).toChart -
    RVOrdinaryRing.objectClass (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B))

theorem forget_pClass (B : Base (M := M)) :
    RVOrdinaryRing.forget B (RVMeasuredSpecialClasses.pClass B) = pClass B := by
  unfold RVMeasuredSpecialClasses.pClass pClass
  rw [map_sub, RVOrdinaryRing.forget_objectClass, RVOrdinaryRing.forget_objectClass]

def pIdeal (B : Base (M := M)) : Ideal (RVOrdinaryRing.Ring B) := Ideal.span {pClass B - 1}

def Ring (B : Base (M := M)) := RVOrdinaryRing.Ring B ⧸ pIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RVOrdinaryRing.Ring B →+* Ring B := Ideal.Quotient.mk (pIdeal B)

theorem p_one (B : Base (M := M)) : quotient B (pClass B) = 1 := by
  have h : quotient B (pClass B - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

def forget (B : Base (M := M)) : RVRadiusQuotient.Ring B →+* Ring B :=
  (quotient B).comp (RVOrdinaryRadius.forget B)

theorem forget_quotient (B : Base (M := M)) (x : RVBoundedRing.Ring B) :
    forget B (RVRadiusQuotient.quotient B x) =
      quotient B (RVOrdinaryMaps.boundedForget B x) := rfl

def ofRES (B : Base (M := M)) : RESOrdinaryRing.Ring B →+* Ring B :=
  (quotient B).comp (RVOrdinaryMaps.ofRES B)

theorem forget_ofRES (B : Base (M := M)) :
    (forget B).comp (RVRadiusQuotient.ofRES B) =
      (ofRES B).comp (RESOrdinaryRing.forget B) := by
  rw [forget, RingHom.comp_assoc, RVOrdinaryRadius.forget_ofRES]
  rfl

end DiamondIntegral.Section4.RVOrdinaryPNormalization
