import «section 4».RVOrdinaryRing
import «section 4».RESOrdinaryUniversal
import «section 4».RVBoundedMaps

/-! Original-base ordinary RES inclusion and measured-to-ordinary RV
maps, with their actual forgetful square. No Euler descent is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryMaps
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def resInvariant (B : Base (M := M)) : RESOrdinaryRing.Invariant B (RVOrdinaryRing.Ring B) where
  value _ a := RVOrdinaryRing.objectClass a.toChart
  unit := RVOrdinaryRing.objectClass_unit B
  product _ _ a b := RVOrdinaryRing.objectClass_product a.toChart b.toChart
  iso _ _ _ F := RVOrdinaryRing.objectClass_iso F
  empty _ a ha := RVOrdinaryRing.objectClass_empty a.toChart ha
  scissor _ a b c d h := RVOrdinaryRing.objectClass_scissor a.toChart b.toChart c.toChart d.toChart h

def ofRES (B : Base (M := M)) : RESOrdinaryRing.Ring B →+* RVOrdinaryRing.Ring B :=
  RESOrdinaryRing.lift B (resInvariant B)

theorem ofRES_class (B : Base (M := M)) {n : ℕ} (a : RESChart B n) :
    ofRES B (RESOrdinaryRing.objectClass a) = RVOrdinaryRing.objectClass a.toChart :=
  RESOrdinaryRing.lift_objectClass B (resInvariant B) a

theorem forget_ofRES (B : Base (M := M)) :
    (RVOrdinaryRing.forget B).comp (RVChartMaps.ofRES B) =
      (ofRES B).comp (RESOrdinaryRing.forget B) := by
  apply RESRingCoaction.hom_ext B
  intro n a
  change RVOrdinaryRing.forget B (RVChartMaps.ofRES B (RESChartRing.objectClass a)) =
    ofRES B (RESOrdinaryRing.forget B (RESChartRing.objectClass a))
  rw [RVChartMaps.ofRES_class, RVOrdinaryRing.forget_objectClass,
    RESOrdinaryRing.forget_objectClass, ofRES_class]

def boundedForget (B : Base (M := M)) : RVBoundedRing.Ring B →+* RVOrdinaryRing.Ring B :=
  (RVOrdinaryRing.forget B).comp (RVBoundedMaps.forget B)

theorem boundedForget_class (B : Base (M := M)) {n : ℕ} (a : RVBoundedCharts.BoundedChart B n) :
    boundedForget B (RVBoundedRing.objectClass a) = RVOrdinaryRing.objectClass a.toChart := by
  change RVOrdinaryRing.forget B (RVBoundedMaps.forget B (RVBoundedRing.objectClass a)) = _
  rw [RVBoundedMaps.forget_class, RVOrdinaryRing.forget_objectClass]

theorem boundedForget_ofRES (B : Base (M := M)) :
    (boundedForget B).comp (RVBoundedMaps.ofRES B) =
      (ofRES B).comp (RESOrdinaryRing.forget B) := by
  rw [boundedForget, RingHom.comp_assoc, RVBoundedMaps.forget_ofRES, forget_ofRES]

end DiamondIntegral.Section4.RVOrdinaryMaps
