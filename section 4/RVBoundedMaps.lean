import «section 4».RVBoundedGrading
import «section 4».RVChartMaps

/-! Actual bounded RV ring maps: inclusion into the full RV chart ring and
the measured RES inclusion, both preserving the proved gradings. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVBoundedMaps
open RVMeasuredCharts RVBoundedCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def forgetInvariant (B : Base (M := M)) : RVBoundedRing.Invariant B (RVChartRing.Ring B) where
  value _ a := RVChartRing.objectClass a.toChart
  unit := RVChartRing.objectClass_unit B
  product _ _ a b := RVChartRing.objectClass_product a.toChart b.toChart
  iso _ _ _ F := RVChartRing.objectClass_iso F
  empty _ a ha := RVChartRing.objectClass_empty a.toChart ha
  scissor _ a b c d h := RVChartRing.objectClass_scissor a.toChart b.toChart c.toChart d.toChart h

def forget (B : Base (M := M)) : RVBoundedRing.Ring B →+* RVChartRing.Ring B :=
  RVBoundedRing.lift B (forgetInvariant B)

theorem forget_class (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n) :
    forget B (RVBoundedRing.objectClass a) = RVChartRing.objectClass a.toChart :=
  RVBoundedRing.lift_objectClass B (forgetInvariant B) a

def resInvariant (B : Base (M := M)) : RESChartRing.Invariant B (RVBoundedRing.Ring B) where
  value _ a := RVBoundedRing.objectClass (RVBoundedCharts.ofRES a)
  unit := RVBoundedRing.objectClass_unit B
  product _ _ a b := RVBoundedRing.objectClass_product (RVBoundedCharts.ofRES a) (RVBoundedCharts.ofRES b)
  iso _ _ _ F := RVBoundedRing.objectClass_iso F
  empty _ a ha := RVBoundedRing.objectClass_empty (RVBoundedCharts.ofRES a) ha
  scissor _ a b c d h := RVBoundedRing.objectClass_scissor
    (RVBoundedCharts.ofRES a) (RVBoundedCharts.ofRES b) (RVBoundedCharts.ofRES c) (RVBoundedCharts.ofRES d) h

def ofRES (B : Base (M := M)) : RESChartRing.Ring B →+* RVBoundedRing.Ring B :=
  RESChartRing.lift B (resInvariant B)

theorem ofRES_class (B : Base (M := M)) {n : ℕ} (a : RESChart B n) :
    ofRES B (RESChartRing.objectClass a) = RVBoundedRing.objectClass (RVBoundedCharts.ofRES a) :=
  RESChartRing.lift_objectClass B (resInvariant B) a

theorem forget_ofRES (B : Base (M := M)) : (forget B).comp (ofRES B) = RVChartMaps.ofRES B := by
  apply RESRingCoaction.hom_ext B
  intro n a
  change forget B (ofRES B (RESChartRing.objectClass a)) = RVChartMaps.ofRES B (RESChartRing.objectClass a)
  rw [ofRES_class, forget_class, RVChartMaps.ofRES_class]
  rfl

theorem forget_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (forget B)).comp (RVBoundedGrading.coaction B) =
      (RVGrading.coaction B).comp (forget B) := by
  apply RVBoundedGrading.hom_ext B
  intro n a
  change (RVBoundedGrading.coaction B (RVBoundedRing.objectClass a)).map (forget B) =
    RVGrading.coaction B (forget B (RVBoundedRing.objectClass a))
  rw [RVBoundedGrading.coaction_class, Polynomial.map_monomial, forget_class, RVGrading.coaction_class]

theorem forget_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedRing.Ring B}
    (hx : x ∈ RVBoundedGrading.gradedPiece B n) : forget B x ∈ RVGrading.gradedPiece B n := by
  change RVBoundedGrading.coaction B x = Polynomial.monomial n x at hx
  change RVGrading.coaction B (forget B x) = Polynomial.monomial n (forget B x)
  have he : RVGrading.coaction B (forget B x) = (RVBoundedGrading.coaction B x).map (forget B) :=
    (RingHom.congr_fun (forget_coaction B) x).symm
  rw [he, hx, Polynomial.map_monomial]

theorem ofRES_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (ofRES B)).comp (RESRingCoaction.coaction B) =
      (RVBoundedGrading.coaction B).comp (ofRES B) := by
  apply RESRingCoaction.hom_ext B
  intro n a
  change (RESRingCoaction.coaction B (RESChartRing.objectClass a)).map (ofRES B) =
    RVBoundedGrading.coaction B (ofRES B (RESChartRing.objectClass a))
  rw [RESRingCoaction.coaction_class, Polynomial.map_monomial, ofRES_class, RVBoundedGrading.coaction_class]

theorem ofRES_mem (B : Base (M := M)) {n : ℕ} {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B n) : ofRES B x ∈ RVBoundedGrading.gradedPiece B n := by
  change RESRingCoaction.coaction B x = Polynomial.monomial n x at hx
  change RVBoundedGrading.coaction B (ofRES B x) = Polynomial.monomial n (ofRES B x)
  have he : RVBoundedGrading.coaction B (ofRES B x) = (RESRingCoaction.coaction B x).map (ofRES B) :=
    (RingHom.congr_fun (ofRES_coaction B) x).symm
  rw [he, hx, Polynomial.map_monomial]

end DiamondIntegral.Section4.RVBoundedMaps
