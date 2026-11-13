import «section 4».RVGrading
import «section 4».RESGrading

/-! The fixed-degree RV scissors groups and the measured RES chart ring
map to the actual graded RV chart ring. Injectivity or identification with
the finite-coproduct manuscript categories is not assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVChartMaps
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def fixedDegreeInvariant (B : Base (M := M)) (n : ℕ) :
    RVMeasuredGroup.Invariant B n (RVChartRing.Ring B) where
  value := RVChartRing.objectClass
  iso _ _ F := RVChartRing.objectClass_iso F
  empty a ha := RVChartRing.objectClass_empty a ha
  scissor a b c d h := RVChartRing.objectClass_scissor a b c d h

def fixedDegreeMap (B : Base (M := M)) (n : ℕ) :
    RVMeasuredGroup.KGroup B n →+ RVChartRing.Ring B :=
  RVMeasuredGroup.lift B n (fixedDegreeInvariant B n)

theorem fixedDegreeMap_class (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    fixedDegreeMap B n (RVMeasuredGroup.objectClass a) = RVChartRing.objectClass a :=
  RVMeasuredGroup.lift_objectClass B n (fixedDegreeInvariant B n) a

def fixedDegreeGradedInvariant (B : Base (M := M)) (n : ℕ) :
    RVMeasuredGroup.Invariant B n (RVGrading.gradedPiece B n) where
  value a := ⟨RVChartRing.objectClass a, RVGrading.class_mem B a⟩
  iso _ _ F := Subtype.ext (RVChartRing.objectClass_iso F)
  empty a ha := Subtype.ext (RVChartRing.objectClass_empty a ha)
  scissor a b c d h := Subtype.ext (RVChartRing.objectClass_scissor a b c d h)

theorem fixedDegreeMap_mem (B : Base (M := M)) (n : ℕ) (x : RVMeasuredGroup.KGroup B n) :
    fixedDegreeMap B n x ∈ RVGrading.gradedPiece B n := by
  let f := RVMeasuredGroup.lift B n (fixedDegreeGradedInvariant B n)
  have hf : (RVGrading.gradedPiece B n).subtype.comp f = fixedDegreeMap B n := by
    apply RVMeasuredGroup.hom_ext B n
    intro a
    rw [fixedDegreeMap_class]
    change ((f (RVMeasuredGroup.objectClass a) : RVGrading.gradedPiece B n) : RVChartRing.Ring B) = RVChartRing.objectClass a
    exact congrArg Subtype.val (RVMeasuredGroup.lift_objectClass B n (fixedDegreeGradedInvariant B n) a)
  rw [← hf]
  exact (f x).property

def resInvariant (B : Base (M := M)) : RESChartRing.Invariant B (RVChartRing.Ring B) where
  value _ a := RVChartRing.objectClass a.toChart
  unit := RVChartRing.objectClass_unit B
  product _ _ a b := RVChartRing.objectClass_product a.toChart b.toChart
  iso _ _ _ F := RVChartRing.objectClass_iso F
  empty _ a ha := RVChartRing.objectClass_empty a.toChart ha
  scissor _ a b c d h := RVChartRing.objectClass_scissor a.toChart b.toChart c.toChart d.toChart h

def ofRES (B : Base (M := M)) : RESChartRing.Ring B →+* RVChartRing.Ring B :=
  RESChartRing.lift B (resInvariant B)

theorem ofRES_class (B : Base (M := M)) {n : ℕ} (a : RESChart B n) :
    ofRES B (RESChartRing.objectClass a) = RVChartRing.objectClass a.toChart :=
  RESChartRing.lift_objectClass B (resInvariant B) a

theorem ofRES_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (ofRES B)).comp (RESRingCoaction.coaction B) =
      (RVGrading.coaction B).comp (ofRES B) := by
  apply RESRingCoaction.hom_ext B
  intro n a
  change (RESRingCoaction.coaction B (RESChartRing.objectClass a)).map (ofRES B) =
    RVGrading.coaction B (ofRES B (RESChartRing.objectClass a))
  rw [RESRingCoaction.coaction_class, Polynomial.map_monomial, ofRES_class, RVGrading.coaction_class]

theorem ofRES_mem (B : Base (M := M)) {n : ℕ} {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B n) : ofRES B x ∈ RVGrading.gradedPiece B n := by
  change RESRingCoaction.coaction B x = Polynomial.monomial n x at hx
  change RVGrading.coaction B (ofRES B x) = Polynomial.monomial n (ofRES B x)
  have he : RVGrading.coaction B (ofRES B x) = (RESRingCoaction.coaction B x).map (ofRES B) :=
    (RingHom.congr_fun (ofRES_coaction B) x).symm
  rw [he, hx, Polynomial.map_monomial]

end DiamondIntegral.Section4.RVChartMaps
