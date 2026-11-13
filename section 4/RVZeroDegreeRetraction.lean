import «section 4».RVZeroDegreeRES

/-! Actual inverse maps in degree zero: a zero-degree RV object is a RES
object because its domain is finite. Positive-degree generators are sent
to zero. This proves injectivity on degree zero without an RV tensor
decomposition or a definable singleton-splitting assertion. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVZeroDegreeRetraction
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def value (B : Base (M := M)) : ∀ k, Chart B k → RESChartRing.Ring B
  | 0, a => RESChartRing.objectClass (zeroRESChart a)
  | _ + 1, _ => 0

def invariant (B : Base (M := M)) : RVChartRing.Invariant B (RESChartRing.Ring B) where
  value := value B
  unit := RESChartRing.objectClass_unit B
  product k l a b := by
    cases k <;> cases l
    · exact RESChartRing.objectClass_product (zeroRESChart a) (zeroRESChart b)
    · exact (mul_zero _).symm
    · exact (zero_mul _).symm
    · exact (zero_mul _).symm
  iso k a b F := by
    cases k
    · exact RESChartRing.objectClass_iso F
    · rfl
  empty k a ha := by
    cases k
    · exact RESChartRing.objectClass_empty (zeroRESChart a) ha
    · rfl
  scissor k a b c d h := by
    cases k
    · exact RESChartRing.objectClass_scissor (zeroRESChart a) (zeroRESChart b) (zeroRESChart c) (zeroRESChart d) h
    · rfl

def full (B : Base (M := M)) : RVChartRing.Ring B →+* RESChartRing.Ring B :=
  RVChartRing.lift B (invariant B)

theorem full_class (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    full B (RVChartRing.objectClass a) = value B n a := RVChartRing.lift_objectClass B (invariant B) a

theorem full_ofRES (B : Base (M := M)) :
    (full B).comp (RVChartMaps.ofRES B) = (RESGrading.gradingCoaction B).zeroProjection := by
  apply RESRingCoaction.hom_ext B
  intro n a
  change full B (RVChartMaps.ofRES B (RESChartRing.objectClass a)) = _
  rw [RVChartMaps.ofRES_class, full_class]
  change value B n a.toChart = (RESRingCoaction.coaction B (RESChartRing.objectClass a)).coeff 0
  rw [RESRingCoaction.coaction_class]
  cases n with
  | zero => exact (Polynomial.coeff_monomial_same 0 _).symm
  | succ n => simp only [value, Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]

theorem full_left_inverse (B : Base (M := M)) {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B 0) : full B (RVChartMaps.ofRES B x) = x :=
  (RingHom.congr_fun (full_ofRES B) x).trans ((RESGrading.gradingCoaction B).zeroProjection_of_mem hx)

theorem full_injective_on_degree_zero (B : Base (M := M)) :
    Set.InjOn (RVChartMaps.ofRES B) (RESRingCoaction.gradedPiece B 0) := by
  intro x hx y hy hxy
  calc
    x = full B (RVChartMaps.ofRES B x) := (full_left_inverse B hx).symm
    _ = full B (RVChartMaps.ofRES B y) := congrArg (full B) hxy
    _ = y := full_left_inverse B hy

def bounded (B : Base (M := M)) : RVBoundedRing.Ring B →+* RESChartRing.Ring B :=
  (full B).comp (RVBoundedMaps.forget B)

theorem bounded_ofRES (B : Base (M := M)) :
    (bounded B).comp (RVBoundedMaps.ofRES B) = (RESGrading.gradingCoaction B).zeroProjection := by
  change (full B).comp ((RVBoundedMaps.forget B).comp (RVBoundedMaps.ofRES B)) = _
  rw [RVBoundedMaps.forget_ofRES, full_ofRES]

theorem bounded_left_inverse (B : Base (M := M)) {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B 0) : bounded B (RVBoundedMaps.ofRES B x) = x :=
  (RingHom.congr_fun (bounded_ofRES B) x).trans ((RESGrading.gradingCoaction B).zeroProjection_of_mem hx)

theorem bounded_injective_on_degree_zero (B : Base (M := M)) :
    Set.InjOn (RVBoundedMaps.ofRES B) (RESRingCoaction.gradedPiece B 0) := by
  intro x hx y hy hxy
  calc
    x = bounded B (RVBoundedMaps.ofRES B x) := (bounded_left_inverse B hx).symm
    _ = bounded B (RVBoundedMaps.ofRES B y) := congrArg (bounded B) hxy
    _ = y := bounded_left_inverse B hy

end DiamondIntegral.Section4.RVZeroDegreeRetraction
