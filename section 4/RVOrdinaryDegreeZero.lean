import «section 4».RVOrdinaryMapGradings
import «section 4».RVZeroDegreeEquivalences

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

namespace DiamondIntegral.Section4.RVOrdinaryDegreeZero
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def value (B : Base (M := M)) : ∀ k, Chart B k → RESOrdinaryRing.Ring B
  | 0, a => RESOrdinaryRing.objectClass (zeroRESChart a)
  | _ + 1, _ => 0

def invariant (B : Base (M := M)) : RVOrdinaryRing.Invariant B (RESOrdinaryRing.Ring B) where
  value := value B
  unit := RESOrdinaryRing.objectClass_unit B
  product k l a b := by
    cases k <;> cases l
    · exact RESOrdinaryRing.objectClass_product (zeroRESChart a) (zeroRESChart b)
    · exact (mul_zero _).symm
    · exact (zero_mul _).symm
    · exact (zero_mul _).symm
  iso k a b F := by
    cases k
    · exact RESOrdinaryRing.objectClass_iso F
    · rfl
  empty k a ha := by
    cases k
    · exact RESOrdinaryRing.objectClass_empty (zeroRESChart a) ha
    · rfl
  scissor k a b c d h := by
    cases k
    · exact RESOrdinaryRing.objectClass_scissor (zeroRESChart a) (zeroRESChart b) (zeroRESChart c) (zeroRESChart d) h
    · rfl

def full (B : Base (M := M)) : RVOrdinaryRing.Ring B →+* RESOrdinaryRing.Ring B :=
  RVOrdinaryRing.lift B (invariant B)

theorem full_class (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    full B (RVOrdinaryRing.objectClass a) = value B n a := RVOrdinaryRing.lift_objectClass B (invariant B) a

theorem full_ofRES (B : Base (M := M)) :
    (full B).comp (RVOrdinaryMaps.ofRES B) = (RESOrdinaryGrading.gradingCoaction B).zeroProjection := by
  apply RESOrdinaryRing.hom_ext B
  intro n a
  change full B (RVOrdinaryMaps.ofRES B (RESOrdinaryRing.objectClass a)) = _
  rw [RVOrdinaryMaps.ofRES_class, full_class]
  change value B n a.toChart = (RESOrdinaryGrading.coaction B (RESOrdinaryRing.objectClass a)).coeff 0
  rw [RESOrdinaryGrading.coaction_class]
  cases n with
  | zero => exact (Polynomial.coeff_monomial_same 0 _).symm
  | succ n => simp only [value, Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]

theorem full_left_inverse (B : Base (M := M)) {x : RESOrdinaryRing.Ring B}
    (hx : x ∈ RESOrdinaryGrading.gradedPiece B 0) : full B (RVOrdinaryMaps.ofRES B x) = x :=
  (RingHom.congr_fun (full_ofRES B) x).trans ((RESOrdinaryGrading.gradingCoaction B).zeroProjection_of_mem hx)

theorem full_injective_on_degree_zero (B : Base (M := M)) :
    Set.InjOn (RVOrdinaryMaps.ofRES B) (RESOrdinaryGrading.gradedPiece B 0) := by
  intro x hx y hy hxy
  calc
    x = full B (RVOrdinaryMaps.ofRES B x) := (full_left_inverse B hx).symm
    _ = full B (RVOrdinaryMaps.ofRES B y) := congrArg (full B) hxy
    _ = y := full_left_inverse B hy

theorem full_projection_range (B : Base (M := M)) (x : RVOrdinaryRing.Ring B) :
    (RVOrdinaryGrading.gradingCoaction B).zeroProjection x ∈ (RVOrdinaryMaps.ofRES B).range := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  let f := (RVOrdinaryGrading.gradingCoaction B).zeroProjection.comp (Ideal.Quotient.mk (RVOrdinaryRing.relationIdeal B))
  change f p ∈ (RVOrdinaryMaps.ofRES B).range
  induction p using FreeCommRing.induction_on with
  | neg_one =>
    rw [map_neg, map_one]
    exact (RVOrdinaryMaps.ofRES B).range.neg_mem (RVOrdinaryMaps.ofRES B).range.one_mem
  | of g =>
    rcases g with ⟨n, a⟩
    change (RVOrdinaryGrading.coaction B (RVOrdinaryRing.objectClass a)).coeff 0 ∈ (RVOrdinaryMaps.ofRES B).range
    rw [RVOrdinaryGrading.coaction_class]
    cases n with
    | zero =>
      rw [Polynomial.coeff_monomial_same]
      exact ⟨RESOrdinaryRing.objectClass (RVMeasuredCharts.zeroRESChart a), RVOrdinaryMaps.ofRES_class B _⟩
    | succ n =>
      simp only [Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]
      exact (RVOrdinaryMaps.ofRES B).range.zero_mem
  | add p q hp hq =>
    rw [map_add]
    exact (RVOrdinaryMaps.ofRES B).range.add_mem hp hq
  | mul p q hp hq =>
    rw [map_mul]
    exact (RVOrdinaryMaps.ofRES B).range.mul_mem hp hq

theorem full_degree_zero_surjective (B : Base (M := M)) (x : RVOrdinaryRing.Ring B)
    (hx : x ∈ RVOrdinaryGrading.gradedPiece B 0) :
    ∃ r : RESOrdinaryRing.Ring B, r ∈ RESOrdinaryGrading.gradedPiece B 0 ∧ RVOrdinaryMaps.ofRES B r = x := by
  obtain ⟨r, hr⟩ := full_projection_range B x
  have hrx : RVOrdinaryMaps.ofRES B r = x := hr.trans ((RVOrdinaryGrading.gradingCoaction B).zeroProjection_of_mem hx)
  refine ⟨(RESOrdinaryGrading.gradingCoaction B).zeroProjection r, (RESOrdinaryGrading.gradingCoaction B).zeroProjection_mem r, ?_⟩
  rw [(RESOrdinaryGrading.gradingCoaction B).zeroProjection_natural (RVOrdinaryGrading.gradingCoaction B)
    (RVOrdinaryMaps.ofRES B) (RVOrdinaryMapGradings.ofRES_coaction B), hrx]
  exact (RVOrdinaryGrading.gradingCoaction B).zeroProjection_of_mem hx

theorem forget_full_square (B : Base (M := M)) :
    (full B).comp (RVOrdinaryRing.forget B) =
      (RESOrdinaryRing.forget B).comp (RVZeroDegreeRetraction.full B) := by
  apply RVGrading.hom_ext B
  intro n a
  change full B (RVOrdinaryRing.forget B (RVChartRing.objectClass a)) =
    RESOrdinaryRing.forget B (RVZeroDegreeRetraction.full B (RVChartRing.objectClass a))
  rw [RVOrdinaryRing.forget_objectClass, full_class, RVZeroDegreeRetraction.full_class]
  cases n with
  | zero => exact (RESOrdinaryRing.forget_objectClass B (RVMeasuredCharts.zeroRESChart a)).symm
  | succ n => exact (map_zero (RESOrdinaryRing.forget B)).symm

def zeroEquiv (B : Base (M := M)) :
    (RESOrdinaryGrading.gradingCoaction B).zeroSubring ≃+*
      (RVOrdinaryGrading.gradingCoaction B).zeroSubring := by
  let f : (RESOrdinaryGrading.gradingCoaction B).zeroSubring →+*
      (RVOrdinaryGrading.gradingCoaction B).zeroSubring :=
    ((RVOrdinaryMaps.ofRES B).comp (RESOrdinaryGrading.gradingCoaction B).zeroSubring.subtype).codRestrict
      (RVOrdinaryGrading.gradingCoaction B).zeroSubring (fun x => RVOrdinaryMapGradings.ofRES_mem B x.property)
  exact RingEquiv.ofBijective f ⟨(by
    intro x y h
    apply Subtype.ext
    exact full_injective_on_degree_zero B x.property y.property (congrArg Subtype.val h)), (by
    intro x
    obtain ⟨r, hr, hrx⟩ := full_degree_zero_surjective B x.val x.property
    exact ⟨⟨r, hr⟩, Subtype.ext hrx⟩)⟩

theorem zeroEquiv_apply (B : Base (M := M)) (x : (RESOrdinaryGrading.gradingCoaction B).zeroSubring) :
    (zeroEquiv B x).val = RVOrdinaryMaps.ofRES B x.val := rfl

end DiamondIntegral.Section4.RVOrdinaryDegreeZero
