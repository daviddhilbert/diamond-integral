import «section 4».RVChartMaps
import «section 4».RVBoundedMaps

/-! Every homogeneous degree-zero class in either actual RV presentation
comes from a degree-zero RES class. Finite coordinate fibres in degree
zero give finite domains; no finite RV set is split into named points. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
variable {R S : Type*} [CommRing R] [CommRing S]

def zeroProjection (c : Coaction R) : R →+* R := Polynomial.constantCoeff.comp c.map

theorem zeroProjection_mem (c : Coaction R) (x : R) : c.zeroProjection x ∈ c.piece 0 :=
  c.coefficient_mem x 0

theorem zeroProjection_of_mem (c : Coaction R) {x : R} (hx : x ∈ c.piece 0) : c.zeroProjection x = x := by
  change (c.map x).coeff 0 = x
  change c.map x = Polynomial.monomial 0 x at hx
  rw [hx, Polynomial.coeff_monomial_same]

theorem zeroProjection_natural (c : Coaction R) (e : Coaction S) (f : R →+* S)
    (h : (Polynomial.mapRingHom f).comp c.map = e.map.comp f) (x : R) :
    f (c.zeroProjection x) = e.zeroProjection (f x) := by
  have he := congrArg (fun p : Polynomial S => p.coeff 0) (RingHom.congr_fun h x)
  change ((c.map x).map f).coeff 0 = (e.map (f x)).coeff 0 at he
  rw [Polynomial.coeff_map] at he
  exact he

end DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction

namespace DiamondIntegral.Section4.RVZeroDegreeRES
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem full_projection_range (B : Base (M := M)) (x : RVChartRing.Ring B) :
    (RVGrading.gradingCoaction B).zeroProjection x ∈ (RVChartMaps.ofRES B).range := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  let f := (RVGrading.gradingCoaction B).zeroProjection.comp (Ideal.Quotient.mk (RVChartRing.relationIdeal B))
  change f p ∈ (RVChartMaps.ofRES B).range
  induction p using FreeCommRing.induction_on with
  | neg_one =>
    rw [map_neg, map_one]
    exact (RVChartMaps.ofRES B).range.neg_mem (RVChartMaps.ofRES B).range.one_mem
  | of g =>
    rcases g with ⟨n, a⟩
    change (RVGrading.coaction B (RVChartRing.objectClass a)).coeff 0 ∈ (RVChartMaps.ofRES B).range
    rw [RVGrading.coaction_class]
    cases n with
    | zero =>
      rw [Polynomial.coeff_monomial_same]
      exact ⟨RESChartRing.objectClass (RVMeasuredCharts.zeroRESChart a), RVChartMaps.ofRES_class B _⟩
    | succ n =>
      simp only [Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]
      exact (RVChartMaps.ofRES B).range.zero_mem
  | add p q hp hq =>
    rw [map_add]
    exact (RVChartMaps.ofRES B).range.add_mem hp hq
  | mul p q hp hq =>
    rw [map_mul]
    exact (RVChartMaps.ofRES B).range.mul_mem hp hq

theorem full_degree_zero_surjective (B : Base (M := M)) (x : RVChartRing.Ring B)
    (hx : x ∈ RVGrading.gradedPiece B 0) :
    ∃ r : RESChartRing.Ring B, r ∈ RESRingCoaction.gradedPiece B 0 ∧ RVChartMaps.ofRES B r = x := by
  obtain ⟨r, hr⟩ := full_projection_range B x
  have hrx : RVChartMaps.ofRES B r = x := hr.trans ((RVGrading.gradingCoaction B).zeroProjection_of_mem hx)
  refine ⟨(RESGrading.gradingCoaction B).zeroProjection r, (RESGrading.gradingCoaction B).zeroProjection_mem r, ?_⟩
  rw [(RESGrading.gradingCoaction B).zeroProjection_natural (RVGrading.gradingCoaction B)
    (RVChartMaps.ofRES B) (RVChartMaps.ofRES_coaction B), hrx]
  exact (RVGrading.gradingCoaction B).zeroProjection_of_mem hx

theorem bounded_projection_range (B : Base (M := M)) (x : RVBoundedRing.Ring B) :
    (RVBoundedGrading.gradingCoaction B).zeroProjection x ∈ (RVBoundedMaps.ofRES B).range := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  let f := (RVBoundedGrading.gradingCoaction B).zeroProjection.comp (Ideal.Quotient.mk (RVBoundedRing.relationIdeal B))
  change f p ∈ (RVBoundedMaps.ofRES B).range
  induction p using FreeCommRing.induction_on with
  | neg_one =>
    rw [map_neg, map_one]
    exact (RVBoundedMaps.ofRES B).range.neg_mem (RVBoundedMaps.ofRES B).range.one_mem
  | of g =>
    rcases g with ⟨n, a⟩
    change (RVBoundedGrading.coaction B (RVBoundedRing.objectClass a)).coeff 0 ∈ (RVBoundedMaps.ofRES B).range
    rw [RVBoundedGrading.coaction_class]
    cases n with
    | zero =>
      rw [Polynomial.coeff_monomial_same]
      exact ⟨RESChartRing.objectClass (RVMeasuredCharts.zeroRESChart a.toChart), RVBoundedMaps.ofRES_class B _⟩
    | succ n =>
      simp only [Polynomial.coeff_monomial, Nat.succ_ne_zero, ite_false]
      exact (RVBoundedMaps.ofRES B).range.zero_mem
  | add p q hp hq =>
    rw [map_add]
    exact (RVBoundedMaps.ofRES B).range.add_mem hp hq
  | mul p q hp hq =>
    rw [map_mul]
    exact (RVBoundedMaps.ofRES B).range.mul_mem hp hq

theorem bounded_degree_zero_surjective (B : Base (M := M)) (x : RVBoundedRing.Ring B)
    (hx : x ∈ RVBoundedGrading.gradedPiece B 0) :
    ∃ r : RESChartRing.Ring B, r ∈ RESRingCoaction.gradedPiece B 0 ∧ RVBoundedMaps.ofRES B r = x := by
  obtain ⟨r, hr⟩ := bounded_projection_range B x
  have hrx : RVBoundedMaps.ofRES B r = x := hr.trans ((RVBoundedGrading.gradingCoaction B).zeroProjection_of_mem hx)
  refine ⟨(RESGrading.gradingCoaction B).zeroProjection r, (RESGrading.gradingCoaction B).zeroProjection_mem r, ?_⟩
  rw [(RESGrading.gradingCoaction B).zeroProjection_natural (RVBoundedGrading.gradingCoaction B)
    (RVBoundedMaps.ofRES B) (RVBoundedMaps.ofRES_coaction B), hrx]
  exact (RVBoundedGrading.gradingCoaction B).zeroProjection_of_mem hx

end DiamondIntegral.Section4.RVZeroDegreeRES
