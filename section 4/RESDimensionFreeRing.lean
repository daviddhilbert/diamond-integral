import «section 4».RESHomogenization
import «section 4».RESPointIdentification
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A dimension-free presentation on actual RES charts: ordinary chart
classes are identified by actual original-base underlying bijections in
all degrees. Homogenization proves the forget-degree kernel is exactly
the degree-one point minus the unit. Finite-coproduct category
identification is still a separate obligation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESDimensionFreeRing
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def relations (B : Base (M := M)) : Set (RESOrdinaryRing.Ring B) :=
  {x | ∃ k l, ∃ a : RESChart B k, ∃ b : RESChart B l,
    ∃ _F : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart,
      x = RESOrdinaryRing.objectClass a - RESOrdinaryRing.objectClass b}

def degreeIdeal (B : Base (M := M)) : Ideal (RESOrdinaryRing.Ring B) := Ideal.span (relations B)

def Ring (B : Base (M := M)) := RESOrdinaryRing.Ring B ⧸ degreeIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RESOrdinaryRing.Ring B →+* Ring B := Ideal.Quotient.mk (degreeIdeal B)

def objectClass {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : Ring B := quotient B (RESOrdinaryRing.objectClass a)

theorem objectClass_iso {B : Base (M := M)} {k l : ℕ} (a : RESChart B k) (b : RESChart B l)
    (F : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart) : objectClass a = objectClass b := by
  apply sub_eq_zero.mp
  change quotient B (RESOrdinaryRing.objectClass a) - quotient B (RESOrdinaryRing.objectClass b) = 0
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, l, a, b, F, rfl⟩)

theorem objectClass_product {B : Base (M := M)} {k l : ℕ} (a : RESChart B k) (b : RESChart B l) :
    objectClass (RVMeasuredProductProperties.resProduct a b) = objectClass a * objectClass b := by
  change quotient B (RESOrdinaryRing.objectClass _) = quotient B (RESOrdinaryRing.objectClass a) * quotient B (RESOrdinaryRing.objectClass b)
  rw [RESOrdinaryRing.objectClass_product, map_mul]

theorem objectClass_unit (B : Base (M := M)) : objectClass (RESChartRing.unit B) = 1 := by
  change quotient B (RESOrdinaryRing.objectClass (RESChartRing.unit B)) = 1
  rw [RESOrdinaryRing.objectClass_unit, map_one]

def pointClass (B : Base (M := M)) : RESOrdinaryRing.Ring B := RESOrdinaryRing.objectClass (RESPointTuples.res B 1)

def pointIdeal (B : Base (M := M)) : Ideal (RESOrdinaryRing.Ring B) := Ideal.span {pointClass B - 1}

theorem point_minus_one_mem (B : Base (M := M)) : pointClass B - 1 ∈ degreeIdeal B := by
  have he : RESOrdinaryRing.objectClass (RESPointTuples.res B 1) - RESOrdinaryRing.objectClass (RESPointTuples.res B 0) ∈ degreeIdeal B :=
    Ideal.subset_span ⟨1, 0, RESPointTuples.res B 1, RESPointTuples.res B 0, RESPointTuples.underlyingIso B 1 0, rfl⟩
  simpa only [pointClass, RESPointTuples.ordinary_zero] using he

theorem pointIdeal_le_degreeIdeal (B : Base (M := M)) : pointIdeal B ≤ degreeIdeal B := by
  apply Ideal.span_le.mpr
  rintro x (rfl : x = pointClass B - 1)
  exact point_minus_one_mem B

theorem point_quotient_one (B : Base (M := M)) :
    Ideal.Quotient.mk (pointIdeal B) (RESOrdinaryRing.objectClass (RESPointTuples.res B 1)) = 1 := by
  have he : Ideal.Quotient.mk (pointIdeal B) (pointClass B - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [map_sub, map_one] at he
  exact sub_eq_zero.mp he

theorem relation_mem_pointIdeal (B : Base (M := M)) (x : RESOrdinaryRing.Ring B)
    (hx : x ∈ relations B) : x ∈ pointIdeal B := by
  obtain ⟨k, l, a, b, F, rfl⟩ := hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he := congrArg (Ideal.Quotient.mk (pointIdeal B)) (RESHomogenization.ordinary_homogenization a b F)
  simpa only [map_mul, map_pow, point_quotient_one, one_pow, mul_one] using he

theorem degreeIdeal_le_pointIdeal (B : Base (M := M)) : degreeIdeal B ≤ pointIdeal B :=
  Ideal.span_le.mpr (fun x hx => relation_mem_pointIdeal B x hx)

theorem degreeIdeal_eq_pointIdeal (B : Base (M := M)) : degreeIdeal B = pointIdeal B :=
  le_antisymm (degreeIdeal_le_pointIdeal B) (pointIdeal_le_degreeIdeal B)

theorem pointIdeal_eq_manuscript (B : Base (M := M)) :
    pointIdeal B = Ideal.span {RESOrdinaryRing.objectClass (RESFibreObjects.point B) - 1} := by
  unfold pointIdeal pointClass
  rw [RESPointIdentification.ordinary_point]

theorem kernel_quotient (B : Base (M := M)) :
    RingHom.ker (quotient B) = Ideal.span {RESOrdinaryRing.objectClass (RESFibreObjects.point B) - 1} := by
  change RingHom.ker (Ideal.Quotient.mk (degreeIdeal B)) = _
  rw [Ideal.mk_ker, degreeIdeal_eq_pointIdeal, pointIdeal_eq_manuscript]

def normalizationEquiv (B : Base (M := M)) : (RESOrdinaryRing.Ring B ⧸ pointIdeal B) ≃+* Ring B :=
  Ideal.quotEquivOfEq (degreeIdeal_eq_pointIdeal B).symm

theorem normalizationEquiv_mk (B : Base (M := M)) (x : RESOrdinaryRing.Ring B) :
    normalizationEquiv B (Ideal.Quotient.mk (pointIdeal B) x) = quotient B x := rfl

end DiamondIntegral.Section4.RESDimensionFreeRing
