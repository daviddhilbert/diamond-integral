import «section 4».RVFiniteOrdinaryCounts
import «section 4».RVOrdinaryMaps
import «section 4».RESOrdinaryReduction

/-! An integer-valued degree-zero count on ordinary RV/RES rings and
its actual ordinary RES fibre quotient. The degree-zero unit survives;
this count vanishes in positive degree and does not detect the graded
point class. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryZeroCount
open RVMeasuredCharts RVFiniteOrdinaryCounts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def value (B : Base (M := M)) : ∀ k, Chart B k → ℤ
  | 0, a => count a a.zero_domain_finite
  | _ + 1, _ => 0

def invariant (B : Base (M := M)) : RVOrdinaryRing.Invariant B ℤ where
  value := value B
  unit := count_weightedUnit B 1 (GammaGroupNames.one_definable_base B)
  product k l a b := by
    cases k <;> cases l
    · exact count_product a b a.zero_domain_finite b.zero_domain_finite
    · exact (mul_zero _).symm
    · exact (zero_mul _).symm
    · exact (zero_mul _).symm
  iso k a b f := by
    cases k
    · exact count_iso a.zero_domain_finite b.zero_domain_finite f
    · rfl
  empty k a ha := by
    cases k
    · exact count_empty a a.zero_domain_finite ha
    · rfl
  scissor k a b c d h := by
    cases k
    · exact count_scissor a b c d a.zero_domain_finite b.zero_domain_finite c.zero_domain_finite d.zero_domain_finite h
    · rfl

def full (B : Base (M := M)) : RVOrdinaryRing.Ring B →+* ℤ := RVOrdinaryRing.lift B (invariant B)

theorem full_class (B : Base (M := M)) {k : ℕ} (a : Chart B k) : full B (RVOrdinaryRing.objectClass a) = value B k a :=
  RVOrdinaryRing.lift_objectClass B (invariant B) a

def res (B : Base (M := M)) : RESOrdinaryRing.Ring B →+* ℤ := (full B).comp (RVOrdinaryMaps.ofRES B)

theorem res_class (B : Base (M := M)) {k : ℕ} (a : RESChart B k) : res B (RESOrdinaryRing.objectClass a) = value B k a.toChart := by
  change full B (RVOrdinaryMaps.ofRES B (RESOrdinaryRing.objectClass a)) = _
  rw [RVOrdinaryMaps.ofRES_class, full_class]

theorem fibreIdeal_zero (B : Base (M := M)) : RESOrdinaryReduction.fibreIdeal B ≤ RingHom.ker (res B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨α, hα, rfl⟩
  change res B (_ - _) = 0
  rw [map_sub, res_class, res_class]
  exact sub_self _

def reduced (B : Base (M := M)) : RESOrdinaryReduction.ReducedRing B →+* ℤ :=
  Ideal.Quotient.lift _ (res B) (fibreIdeal_zero B)

theorem reduced_zero_ne_one (B : Base (M := M)) : (0 : RESOrdinaryReduction.ReducedRing B) ≠ 1 := by
  intro h
  have he := congrArg (reduced B) h
  have hz : (0 : ℤ) = 1 := by simpa only [map_zero, map_one] using he
  exact zero_ne_one hz

theorem reduced_point (B : Base (M := M)) : reduced B (RESOrdinaryReduction.pointClass B) = 0 := res_class B (RESFibreObjects.point B)

end DiamondIntegral.Section4.RVOrdinaryZeroCount
