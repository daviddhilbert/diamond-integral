import «section 4».RVDisjointGrading
import «section 4».RVOrdinaryDisjointGrading
import «section 4».RVMeasuredPQuotient
import «section 4».RVOrdinaryPNormalization
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Actual P quotients in the intrinsic disjoint-union presentations.
The measured relation P=0 and ordinary relation P=1 are compared
separately with their scissor quotients. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVDisjointPQuotients
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

namespace Measured

def pClass (B : Base (M := M)) : RVDisjointPresentation.Ring B :=
  RVDisjointPresentation.objectClass (RESFibreObjects.point B).toChart -
    RVDisjointPresentation.objectClass (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B))

theorem toChart_pClass (B : Base (M := M)) :
    RVDisjointPresentation.toChartRing B (pClass B) = RVMeasuredSpecialClasses.pClass B := by
  simp only [pClass, RVMeasuredSpecialClasses.pClass, map_sub, RVDisjointPresentation.toChartRing_class]

def pIdeal (B : Base (M := M)) : Ideal (RVDisjointPresentation.Ring B) := Ideal.span {pClass B}

theorem map_pIdeal (B : Base (M := M)) :
    (pIdeal B).map (RVDisjointPresentation.toChartRing B) = RVMeasuredPQuotient.pIdeal B := by
  rw [pIdeal, RVMeasuredPQuotient.pIdeal, Ideal.map_span, Set.image_singleton, toChart_pClass]

def Ring (B : Base (M := M)) := RVDisjointPresentation.Ring B ⧸ pIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RVDisjointPresentation.Ring B →+* Ring B := Ideal.Quotient.mk _

def equivalence (B : Base (M := M)) : Ring B ≃+* RVMeasuredPQuotient.Ring B :=
  Ideal.quotientEquiv (pIdeal B) (RVMeasuredPQuotient.pIdeal B) (RVDisjointPresentation.equivalence B) (map_pIdeal B).symm

theorem equivalence_quotient (B : Base (M := M)) (x : RVDisjointPresentation.Ring B) :
    equivalence B (quotient B x) = RVMeasuredPQuotient.quotient B (RVDisjointPresentation.toChartRing B x) := rfl

theorem equivalence_class (B : Base (M := M)) {k : ℕ} (a : RVMeasuredCharts.Chart B k) :
    equivalence B (quotient B (RVDisjointPresentation.objectClass a)) =
      RVMeasuredPQuotient.quotient B (RVChartRing.objectClass a) := by
  rw [equivalence_quotient, RVDisjointPresentation.toChartRing_class]

theorem p_zero (B : Base (M := M)) : quotient B (pClass B) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

theorem pClass_mem (B : Base (M := M)) : pClass B ∈ RVDisjointGrading.piece B 1 :=
  (RVDisjointGrading.piece B 1).sub_mem (RVDisjointGrading.class_mem B _) (RVDisjointGrading.class_mem B _)

theorem pIdeal_homogeneous (B : Base (M := M)) : (pIdeal B).IsHomogeneous (RVDisjointGrading.piece B) := by
  apply Ideal.homogeneous_span
  intro x hx
  have he : x = pClass B := hx
  subst x
  exact ⟨1, pClass_mem B⟩

end Measured

namespace Ordinary

def pClass (B : Base (M := M)) : RVOrdinaryDisjointPresentation.Ring B :=
  RVOrdinaryDisjointPresentation.objectClass (RESFibreObjects.point B).toChart -
    RVOrdinaryDisjointPresentation.objectClass (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B))

theorem toChart_pClass (B : Base (M := M)) :
    RVOrdinaryDisjointPresentation.toChartRing B (pClass B) = RVOrdinaryPNormalization.pClass B := by
  simp only [pClass, RVOrdinaryPNormalization.pClass, map_sub, RVOrdinaryDisjointPresentation.toChartRing_class]

def pIdeal (B : Base (M := M)) : Ideal (RVOrdinaryDisjointPresentation.Ring B) := Ideal.span {pClass B - 1}

theorem map_pIdeal (B : Base (M := M)) :
    (pIdeal B).map (RVOrdinaryDisjointPresentation.toChartRing B) = RVOrdinaryPNormalization.pIdeal B := by
  rw [pIdeal, RVOrdinaryPNormalization.pIdeal, Ideal.map_span, Set.image_singleton, map_sub, toChart_pClass, map_one]

def Ring (B : Base (M := M)) := RVOrdinaryDisjointPresentation.Ring B ⧸ pIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RVOrdinaryDisjointPresentation.Ring B →+* Ring B := Ideal.Quotient.mk _

def equivalence (B : Base (M := M)) : Ring B ≃+* RVOrdinaryPNormalization.Ring B :=
  Ideal.quotientEquiv (pIdeal B) (RVOrdinaryPNormalization.pIdeal B) (RVOrdinaryDisjointPresentation.equivalence B) (map_pIdeal B).symm

theorem equivalence_quotient (B : Base (M := M)) (x : RVOrdinaryDisjointPresentation.Ring B) :
    equivalence B (quotient B x) = RVOrdinaryPNormalization.quotient B (RVOrdinaryDisjointPresentation.toChartRing B x) := rfl

theorem equivalence_class (B : Base (M := M)) {k : ℕ} (a : RVMeasuredCharts.Chart B k) :
    equivalence B (quotient B (RVOrdinaryDisjointPresentation.objectClass a)) =
      RVOrdinaryPNormalization.quotient B (RVOrdinaryRing.objectClass a) := by
  rw [equivalence_quotient, RVOrdinaryDisjointPresentation.toChartRing_class]

theorem p_one (B : Base (M := M)) : quotient B (pClass B) = 1 := by
  have h : quotient B (pClass B - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

end Ordinary
end DiamondIntegral.Section4.RVDisjointPQuotients
