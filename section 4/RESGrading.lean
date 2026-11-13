import «section 4».RESRingCoaction
import «section 4».PolynomialCoactionGrading

/-! The measured RES chart ring has its actual natural-number grading.
This includes finite homogeneous decomposition, not only degree labels.
Identification with the finite-coproduct manuscript category remains open. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESGrading
open RVMeasuredCharts RESRingCoaction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem coaction_coassoc (B : Base (M := M)) :
    (Polynomial.mapRingHom (coaction B)).comp (coaction B) =
      PolynomialDiagonal.diagonal.comp (coaction B) := by
  apply RESRingCoaction.hom_ext B
  intro n a
  change (coaction B (RESChartRing.objectClass a)).map (coaction B) =
    PolynomialDiagonal.diagonal (coaction B (RESChartRing.objectClass a))
  rw [coaction_class, Polynomial.map_monomial, coaction_class,
    PolynomialDiagonal.diagonal_monomial]

def gradingCoaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (RESChartRing.Ring B) where
  map := coaction B
  counit := coaction_counit B
  coassoc := coaction_coassoc B

instance gradedRing (B : Base (M := M)) : GradedRing (gradedPiece B) :=
  (gradingCoaction B).grading

def component (B : Base (M := M)) (n : ℕ) : RESChartRing.Ring B →+ RESChartRing.Ring B :=
  (Polynomial.lcoeff (RESChartRing.Ring B) n).toAddMonoidHom.comp (coaction B).toAddMonoidHom

theorem component_mem (B : Base (M := M)) (n : ℕ) (x : RESChartRing.Ring B) :
    component B n x ∈ gradedPiece B n := (gradingCoaction B).coefficient_mem x n

theorem sum_components (B : Base (M := M)) (x : RESChartRing.Ring B) :
    ∑ n ∈ (coaction B x).support, component B n x = x :=
  (gradingCoaction B).sum_coefficients x

theorem component_class (B : Base (M := M)) {n : ℕ} (a : RESChart B n) (m : ℕ) :
    component B m (RESChartRing.objectClass a) =
      if n = m then RESChartRing.objectClass a else 0 := by
  change (coaction B (RESChartRing.objectClass a)).coeff m = _
  rw [coaction_class, Polynomial.coeff_monomial]

theorem component_of_mem (B : Base (M := M)) {n : ℕ} {x : RESChartRing.Ring B}
    (hx : x ∈ gradedPiece B n) (m : ℕ) :
    component B m x = if n = m then x else 0 :=
  (gradingCoaction B).coefficient_of_mem hx m

end DiamondIntegral.Section4.RESGrading
