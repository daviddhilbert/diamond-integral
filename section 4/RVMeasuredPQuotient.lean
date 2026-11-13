import «section 4».RVMeasuredRadius
import «section 4».RVRadiusQuotient
import «section 4».CoactionGradedMaps

/-! The actual full measured RV quotient by P and the natural graded map
from the bounded radius quotient. These structural maps do not presuppose
an Euler retraction or the RV tensor-kernel theorem. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVMeasuredPQuotient
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pIdeal (B : Base (M := M)) : Ideal (RVChartRing.Ring B) :=
  Ideal.span {RVMeasuredSpecialClasses.pClass B}

theorem pIdeal_homogeneous (B : Base (M := M)) :
    (pIdeal B).IsHomogeneous (RVGrading.gradedPiece B) := by
  apply Ideal.homogeneous_span
  intro x hx
  have he : x = RVMeasuredSpecialClasses.pClass B := hx
  subst x
  exact ⟨1, RVMeasuredSpecialClasses.pClass_mem B⟩

def Ring (B : Base (M := M)) := RVChartRing.Ring B ⧸ pIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RVChartRing.Ring B →+* Ring B := Ideal.Quotient.mk (pIdeal B)

theorem ideal_coefficients (B : Base (M := M)) :
    ∀ n x, x ∈ pIdeal B → (RVGrading.coaction B x).coeff n ∈ pIdeal B :=
  (RVGrading.gradingCoaction B).homogeneous_ideal_coefficients _ (pIdeal_homogeneous B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (RVGrading.gradingCoaction B).quotient _ (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n

instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RVChartRing.Ring B}
    (hx : x ∈ RVGrading.gradedPiece B n) : quotient B x ∈ piece B n :=
  (RVGrading.gradingCoaction B).quotient_mem _ (ideal_coefficients B) hx

theorem p_zero (B : Base (M := M)) : quotient B (RVMeasuredSpecialClasses.pClass B) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

def boundedMap (B : Base (M := M)) : RVBoundedRing.Ring B →+* Ring B :=
  (quotient B).comp (RVBoundedMaps.forget B)

theorem radiusIdeal_le_ker (B : Base (M := M)) :
    RVRadiusIdeal.radiusIdeal B ≤ RingHom.ker (boundedMap B) := by
  intro x hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (RVMeasuredRadius.radiusIdeal_le_comap_pIdeal B hx)

def forget (B : Base (M := M)) : RVRadiusQuotient.Ring B →+* Ring B :=
  Ideal.Quotient.lift _ (boundedMap B) (radiusIdeal_le_ker B)

theorem forget_quotient (B : Base (M := M)) (x : RVBoundedRing.Ring B) :
    forget B (RVRadiusQuotient.quotient B x) = quotient B (RVBoundedMaps.forget B x) := rfl

theorem boundedMap_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedRing.Ring B}
    (hx : x ∈ RVBoundedGrading.gradedPiece B n) : boundedMap B x ∈ piece B n :=
  quotient_mem B (RVBoundedMaps.forget_mem B hx)

theorem forget_mem (B : Base (M := M)) {n : ℕ} {x : RVRadiusQuotient.Ring B}
    (hx : x ∈ RVRadiusQuotient.piece B n) : forget B x ∈ piece B n :=
  (RVBoundedGrading.gradingCoaction B).quotientLift_mem (coaction B)
    (boundedMap B) (RVRadiusIdeal.radiusIdeal B) (RVRadiusQuotient.ideal_coefficients B)
    (radiusIdeal_le_ker B) (fun _ _ hx => boundedMap_mem B hx) hx

def gradedForget (B : Base (M := M)) : GradedRingHom (RVRadiusQuotient.piece B) (piece B) where
  toRingHom := forget B
  map_mem := fun hx => forget_mem B hx

def ofRES (B : Base (M := M)) : RESChartRing.Ring B →+* Ring B :=
  (quotient B).comp (RVChartMaps.ofRES B)

theorem ofRES_mem (B : Base (M := M)) {n : ℕ} {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B n) : ofRES B x ∈ piece B n :=
  quotient_mem B (RVChartMaps.ofRES_mem B hx)

theorem forget_ofRES (B : Base (M := M)) :
    (forget B).comp (RVRadiusQuotient.ofRES B) = ofRES B := by
  change ((forget B).comp (RVRadiusQuotient.quotient B)).comp (RVBoundedMaps.ofRES B) = _
  change ((quotient B).comp (RVBoundedMaps.forget B)).comp (RVBoundedMaps.ofRES B) = _
  rw [RingHom.comp_assoc, RVBoundedMaps.forget_ofRES]
  rfl

end DiamondIntegral.Section4.RVMeasuredPQuotient
