import «section 4».RVBoundedDisjointGrading
import «section 4».RVRadiusQuotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The accepted radius ideal in the intrinsic bounded disjoint-union
presentation and its actual quotient comparison. The generators use
exactly the original-base RV-liftable radii, including radius zero. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVDisjointRadiusQuotient
open RVBoundedDisjointPresentation GammaRVLifts GammaRadiusAnnulus RVRadiusGenerators RVPointChoices
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def radiusGenerator (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) : RVBoundedDisjointPresentation.Ring B :=
  objectClass (RVRadiusIdeal.boundedAnnulus B γ hγ) +
    objectClass (RVRadiusIdeal.boundedPoint B t.point t.definable) -
    objectClass (RVRadiusIdeal.boundedPoint B oneCode (oneCode_definable B))

theorem toChart_radiusGenerator (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) :
    toChartRing B (radiusGenerator B γ hγ t) = RVRadiusIdeal.radiusGenerator B γ hγ t := by
  simp only [radiusGenerator, RVRadiusIdeal.radiusGenerator, map_sub, map_add, toChartRing_class]

theorem radiusGenerator_independent (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t u : RadiusLift B γ) :
    radiusGenerator B γ hγ t = radiusGenerator B γ hγ u := by
  apply (equivalence B).injective
  change toChartRing B (radiusGenerator B γ hγ t) = toChartRing B (radiusGenerator B γ hγ u)
  rw [toChart_radiusGenerator, toChart_radiusGenerator]
  exact RVRadiusIdeal.radiusGenerator_independent B γ hγ t u

def pGamma (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    RVBoundedDisjointPresentation.Ring B := radiusGenerator B γ hγ (Classical.choice (radiusLift_exists B γ hγ))

theorem toChart_pGamma (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    toChartRing B (pGamma B γ hγ) = RVRadiusIdeal.pGamma B γ hγ := toChart_radiusGenerator B γ hγ _

theorem pGamma_zero (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B) :
    pGamma B 1 hγ = 0 := by
  apply (equivalence B).injective
  change toChartRing B (pGamma B 1 hγ) = toChartRing B 0
  rw [toChart_pGamma, map_zero]
  exact RVRadiusIdeal.pGamma_zero B hγ

def radiusIdeal (B : Base (M := M)) : Ideal (RVBoundedDisjointPresentation.Ring B) :=
  Ideal.span {x | ∃ γ : Values.Gamma (M := M), ∃ hγ : γ ∈ admissibleRadii B, x = pGamma B γ hγ}

theorem map_radiusIdeal (B : Base (M := M)) :
    (radiusIdeal B).map (toChartRing B) = RVRadiusIdeal.radiusIdeal B := by
  rw [radiusIdeal, RVRadiusIdeal.radiusIdeal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨γ, hγ, toChart_pGamma B γ hγ⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨pGamma B γ hγ, ⟨γ, hγ, rfl⟩, toChart_pGamma B γ hγ⟩

def Ring (B : Base (M := M)) := RVBoundedDisjointPresentation.Ring B ⧸ radiusIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RVBoundedDisjointPresentation.Ring B →+* Ring B := Ideal.Quotient.mk _

def quotientEquivalence (B : Base (M := M)) : Ring B ≃+* RVRadiusQuotient.Ring B :=
  Ideal.quotientEquiv (radiusIdeal B) (RVRadiusIdeal.radiusIdeal B) (equivalence B) (map_radiusIdeal B).symm

theorem quotientEquivalence_quotient (B : Base (M := M)) (x : RVBoundedDisjointPresentation.Ring B) :
    quotientEquivalence B (quotient B x) = RVRadiusQuotient.quotient B (toChartRing B x) := rfl

theorem quotientEquivalence_class (B : Base (M := M)) {k : ℕ} (a : RVBoundedCharts.BoundedChart B k) :
    quotientEquivalence B (quotient B (objectClass a)) = RVRadiusQuotient.quotient B (RVBoundedRing.objectClass a) := by
  rw [quotientEquivalence_quotient, toChartRing_class]


theorem pGamma_mem (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    pGamma B γ hγ ∈ RVBoundedDisjointGrading.piece B 1 := by
  unfold pGamma radiusGenerator
  exact (RVBoundedDisjointGrading.piece B 1).sub_mem
    ((RVBoundedDisjointGrading.piece B 1).add_mem
      (RVFamilyDisjointGrading.class_mem (family B) (toObject _))
      (RVFamilyDisjointGrading.class_mem (family B) (toObject _)))
    (RVFamilyDisjointGrading.class_mem (family B) (toObject _))

theorem radiusIdeal_homogeneous (B : Base (M := M)) :
    (radiusIdeal B).IsHomogeneous (RVBoundedDisjointGrading.piece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨γ, hγ, rfl⟩
  exact ⟨1, pGamma_mem B γ hγ⟩

theorem ideal_coefficients (B : Base (M := M)) : ∀ n x, x ∈ radiusIdeal B →
    (RVFamilyDisjointGrading.coaction (family B) x).coeff n ∈ radiusIdeal B :=
  (RVFamilyDisjointGrading.gradingCoaction (family B)).homogeneous_ideal_coefficients _ (radiusIdeal_homogeneous B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (RVFamilyDisjointGrading.gradingCoaction (family B)).quotient _ (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n
instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedDisjointPresentation.Ring B}
    (hx : x ∈ RVBoundedDisjointGrading.piece B n) : quotient B x ∈ piece B n :=
  (RVFamilyDisjointGrading.gradingCoaction (family B)).quotient_mem _ (ideal_coefficients B) hx

theorem comparison_ideal_zero (B : Base (M := M)) :
    radiusIdeal B ≤ RingHom.ker ((RVRadiusQuotient.quotient B).comp (toChartRing B)) := by
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← map_radiusIdeal B]
  exact Ideal.mem_map_of_mem _ hx

def comparison (B : Base (M := M)) : Ring B →+* RVRadiusQuotient.Ring B :=
  Ideal.Quotient.lift _ ((RVRadiusQuotient.quotient B).comp (toChartRing B)) (comparison_ideal_zero B)

theorem comparison_eq (B : Base (M := M)) : comparison B = (quotientEquivalence B).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  rfl

theorem quotientEquivalence_mem (B : Base (M := M)) {n : ℕ} {x : Ring B} (hx : x ∈ piece B n) :
    quotientEquivalence B x ∈ RVRadiusQuotient.piece B n := by
  have h := (RVFamilyDisjointGrading.gradingCoaction (family B)).quotientLift_mem
    (RVRadiusQuotient.coaction B) ((RVRadiusQuotient.quotient B).comp (toChartRing B))
    (radiusIdeal B) (ideal_coefficients B) (comparison_ideal_zero B)
    (fun _ _ hy => RVRadiusQuotient.quotient_mem B (RVBoundedDisjointGrading.toChart_mem B hy)) hx
  change comparison B x ∈ RVRadiusQuotient.piece B n at h
  rw [comparison_eq] at h
  exact h

def gradedComparison (B : Base (M := M)) : GradedRingHom (piece B) (RVRadiusQuotient.piece B) where
  toRingHom := (quotientEquivalence B).toRingHom
  map_mem := fun hx => quotientEquivalence_mem B hx

end DiamondIntegral.Section4.RVDisjointRadiusQuotient
