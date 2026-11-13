import «section 4».RVBoundedMaps
import «section 4».RVRadiusBounds
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! The actual P_gamma classes and their homogeneous ideal in the bounded
measured RV chart ring, for exactly the accepted RV-liftable radii. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVRadiusIdeal
open RVMeasuredCharts RVBoundedCharts RVBoundedRing RVRadiusGenerators
open RVSharpCharts RVPointChoices GammaRVLifts GammaRadiusAnnulus
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def boundedAnnulus (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : BoundedChart B 1 :=
  ⟨sharpChart (annulusChart B γ hγ), RVRadiusBounds.annulus_domain_bounded B γ hγ⟩

def boundedPoint (B : Base (M := M)) (t : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) : BoundedChart B 1 :=
  RVBoundedCharts.ofRES (pointRESChart B t ht)

def radiusGenerator (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) : Ring B :=
  objectClass (boundedAnnulus B γ hγ) + objectClass (boundedPoint B t.point t.definable) -
    objectClass (boundedPoint B oneCode (oneCode_definable B))

theorem radiusGenerator_independent (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t u : RadiusLift B γ) :
    radiusGenerator B γ hγ t = radiusGenerator B γ hγ u := by
  have h : objectClass (boundedPoint B t.point t.definable) = objectClass (boundedPoint B u.point u.definable) :=
    objectClass_iso (same_value_iso B t.point u.point t.definable u.definable (t.value_eq.trans u.value_eq.symm))
  unfold radiusGenerator
  rw [h]

theorem radiusGenerator_zero (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B)
    (t : RadiusLift B 1) : radiusGenerator B 1 hγ t = 0 := by
  have he : (boundedAnnulus B 1 hγ).domain = ∅ := by
    change GammaRVChartPresentation.sharp (annulus (1 : Values.Gamma (M := M))) = ∅
    rw [annulus_one]
    ext z
    simp [GammaRVChartPresentation.sharp]
  have hp : objectClass (boundedPoint B t.point t.definable) = objectClass (boundedPoint B oneCode (oneCode_definable B)) :=
    objectClass_iso (same_value_iso B t.point oneCode t.definable (oneCode_definable B)
      (t.value_eq.trans oneCode_value.symm))
  unfold radiusGenerator
  rw [objectClass_empty _ he, hp, zero_add, sub_self]

def pGamma (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) : Ring B :=
  radiusGenerator B γ hγ (Classical.choice (radiusLift_exists B γ hγ))

theorem pGamma_eq (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B)
    (t : RadiusLift B γ) : pGamma B γ hγ = radiusGenerator B γ hγ t :=
  radiusGenerator_independent B γ hγ _ t

theorem pGamma_zero (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B) :
    pGamma B 1 hγ = 0 := radiusGenerator_zero B hγ _

theorem pGamma_mem_degree_one (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : pGamma B γ hγ ∈ RVBoundedGrading.gradedPiece B 1 :=
  (RVBoundedGrading.gradedPiece B 1).sub_mem
    ((RVBoundedGrading.gradedPiece B 1).add_mem (RVBoundedGrading.class_mem B _) (RVBoundedGrading.class_mem B _))
    (RVBoundedGrading.class_mem B _)

def radiusIdeal (B : Base (M := M)) : Ideal (Ring B) :=
  Ideal.span {x | ∃ γ : Values.Gamma (M := M), ∃ hγ : γ ∈ admissibleRadii B, x = pGamma B γ hγ}

theorem pGamma_mem_ideal (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : pGamma B γ hγ ∈ radiusIdeal B :=
  Ideal.subset_span ⟨γ, hγ, rfl⟩

theorem radiusIdeal_homogeneous (B : Base (M := M)) :
    (radiusIdeal B).IsHomogeneous (RVBoundedGrading.gradedPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨γ, hγ, rfl⟩
  exact ⟨1, pGamma_mem_degree_one B γ hγ⟩

theorem forget_pGamma (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) :
    RVBoundedMaps.forget B (pGamma B γ hγ) = RVChartMaps.fixedDegreeMap B 1 (RVRadiusGenerators.pGamma B γ hγ) := by
  unfold pGamma radiusGenerator RVRadiusGenerators.pGamma RVRadiusGenerators.radiusGenerator
  simp only [map_sub, map_add, RVBoundedMaps.forget_class, RVChartMaps.fixedDegreeMap_class]
  rfl

end DiamondIntegral.Section4.RVRadiusIdeal
