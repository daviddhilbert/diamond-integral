import «section 4».RVMeasuredGroup
import «section 4».RVSharpCharts
import «section 4».RVPointChoices
import «section 4».GammaRadiusAnnulus

/-! Actual additive RV classes P_gamma for the author-approved radius
indexing. Their singleton choice is independent and the zero-radius class
is zero. The graded product ring, generated ideal and retraction of these
classes remain separate constructions. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVRadiusGenerators
open GammaRVLifts RVMeasuredGroup RVSharpCharts RVPointChoices GammaRadiusAnnulus

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure RadiusLift (B : Base (M := M)) (γ : Values.Gamma (M := M)) where
  point : Code (M := M)
  definable : DefinableClosureAtBase B .rv (raw point)
  value_eq : value point = γ

theorem radiusLift_exists (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : Nonempty (RadiusLift B γ) := by
  obtain ⟨t, ht, hv⟩ := (admissibleRadii_iff B γ).mp hγ |>.2
  exact ⟨⟨t, ht, hv⟩⟩

def oneCode : Code (M := M) := ⟨1, (unit_nonzero_code 1).2⟩

theorem oneCode_value : value (oneCode (M := M)) = 1 := Subtype.ext RVOperations.vrv_one

theorem oneCode_definable (B : Base (M := M)) : DefinableClosureAtBase B .rv (raw (oneCode (M := M))) :=
  (rvNames B).one_mem

def unitLift (B : Base (M := M)) : RadiusLift B 1 :=
  ⟨oneCode, oneCode_definable B, oneCode_value⟩

def radiusGenerator (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) : KGroup B 1 :=
  objectClass (sharpChart (annulusChart B γ hγ)) + objectClass (pointChart B t.point t.definable) -
    objectClass (pointChart B oneCode (oneCode_definable B))

theorem radiusGenerator_independent (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t u : RadiusLift B γ) :
    radiusGenerator B γ hγ t = radiusGenerator B γ hγ u := by
  have h := objectClass_iso (same_value_iso B t.point u.point t.definable u.definable
    (t.value_eq.trans u.value_eq.symm))
  change objectClass (sharpChart (annulusChart B γ hγ)) + objectClass (pointChart B t.point t.definable) - _ =
    objectClass (sharpChart (annulusChart B γ hγ)) + objectClass (pointChart B u.point u.definable) - _
  rw [h]

theorem radiusGenerator_zero (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B)
    (t : RadiusLift B 1) : radiusGenerator B 1 hγ t = 0 := by
  have he : (sharpChart (annulusChart B 1 hγ)).domain = ∅ := by
    change GammaRVChartPresentation.sharp (annulus (1 : Values.Gamma (M := M))) = ∅
    rw [annulus_one]
    ext z
    simp [GammaRVChartPresentation.sharp]
  have ha := objectClass_empty (sharpChart (annulusChart B 1 hγ)) he
  have hp := objectClass_iso (same_value_iso B t.point oneCode t.definable (oneCode_definable B)
    (t.value_eq.trans oneCode_value.symm))
  change objectClass (sharpChart (annulusChart B 1 hγ)) + objectClass (pointChart B t.point t.definable) -
    objectClass (pointChart B oneCode (oneCode_definable B)) = 0
  rw [ha, hp, zero_add, sub_self]

def pGamma (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) : KGroup B 1 :=
  radiusGenerator B γ hγ (Classical.choice (radiusLift_exists B γ hγ))

theorem pGamma_eq (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B)
    (t : RadiusLift B γ) : pGamma B γ hγ = radiusGenerator B γ hγ t :=
  radiusGenerator_independent B γ hγ _ t

theorem pGamma_zero (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B) :
    pGamma B 1 hγ = 0 := radiusGenerator_zero B hγ _

end DiamondIntegral.Section4.RVRadiusGenerators
