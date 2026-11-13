import «section 4».RVOrdinarySharpScissors
import «section 4».RVScaledRays
import «section 4».RVOrdinaryMaps
import «section 4».RESOrdinaryPoints
import «section 4».RVRadiusQuotient

/-! The accepted actual radius generators vanish after forgetting volume.
Named RV scaling and actual scissors prove annulus cancellation, including
radius zero, and produce the natural forgetful map out of the bounded RV
radius quotient. Global Euler descent is not used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryRadius
open RVMeasuredCharts RVSharpCharts RVOrdinaryRing RVOrdinarySharpScissors
open RVScaledRays GammaRadiusAnnulus GammaRVLifts RVRadiusGenerators
open GammaChartOperations GammaDefinableMaps GammaGroupNames GammaCounterweightedRay GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem annulus_zero (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) :
    objectClass (sharpChart (annulusChart B γ hγ)) = 0 := by
  have hUeq := annulus_union_above γ hγ.1
  have hNeq := annulus_inter_above γ
  have hI := annulus_definable B γ hγ
  have hJ := above_definable B γ (admissible_definable B hγ)
  have hU : GammaDefinable B (annulus γ ∪ above γ) := hUeq.symm ▸ positiveRay_definable B
  have hN : GammaDefinable B (annulus γ ∩ above γ) :=
    hNeq.symm ▸ GammaIntegerFamilies.empty_definable_base B 1
  let μ : (Fin 1 → Values.Gamma (M := M)) → Values.Gamma (M := M) := fun _ => 1
  have hμ : MapDefinable B μ := constant_definable B 1 (one_definable_base B)
  have hsc := scissor_ofTotal B 1 (annulus γ) (above γ) hI hJ hU hN μ hμ
  have hcU : objectClass (sharpChart (ofTotal B 1 (annulus γ ∪ above γ) hU μ hμ)) =
      objectClass (sharpChart (RVMeasuredSpecialClasses.rayChart B)) :=
    class_eq_of_support_eq _ _ hUeq
  have hcN : objectClass (sharpChart (ofTotal B 1 (annulus γ ∩ above γ) hN μ hμ)) = 0 :=
    empty_support _ hNeq
  have hcI : objectClass (sharpChart (ofTotal B 1 (annulus γ) hI μ hμ)) =
      objectClass (sharpChart (annulusChart B γ hγ)) :=
    class_eq_of_support_eq _ _ rfl
  have hcJ : objectClass (sharpChart (ofTotal B 1 (above γ) hJ μ hμ)) =
      objectClass (aboveChart B γ (admissible_definable B hγ)) :=
    class_eq_of_support_eq _ _ rfl
  rw [hcU, hcN, hcI, hcJ, add_zero] at hsc
  have hr := objectClass_iso (rayIso B γ (admissible_definable B hγ) t)
  rw [hr] at hsc
  have he : (0 : Ring B) + objectClass (aboveChart B γ (admissible_definable B hγ)) =
      objectClass (sharpChart (annulusChart B γ hγ)) +
        objectClass (aboveChart B γ (admissible_definable B hγ)) := by
    simpa only [zero_add] using hsc
  exact (add_right_cancel he).symm

theorem boundedForget_radiusGenerator (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) :
    RVOrdinaryMaps.boundedForget B (RVRadiusIdeal.radiusGenerator B γ hγ t) = 0 := by
  unfold RVRadiusIdeal.radiusGenerator
  simp only [map_sub, map_add, RVOrdinaryMaps.boundedForget_class]
  change objectClass (sharpChart (annulusChart B γ hγ)) +
    objectClass (RVPointChoices.pointChart B t.point t.definable) -
      objectClass (RVPointChoices.pointChart B oneCode (oneCode_definable B)) = 0
  rw [annulus_zero B γ hγ t,
    objectClass_iso (RESOrdinaryPoints.pointIso B t.point oneCode t.definable (oneCode_definable B)),
    zero_add, sub_self]

theorem boundedForget_pGamma (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) :
    RVOrdinaryMaps.boundedForget B (RVRadiusIdeal.pGamma B γ hγ) = 0 :=
  boundedForget_radiusGenerator B γ hγ _

theorem radiusIdeal_le_ker (B : Base (M := M)) :
    RVRadiusIdeal.radiusIdeal B ≤ RingHom.ker (RVOrdinaryMaps.boundedForget B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ, rfl⟩
  exact boundedForget_pGamma B γ hγ

def forget (B : Base (M := M)) : RVRadiusQuotient.Ring B →+* Ring B :=
  Ideal.Quotient.lift _ (RVOrdinaryMaps.boundedForget B) (radiusIdeal_le_ker B)

theorem forget_quotient (B : Base (M := M)) (x : RVBoundedRing.Ring B) :
    forget B (RVRadiusQuotient.quotient B x) = RVOrdinaryMaps.boundedForget B x := rfl

theorem forget_ofRES (B : Base (M := M)) :
    (forget B).comp (RVRadiusQuotient.ofRES B) =
      (RVOrdinaryMaps.ofRES B).comp (RESOrdinaryRing.forget B) := by
  change ((forget B).comp (RVRadiusQuotient.quotient B)).comp (RVBoundedMaps.ofRES B) = _
  change (RVOrdinaryMaps.boundedForget B).comp (RVBoundedMaps.ofRES B) = _
  exact RVOrdinaryMaps.boundedForget_ofRES B

end DiamondIntegral.Section4.RVOrdinaryRadius
