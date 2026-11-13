import «section 4».RVMeasuredScaling
import «section 4».RVRadiusIdeal
import «section 4».GammaRVIdentityIso
import «section 4».RVSharpScissors

/-! The measured forgetful image of every accepted radius generator is
an explicit degree-zero volume-weight multiple of the actual full-RV
class P. This proves the ideal inclusion in Notation 4.13 without a global
RV tensor isomorphism or an Euler retraction. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVMeasuredRadius
open RVMeasuredCharts RVSharpCharts RVChartRing RVScaledRays GammaRadiusAnnulus
open GammaRVLifts RVRadiusGenerators GammaChartOperations GammaDefinableMaps
open GammaGroupNames GammaCounterweightedRay GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem ray_scissor (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) :
    objectClass (sharpChart (RVMeasuredSpecialClasses.rayChart B)) =
      objectClass (sharpChart (annulusChart B γ hγ)) +
        objectClass (aboveChart B γ (admissible_definable B hγ)) := by
  have hUeq := annulus_union_above γ hγ.1
  have hNeq := annulus_inter_above γ
  have hI := annulus_definable B γ hγ
  have hJ := above_definable B γ (admissible_definable B hγ)
  have hU : GammaDefinable B (annulus γ ∪ above γ) := hUeq.symm ▸ positiveRay_definable B
  have hN : GammaDefinable B (annulus γ ∩ above γ) :=
    hNeq.symm ▸ GammaIntegerFamilies.empty_definable_base B 1
  let μ : (Fin 1 → Values.Gamma (M := M)) → Values.Gamma (M := M) := fun _ => 1
  have hμ : MapDefinable B μ := constant_definable B 1 (one_definable_base B)
  have hsc := objectClass_scissor _ _ _ _
    (RVSharpScissors.sharp_scissor B 1 (annulus γ) (above γ) hI hJ hU hN μ hμ)
  have hcU : objectClass (sharpChart (ofTotal B 1 (annulus γ ∪ above γ) hU μ hμ)) =
      objectClass (sharpChart (RVMeasuredSpecialClasses.rayChart B)) :=
    objectClass_iso (sharpIso (GammaRVIdentityIso.sameDomainIso _ _ hUeq (fun _ _ => rfl)))
  have hcN : objectClass (sharpChart (ofTotal B 1 (annulus γ ∩ above γ) hN μ hμ)) = 0 := by
    apply objectClass_empty
    ext u
    change (Proper u ∧ GammaRVChartPresentation.codeValues u ∈ annulus γ ∩ above γ) ↔ False
    exact ⟨fun hu => not_lt_of_ge hu.2.1.2 hu.2.2, fun hu => hu.elim⟩
  have hcI : objectClass (sharpChart (ofTotal B 1 (annulus γ) hI μ hμ)) =
      objectClass (sharpChart (annulusChart B γ hγ)) :=
    objectClass_iso (sharpIso (GammaRVIdentityIso.sameDomainIso _ _ rfl (fun _ _ => rfl)))
  have hcJ : objectClass (sharpChart (ofTotal B 1 (above γ) hJ μ hμ)) =
      objectClass (aboveChart B γ (admissible_definable B hγ)) :=
    objectClass_iso (sharpIso (GammaRVIdentityIso.sameDomainIso _ _ rfl (fun _ _ => rfl)))
  rw [hcU, hcN, hcI, hcJ, add_zero] at hsc
  exact hsc

theorem forget_radiusGenerator (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) :
    RVBoundedMaps.forget B (RVRadiusIdeal.radiusGenerator B γ hγ t) =
      (objectClass (RVMeasuredCharts.weightedUnit B γ (admissible_definable B hγ)) - 1) *
        RVMeasuredSpecialClasses.pClass B := by
  have hs := ray_scissor B γ hγ
  rw [RVMeasuredScaling.above_class B γ (admissible_definable B hγ) t] at hs
  have ha : objectClass (sharpChart (annulusChart B γ hγ)) =
      objectClass (sharpChart (RVMeasuredSpecialClasses.rayChart B)) -
        objectClass (RVMeasuredCharts.weightedUnit B γ (admissible_definable B hγ)) *
          objectClass (sharpChart (RVMeasuredSpecialClasses.rayChart B)) :=
    eq_sub_iff_add_eq.mpr hs.symm
  unfold RVRadiusIdeal.radiusGenerator
  simp only [map_sub, map_add, RVBoundedMaps.forget_class]
  change objectClass (sharpChart (annulusChart B γ hγ)) +
    objectClass (RVPointChoices.pointChart B t.point t.definable) -
      objectClass (RVPointChoices.pointChart B oneCode (oneCode_definable B)) = _
  rw [RVMeasuredScaling.point_class B γ (admissible_definable B hγ) t]
  change _ = (_ - 1) *
    (objectClass (RVPointChoices.pointChart B oneCode (oneCode_definable B)) -
      objectClass (sharpChart (RVMeasuredSpecialClasses.rayChart B)))
  rw [ha]
  ring

theorem forget_pGamma (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) :
    RVBoundedMaps.forget B (RVRadiusIdeal.pGamma B γ hγ) =
      (objectClass (RVMeasuredCharts.weightedUnit B γ (admissible_definable B hγ)) - 1) *
        RVMeasuredSpecialClasses.pClass B :=
  forget_radiusGenerator B γ hγ _

theorem radiusIdeal_le_comap_pIdeal (B : Base (M := M)) :
    RVRadiusIdeal.radiusIdeal B ≤
      (Ideal.span {RVMeasuredSpecialClasses.pClass B}).comap (RVBoundedMaps.forget B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ, rfl⟩
  change RVBoundedMaps.forget B (RVRadiusIdeal.pGamma B γ hγ) ∈
    (Ideal.span {RVMeasuredSpecialClasses.pClass B} : Ideal (Ring B))
  rw [forget_pGamma]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

end DiamondIntegral.Section4.RVMeasuredRadius
