import «section 4».GammaOrdinaryRing
import «section 4».RVScaledRays
import «section 4».GammaTranslation

/-! Named RV scaling supplies an actual ordinary Gamma morphism from
the positive ray to the ray above an RV-liftable radius. Ordinary Gamma
scissors then kill the half-open annulus, including radius zero. No
Euler specialization or choice of an RV section is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryRadius
open GammaOrdinaryCharts GammaOrdinaryRing GammaRVLifts GammaOrderLogic
open GammaDefinableMaps GammaGroupNames GammaRVChartPresentation
open RVScaledRays RVNamedMultiplication GammaRadiusAnnulus RVRadiusGenerators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ray (B : Base (M := M)) : Chart B 1 := ofWeighted (RVMeasuredSpecialClasses.rayChart B)
def upperRay (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : Chart B 1 :=
  ofSet B 1 (above γ) (above_definable B γ hγ)
def annulus (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : Chart B 1 := ofWeighted (annulusChart B γ hγ)

theorem shift_ray_bijective (γ : Values.Gamma (M := M)) :
    Set.BijOn (GammaTranslation.shift (fun _ : Fin 1 => γ))
      (GammaCounterweightedRay.positiveRay (M := M)) (above γ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    change γ < γ * z 0
    simpa only [mul_one] using mul_lt_mul_right hz γ
  · intro z _ w _ h
    exact funext (fun i => mul_left_cancel (congrFun h i))
  · intro z hz
    refine ⟨fun i => γ⁻¹ * z i, ?_, ?_⟩
    · change 1 < γ⁻¹ * z 0
      simpa only [inv_mul_cancel] using mul_lt_mul_right hz γ⁻¹
    · funext i
      change γ * (γ⁻¹ * z i) = z i
      rw [← mul_assoc, mul_inv_cancel, one_mul]

def rayIso (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (t : RadiusLift B γ) :
    Iso (ray B) (upperRay B γ hγ) where
  map := GammaTranslation.shift (fun _ : Fin 1 => γ)
  graph_definable := GammaTupleMaps.graph_definable B _ (ray B).support_definable _
    (GammaTranslation.shift_coordinates B (fun _ : Fin 1 => γ) (fun _ => hγ))
  bijective := shift_ray_bijective γ
  lift := scale (raw t.point)
  lift_definable := by
    have h := graphOn_definable B (raw t.point) (raw_rv t.point) t.definable
      (sharp (ray B).support) (sharp_definable _ (ray B).support_definable)
    have he : rawGraphOn (ray B).support (scale (raw t.point)) =
        RVMeasuredCharts.graphOn (sharp (ray B).support) (scale (raw t.point)) := by
      ext w
      exact and_congr_right (fun _ => eq_comm)
    rw [he]
    exact h
  lift_bijective := scale_ray_bijective B γ hγ t
  contraction := by
    intro z hz
    funext i
    fin_cases i
    change codeValue (iRVMul (raw t.point) (z 0)) = γ * codeValue (z 0)
    rw [codeValue_mul _ _ ⟨raw_rv t.point, raw_ne_zero t.point⟩ (hz.1 0),
      codeValue_raw, t.value_eq]

theorem annulus_zero (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) : objectClass (annulus B γ hγ) = 0 := by
  have h := class_scissor (annulus B γ hγ) (upperRay B γ (admissible_definable B hγ))
    (ray B) (empty B 1) ⟨(annulus_union_above γ hγ.1).symm, (annulus_inter_above γ).symm⟩
  rw [class_empty (empty B 1) rfl, add_zero,
    class_iso (rayIso B γ (admissible_definable B hγ) t)] at h
  have he : (0 : Ring B) + objectClass (upperRay B γ (admissible_definable B hγ)) =
      objectClass (annulus B γ hγ) + objectClass (upperRay B γ (admissible_definable B hγ)) := by
    simpa only [zero_add] using h
  exact (add_right_cancel he).symm

theorem annulus_one (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B) :
    objectClass (annulus B 1 hγ) = 0 := class_empty _ GammaRadiusAnnulus.annulus_one

end DiamondIntegral.Section4.GammaOrdinaryRadius
