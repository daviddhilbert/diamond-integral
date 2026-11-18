import «section 3».GammaGroundPointIsomorphisms
import «section 5».NativeMixedCoordinateMaps
import Integration7.GammaSelectedRVVFTailMaps

/-! The existing selected-RV VF-tail maps are actual Gamma-ground
bijections with unchanged base and literal coordinate squares. No
choice of representatives enters the map or its inverse. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a b k : ℕ}
variable (A : DefSet (M := M) S n a) (ρ : Fin k → Fin a) (hA : GammaSetDefinable B (carrier A))

def gammaSelectedVFTailDomain :=
  Section5.nativeGammaPointDomain (hc := hc) (carrier (nativeSelectedRVVFTailLift hc A ρ))
    (gamma_native_selected_rv_vf_tail_lift hc A ρ hA)

theorem gammaSelectedVFTail_prefix_mem (p : gammaSelectedVFTailDomain (hc := hc) A ρ hA) :
    (p.val.1 ∘ Fin.castAdd k,p.val.2) ∈ carrier A :=
  ((native_selected_rv_vf_tail_lift_carrier hc A ρ p.val).mp p.property).1

def gammaSelectedVFTailProjection :
    GammaGroundMap (gammaSelectedVFTailDomain (hc := hc) A ρ hA) (Section5.nativeGammaPointDomain (carrier A) hA) :=
  (Section5.nativeMixedCoordinateMap (gammaSelectedVFTailDomain (hc := hc) A ρ hA)
    (Fin.castAdd k) (id : Fin a → Fin a)).corestrict (fun p => gammaSelectedVFTail_prefix_mem A ρ hA p)

theorem gammaSelectedVFTailProjection_value (p : gammaSelectedVFTailDomain (hc := hc) A ρ hA) :
    (gammaSelectedVFTailProjection A ρ hA p).val = (p.val.1 ∘ Fin.castAdd k,p.val.2) := rfl

variable {D : DefSet (M := M) S n b} (σ : Fin k → Fin b) (hD : GammaSetDefinable B (carrier D))
variable (f : Map A D) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
variable (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ)

def gammaSelectedVFTailBijection :
    GammaGroundBijection (gammaSelectedVFTailDomain (hc := hc) A ρ hA) (gammaSelectedVFTailDomain D σ hD) :=
  Section5.nativeGammaPointBijection _ _
    (⟨Equiv.ofBijective (nativeSelectedRVVFTailMap hc f ρ σ hLabels)
      (native_selected_rv_vf_tail_map_bijective hc f hf ρ σ hLabels),
      gamma_native_selected_rv_vf_tail_map hc f ρ σ hLabels hA hΓ⟩ :
        GammaIso B (carrier (nativeSelectedRVVFTailLift hc A ρ)) (carrier (nativeSelectedRVVFTailLift hc D σ)))

theorem gammaSelectedVFTailBijection_value
    (p : gammaSelectedVFTailDomain (hc := hc) A ρ hA) :
    ((gammaSelectedVFTailBijection A ρ hA σ hD f hf hΓ hLabels).map p).val =
      (Fin.append (f ⟨(p.val.1 ∘ Fin.castAdd k,p.val.2),gammaSelectedVFTail_prefix_mem A ρ hA p⟩).val.1
        (p.val.1 ∘ Fin.natAdd n),
       (f ⟨(p.val.1 ∘ Fin.castAdd k,p.val.2),gammaSelectedVFTail_prefix_mem A ρ hA p⟩).val.2) := by
  exact Section5.nativeGammaPointBijection_apply _ _ _ p

end DiamondIntegral.Section3
