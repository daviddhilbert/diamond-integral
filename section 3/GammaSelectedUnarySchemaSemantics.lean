import «section 3».GammaMeasuredSelectedBounds
import «section 3».GammaSelectedVFTailGroundMaps

/-! The selected unary Gamma schema has the exact source and density
identities required by the existing prepared-family construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a k : ℕ}
variable (U : DefSet (M := M) Set.univ 1 a) (hU : GammaSetDefinable B (carrier U)) (ρ : Fin (k+1) → Fin a)
variable (Ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU)) (N : ℕ)

theorem gammaSelectedUnarySchema_source
    (x : Fin 1 → Section2.VF M) (y : Fin (k+1) → Section2.VF M) (r : Fin a → RV (M := M)) :
    (Fin.append x y,r) ∈ carrier (nativeSelectedRVVFTailLift hc U ρ) ↔
      (gammaMeasuredBoundedSelectedSchema U hU ρ Ω N).object.rowVolume (vfValues x) r (Section2.tupleRV M y) := by
  have hSel := native_selected_rv_vf_tail_lift_carrier hc U ρ (Fin.append x y,r)
  have hHead : Fin.append x y ∘ Fin.castAdd (k+1) = x := by funext j; exact Fin.append_left _ _ j
  have hTail : Fin.append x y ∘ Fin.natAdd 1 = y := by funext j; exact Fin.append_right _ _ j
  rw [hHead,hTail] at hSel
  have hVol := gammaSelectedLabelSchema_volume U hU ρ x r (Section2.tupleRV M y)
  exact hSel.trans ((and_congr Iff.rfl eq_comm).trans hVol.symm)

theorem gammaSelectedUnarySchema_density
    (p : gammaSelectedVFTailDomain (hc := hc) U ρ hU) (c : (volumeGammaSpace hc).domain)
    (hcValue : (volumeGammaSpace hc).decode c = ((Ω.comp (gammaSelectedVFTailProjection U ρ hU)) p).val) :
    (gammaMeasuredBoundedSelectedSchema U hU ρ Ω N).rowDensity
      (vfValues (p.val.1 ∘ Fin.castAdd (k+1))) p.val.2 c := by
  exact (gammaMeasuredSelectedSchema_density U hU ρ Ω (p.val.1 ∘ Fin.castAdd (k+1)) p.val.2 c).mpr
    ⟨gammaSelectedVFTailProjection U ρ hU p,rfl,hcValue.symm⟩

end DiamondIntegral.Section3
