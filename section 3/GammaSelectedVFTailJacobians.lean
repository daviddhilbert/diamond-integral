import «section 3».GammaSelectedVFTailGroundMaps
import «section 3».MixedVFTailJacobians
import «section 3».GammaGroundDifferentiation

/-! The actual selected-RV VF-tail bijection has the same Jacobian as
the original map at its projected point. Generic differentiability on
the selected domain and the checked restriction identity avoid imposing
any auxiliary openness, finite-label or resolved-base hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a b k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (A : DefSet (M := M) S n a) (ρ : Fin k → Fin a) (hA : GammaSetDefinable B (carrier A))
variable {D : DefSet (M := M) S n b} (σ : Fin k → Fin b) (hD : GammaSetDefinable B (carrier D))
variable (f : Map A D) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
variable (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ)

theorem gammaSelectedVFTail_jacobian
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (p : gammaSelectedVFTailDomain (hc := hc) A ρ hA)
    (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) (J : Section2.VF M)
    (hJ : HasMixedVFJacobianAt
      (Section5.nativeGammaPointBijection (hc := hc) hA hD
        (⟨Equiv.ofBijective f hf,hΓ⟩ : GammaIso B (carrier A) (carrier D))).map
      (gammaSelectedVFTailProjection A ρ hA p) J) :
    HasMixedVFJacobianAt (gammaSelectedVFTailBijection A ρ hA σ hD f hf hΓ hLabels).map p J := by
  let e : GammaIso B (carrier A) (carrier D) := ⟨Equiv.ofBijective f hf,hΓ⟩
  let f₀ := Section5.nativeGammaPointBijection (hc := hc) hA hD e
  let F := gammaSelectedVFTailBijection (hc := hc) A ρ hA σ hD f hf hΓ hLabels
  let i : gammaSelectedVFTailDomain (hc := hc) A ρ hA → mixedVFTailSource (carrier A) k :=
    fun q => ⟨q.val,gammaSelectedVFTail_prefix_mem A ρ hA q⟩
  have hBase : HasMixedVFJacobianAt f₀.map (mixedVFTailPrefix (i p)) J := hJ
  have hProduct := mixedVFTailExtension_jacobian f₀.map (i p) J hBase
  have hSame (q : gammaSelectedVFTailDomain (hc := hc) A ρ hA) :
      (F.map q).val = (mixedVFTailExtension f₀.map (i q)).val := by
    have hb := Section5.nativeGammaPointBijection_apply (hc := hc) hA hD e (gammaSelectedVFTailProjection A ρ hA q)
    have hHead := congrArg Prod.fst hb
    have hRV := congrArg Prod.snd hb
    exact (gammaSelectedVFTailBijection_value A ρ hA σ hD f hf hΓ hLabels q).trans
      (Prod.ext (congrArg (fun v => Fin.append v (q.val.1 ∘ Fin.natAdd n)) hHead.symm) hRV.symm)
  obtain ⟨L,hL⟩ := gammaGround_differentiable_of_independent hκ hs hr hv F.map p hp
  have hDet : HasMixedVFJacobianAt F.map p (LinearMap.toMatrix' L).det := by
    obtain ⟨H,hH,hDH⟩ := hL
    exact ⟨H,hH,hDH.hasJacobianAt⟩
  have hEq := mixedJacobian_eq_of_restriction (mixedVFTailExtension f₀.map) F.map i
    (fun _ => rfl) hSame p hProduct hDet
  exact hEq.symm ▸ hDet

end DiamondIntegral.Section3
