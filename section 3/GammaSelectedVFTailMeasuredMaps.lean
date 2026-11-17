import «section 3».GammaSelectedVFTailJacobians
import «section 3».GammaFullMeasuredBijections

/-! Realizing selected RV coordinates by VF tails preserves the given
generic Gamma measure equation. The original unary domains may have
infinite RV fibres; finiteness after fixing the selected labels suffices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a b k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaSelectedVFTailMeasuredData
    (A : DefSet (M := M) S n a) (ρ : Fin k → Fin a) (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA)) :
    GammaGroundMeasuredVFData hc B (n+k) :=
  ⟨a,gammaSelectedVFTailDomain A ρ hA,native_selected_rv_vf_tail_lift_finite_labels hc A ρ hfin,
    ω.comp (gammaSelectedVFTailProjection A ρ hA)⟩

def gammaSelectedVFTailFullMeasured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (M := M) S n a) (D : DefSet (M := M) S n b)
    (ρ : Fin k → Fin a) (σ : Fin k → Fin b)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (f : Map A D) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ)
    (hfinA : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hfinD : ∀ x t, {r | (x,r) ∈ carrier D ∧ r ∘ σ = t}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (η : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier D) hD))
    (hMeasure : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      ∃ J : Section2.VF M, HasMixedVFJacobianAt
        (Section5.nativeGammaPointBijection (hc := hc) hA hD (⟨Equiv.ofBijective f hf,hΓ⟩ : GammaIso B (carrier A) (carrier D))).map p J ∧
        (gammaGroundFormValue ω p).val =
          (gammaGroundFormValue η ((Section5.nativeGammaPointBijection (hc := hc) hA hD
            (⟨Equiv.ofBijective f hf,hΓ⟩ : GammaIso B (carrier A) (carrier D))).map p)).val * Values.vfValueHom J) :
    GammaFullMeasuredBijection (gammaSelectedVFTailMeasuredData A ρ hA hfinA ω)
      (gammaSelectedVFTailMeasuredData D σ hD hfinD η) where
  map := gammaSelectedVFTailBijection A ρ hA σ hD f hf hΓ hLabels
  measure := by
    intro p hp
    let p₀ := gammaSelectedVFTailProjection A ρ hA p
    have hp₀ : AlgebraicIndependent (vfParameterField B.real) p₀.val.1 :=
      hp.comp (Fin.castAdd k) (Fin.castAdd_injective n k)
    obtain ⟨J,hJ,hw⟩ := hMeasure p₀ hp₀
    refine ⟨J,gammaSelectedVFTail_jacobian A ρ hA σ hD f hf hΓ hLabels hκ hs hr hv p hp J hJ,?_⟩
    let e : GammaIso B (carrier A) (carrier D) := ⟨Equiv.ofBijective f hf,hΓ⟩
    let f₀ := Section5.nativeGammaPointBijection (hc := hc) hA hD e
    let F := gammaSelectedVFTailBijection (hc := hc) A ρ hA σ hD f hf hΓ hLabels
    have hComm : gammaSelectedVFTailProjection D σ hD (F.map p) = f₀.map p₀ := by
      apply Subtype.ext
      have hSel := gammaSelectedVFTailBijection_value A ρ hA σ hD f hf hΓ hLabels p
      have hBase := Section5.nativeGammaPointBijection_apply (hc := hc) hA hD e p₀
      change ((F.map p).val.1 ∘ Fin.castAdd k,(F.map p).val.2) = (f₀.map p₀).val
      rw [hSel]
      have hMid :
          (Fin.append (f ⟨p₀.val,p₀.property⟩).val.1 (p.val.1 ∘ Fin.natAdd n) ∘ Fin.castAdd k,
            (f ⟨p₀.val,p₀.property⟩).val.2) = (f ⟨p₀.val,p₀.property⟩).val := by
        apply Prod.ext
        · funext j
          exact Fin.append_left _ _ j
        · rfl
      exact hMid.trans hBase.symm
    change (gammaGroundFormValue ω p₀).val =
      (gammaGroundFormValue η (gammaSelectedVFTailProjection D σ hD (F.map p))).val * Values.vfValueHom J
    rw [hComm]
    exact hw

end DiamondIntegral.Section3
