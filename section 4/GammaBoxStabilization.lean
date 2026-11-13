import «section 4».GammaSymmetricTruncation
import «section 4».GammaPushforwardCongruence

/-! Full finite-dimensional symmetric-box stabilization. The truncation
radius is arbitrary, and is named only in an explicit finite base extension.
The stabilized value is the original-base bounded Euler integral. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoxStabilization
open GammaDefinableEuler GammaIntegerFamilies GammaIteratedIntegral GammaProductFamilies
open GammaParameterExtension GammaRadius GammaRadiusProfiles GammaSymmetricTruncation
open GammaPushforwardCongruence GammaBaseExtension

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def radiusBase (B : Base (M := M)) (r : Values.Gamma (M := M)) : Base (M := M) :=
  withGamma B (Set.range ![r])

theorem radius_name (B : Base (M := M)) (r : Values.Gamma (M := M)) :
    GammaDefinableClosureAtBase (radiusBase B r) r :=
  gammaName_extend B (Set.range ![r]) r (Set.mem_range_self (0 : Fin 1))

def boxTruncation (B : Base (M := M)) {n : ℕ} (f : familySubgroup B n) (r : Values.Gamma (M := M)) :
    familySubgroup (radiusBase B r) n :=
  truncateFamily (radiusBase B r) (extendFamily B (Set.range ![r]) f) r (radius_name B r)

theorem boxTruncation_eval (B : Base (M := M)) {n : ℕ} (f : familySubgroup B n)
    (r : Values.Gamma (M := M)) (hr : 1 ≤ r) (z : Fin n → Values.Gamma (M := M)) :
    (boxTruncation B f r).val z = if ∀ i, r⁻¹ ≤ z i ∧ z i ≤ r then f.val z else 0 :=
  truncateFamily_eval (radiusBase B r) (extendFamily B (Set.range ![r]) f) r (radius_name B r) hr z

theorem box_stabilization (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (n : ℕ) (f : familySubgroup B n) :
    ∃ R : Values.Gamma (M := M), 1 < R ∧ ∀ r, R ≤ r →
      integrateAll h00 hκ hs (radiusBase B r) hr (finite_gamma_extension_small hκ B hγ ![r])
        EulerKind.geometric n (boxTruncation B f r) =
      integrateAll h00 hκ hs B hr hγ EulerKind.bounded n f := by
  obtain ⟨R, hR, hstable⟩ := radiusProfile_stabilization h00 linear hκ hs B hr hγ hΓ n f
  refine ⟨toPaperGamma.symm R, ?_, ?_⟩
  · change 0 < toPaperGamma (toPaperGamma.symm R)
    rwa [toPaperGamma.apply_symm_apply]
  · intro r hrR
    let C := radiusBase B r
    have hγC : Cardinal.mk C.gamma < κ := finite_gamma_extension_small hκ B hγ ![r]
    have hΓC : Section2.NontrivialDefinableGamma C := nontrivial_extend B (Set.range ![r]) hΓ
    let f' := extendFamily B (Set.range ![r]) f
    have hprofile : (radiusProfile h00 hκ hs C hr hγC EulerKind.geometric n f').val =
        (radiusProfile h00 hκ hs B hr hγ EulerKind.geometric n f).val :=
      pushforward_congr h00 hκ hs C B hr hγC hr hγ EulerKind.geometric
        (radius n) (radius n) (radius_graph_definable C n) (radius_graph_definable B n) f' f
        (fun _ => rfl) (fun _ => rfl)
    have htrunc := integral_truncateFamily h00 linear hκ hs C hr hγC hΓC EulerKind.geometric
      f' r (radius_name B r)
    change integrateAll h00 hκ hs C hr hγC EulerKind.geometric n
      (truncateFamily C f' r (radius_name B r)) = _
    rw [htrunc, hprofile]
    apply hstable (toPaperGamma r)
    change toPaperGamma (toPaperGamma.symm R) ≤ toPaperGamma r at hrR
    rwa [toPaperGamma.apply_symm_apply] at hrR

end DiamondIntegral.Section4.GammaBoxStabilization
