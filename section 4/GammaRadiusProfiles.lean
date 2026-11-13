import «section 4».GammaRadius
import «section 4».GammaHigherPushforward
import «section 4».EulerTruncation

/-! Radius fibres are bounded, so both Euler theories give the same
actual radius profile. Unary stabilization of that profile recovers the
bounded integral of the original finite-dimensional family. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRadiusProfiles
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaIntegerFamilies GammaIteratedIntegral
open GammaHigherPushforward GammaRadius GammaBoundedFamilies GammaParameterExtension EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem radius_graph_definable (B : Base (M := M)) (n : ℕ) :
    GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = radius n (Fin.tail z)} := by
  have h := radius_definable B n
  unfold MapDefinable at h
  convert h using 1
  ext z
  change z 0 = radius n (Fin.tail z) ↔ z 0 = radius n (fun i => z i.succ)
  have he : Fin.tail z = (fun i => z i.succ) := by funext i; rfl
  rw [he]

theorem radius_fibre_bounded (B : Base (M := M)) (n : ℕ) (f : familySubgroup B n)
    (a : Values.Gamma (M := M)) :
    BoxSupported a⁻¹ a (fibreFamily B (radius n) (radius_graph_definable B n) f a).val := by
  intro u hu i
  have hval := fibreFamily_eval B (radius n) (radius_graph_definable B n) f a u
  have he : radius n u = a := by
    by_contra hn
    exact hu (hval.trans (ite_eq_right hn))
  simpa only [he] using radius_bounds n u i

def radiusProfile (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) : familySubgroup B n →+ GammaDefinableConvolution.baseSubgroup B k :=
  pushforward h00 hκ hs B hr hγ k (radius n) (radius_graph_definable B n)

theorem radiusProfile_changeKind (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k l : EulerKind) (n : ℕ) (f : familySubgroup B n) :
    changeKind k l (radiusProfile h00 hκ hs B hr hγ k n f).val =
      (radiusProfile h00 hκ hs B hr hγ l n f).val := by
  apply eval_injective l
  funext x
  obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
  change changeKind k l (pushforward h00 hκ hs B hr hγ k _ _ f).val (toPaperGamma a) =
    (pushforward h00 hκ hs B hr hγ l _ _ f).val (toPaperGamma a)
  rw [changeKind_eval, pushforward_eval, pushforward_eval]
  exact integrateAll_bounded_comparison h00 hκ hs (GammaBaseExtension.withGamma B (Set.range ![a])) hr
    (finite_gamma_extension_small hκ B hγ ![a]) k l n _ a⁻¹ a (radius_fibre_bounded B n f a)

theorem radiusProfile_stabilization (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (n : ℕ) (f : familySubgroup B n) :
    ∃ R : PaperGamma (M := M), 0 < R ∧ ∀ r, R ≤ r →
      totalEuler EulerKind.geometric
        (truncate EulerKind.geometric (-r) r (radiusProfile h00 hκ hs B hr hγ EulerKind.geometric n f).val) =
      integrateAll h00 hκ hs B hr hγ EulerKind.bounded n f := by
  obtain ⟨R, hR, hstable⟩ := boundedEuler_stabilization
    (radiusProfile h00 hκ hs B hr hγ EulerKind.geometric n f).val
  refine ⟨R, hR, ?_⟩
  intro r hrR
  rw [hstable r hrR, radiusProfile_changeKind]
  exact pushforward_integral h00 hκ hs B hr hγ EulerKind.bounded linear hΓ _ _ f

end DiamondIntegral.Section4.GammaRadiusProfiles
