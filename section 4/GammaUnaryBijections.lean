import «section 4».GammaPowerLawBijections
import «section 2».CitedGammaLinearity

/-! Unary Euler invariance for actual definable bijections, relative only
to the already-authorized replaceable Gamma-linearity background from
[18, proof of Lemma 3.18]. The Euler and Fubini arguments are proved here.
The original base is retained in the conclusion. -/

set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUnaryBijections
open GammaOrderLogic GammaBaseExtension GammaEulerSets GammaPowerLawBijections

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def commonBase (B : Base (M := M)) : Base (M := M) := ⟨commonRealNames B, ∅⟩

theorem nontrivial_commonBase (B : Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B) :
    Section2.NontrivialDefinableGamma (commonBase B) := by
  obtain ⟨γ, δ, hγ, hδ, hne⟩ := hΓ
  refine ⟨γ, δ, ?_, ?_, hne⟩
  · have hr : Values.GammaDefinable (commonRealNames B) {γ} := DefinableAtBase.common_names hγ
    exact real_definableAtBase (commonBase B) .rv _ hr
  · have hr : Values.GammaDefinable (commonRealNames B) {δ} := DefinableAtBase.common_names hδ
    exact real_definableAtBase (commonBase B) .rv _ hr

theorem unary_bijection_invariance (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (B : Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (D E : Set (Values.Gamma (M := M))) (hD : GammaDefinableOverBase B D)
    (hE : GammaDefinableOverBase B E) (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 ∈ D ∧ T (z 0) = z 1})
    (hinj : Set.InjOn T D) (hrange : T '' D = E) :
    eulerValue h00 B k D hD = eulerValue h00 B k E hE := by
  have hTc := to_common_real_syntax B _ hT
  obtain ⟨m, p, q, c, hq, hcover⟩ := linear h00 (commonRealNames B) (nontrivial_commonBase B hΓ) D T hTc
  exact power_law_bijection_invariance h00 B k D E hD hE T hT hinj hrange p q c hq hcover

end DiamondIntegral.Section4.GammaUnaryBijections
