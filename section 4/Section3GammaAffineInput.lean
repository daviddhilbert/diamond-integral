import «section 4».GammaRationalAffineContinuity

/-! Replaceable Section 3 background: finite rational-affine normal
forms for original-base definable Gamma maps. This is the pure divisible
ordered-group/QE normal form used in the Section 3 Gamma analysis.
The author permits unformalized Section 3 results as given for now.
No continuity, cell decomposition or Euler conclusion is an input. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.Section3GammaAffineInput
open GammaDefinableMaps GammaRationalAffineContinuity
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def Input (B : Base (M := M)) : Prop :=
  ∀ (n : ℕ) (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)),
    MapDefinable B T → ∃ m : ℕ, ∃ branch : Fin m → Branch B n,
      ∀ x, ∃ i, T x = (branch i).eval x

end DiamondIntegral.Section4.Section3GammaAffineInput
