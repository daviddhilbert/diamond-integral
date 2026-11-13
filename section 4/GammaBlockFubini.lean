import «section 4».GammaPrefixIntegration
import «section 4».FiniteTupleSwap

/-! Fubini for two arbitrary finite coordinate blocks of the actual
integer-family integral. Prefix integration already identifies the inner
values with actual fibres over their named parameter tuples. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBlockFubini
open GammaIntegerFamilies GammaIteratedIntegral GammaCoordinatePullback GammaPrefixIntegration
open GammaFubiniPermutation FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem block_fubini (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n m : ℕ)
    (f : familySubgroup B (n + m)) :
    integrateAll h00 hκ hs B hr hγ k n (integratePrefix h00 hκ hs B hr hγ k n m f) =
      integrateAll h00 hκ hs B hr hγ k m
        (integratePrefix h00 hκ hs B hr hγ k m n (pullback B (blockSwap n m) f)) := by
  have hleft := congrArg (fun H => H f) (integrateAll_factor h00 hκ hs B hr hγ k n m)
  have hright := congrArg (fun H => H (pullback B (blockSwap n m) f))
    (integrateAll_factor h00 hκ hs B hr hγ k m n)
  exact hleft.symm.trans
    ((integrateAll_equiv h00 hκ hs B hr hγ k linear hΓ (n + m) (m + n) (blockSwap n m) f).symm.trans hright)

end DiamondIntegral.Section4.GammaBlockFubini
