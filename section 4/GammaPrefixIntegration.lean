import «section 4».GammaFubiniPermutation
import «section 4».GammaBlockSlices

/-! Repeated integration of a prefix is original-base definable and is
equal, at every parameter, to the actual integral over that fibre. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPrefixIntegration
open GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies GammaIteratedIntegral
open GammaFibreIntegralCongruence GammaParameterExtension GammaBlockSlices FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
  (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
  (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
  (k : EulerKind)

def integratePrefix (n : ℕ) : (m : ℕ) → familySubgroup B (n + m) →+ familySubgroup B n
  | 0 => AddMonoidHom.id _
  | m + 1 => (integratePrefix n m).comp (integrateFirst h00 hκ hs B hr hγ k (n + m))

theorem integrateAll_factor (n m : ℕ) :
    integrateAll h00 hκ hs B hr hγ k (n + m) =
      (integrateAll h00 hκ hs B hr hγ k n).comp (integratePrefix h00 hκ hs B hr hγ k n m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (integrateAll h00 hκ hs B hr hγ k (n + m)).comp _ = _
    rw [ih]
    rfl

theorem integratePrefix_fibre (n m : ℕ) (f : familySubgroup B (n + m))
    (y : Fin n → Values.Gamma (M := M)) :
    (integratePrefix h00 hκ hs B hr hγ k n m f).val y =
      integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range y)) hr
        (finite_gamma_extension_small hκ B hγ y) k m
        ⟨slice f.val y, slice_definable B n m f.val f.property y⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    let B' := GammaBaseExtension.withGamma B (Set.range y)
    have hγ' : Cardinal.mk B'.gamma < κ := finite_gamma_extension_small hκ B hγ y
    have hf : IntegerFamilyDefinable B f.val := f.property
    let g := integrateFirst h00 hκ hs B hr hγ k (n + m) f
    have hg : IntegerFamilyDefinable B g.val := g.property
    have hslice := slice_definable B n (m + 1) f.val hf y
    have he : (⟨slice g.val y, slice_definable B n m g.val hg y⟩ : familySubgroup B' m) =
        integrateFirst h00 hκ hs B' hr hγ' k m ⟨slice f.val y, hslice⟩ := by
      apply Subtype.ext
      funext u
      change integralFirst h00 B k f.val hf (join n m u y) =
        integralFirst h00 B' k (slice f.val y) hslice u
      apply integralFirst_congr h00 B B' k f.val hf (slice f.val y) hslice (join n m u y) u
      intro a
      rfl
    change (integratePrefix h00 hκ hs B hr hγ k n m g).val y = _
    rw [ih g, he]
    rfl

end DiamondIntegral.Section4.GammaPrefixIntegration
