import «section 4».GammaFibreIntegralCongruence
import «section 4».GammaIteratedIntegral

/-! Finite-dimensional actual integration is independent of the base
presentation of its integer function. All smallness premises are explicit. -/

set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaIntegralCongruence
open GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies GammaIteratedIntegral
open GammaFibreIntegralCongruence

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integrateAll_congr (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B C : Base (M := M)) (hrB : Cardinal.mk B.real < κ) (hγB : Cardinal.mk B.gamma < κ)
    (hrC : Cardinal.mk C.real < κ) (hγC : Cardinal.mk C.gamma < κ)
    (k : EulerKind) (n : ℕ) (f : familySubgroup B n) (g : familySubgroup C n)
    (he : ∀ z, f.val z = g.val z) :
    integrateAll h00 hκ hs B hrB hγB k n f = integrateAll h00 hκ hs C hrC hγC k n g := by
  induction n with
  | zero => exact he emptyTuple
  | succ n ih =>
    apply ih (integrateFirst h00 hκ hs B hrB hγB k n f) (integrateFirst h00 hκ hs C hrC hγC k n g)
    intro y
    exact integralFirst_congr h00 B C k f.val f.property g.val g.property y y (fun x => he (Fin.cons x y))

end DiamondIntegral.Section4.GammaIntegralCongruence
