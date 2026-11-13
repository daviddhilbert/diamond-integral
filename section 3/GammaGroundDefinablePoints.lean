import «section 3».GammaGroundConstants
import «section 3».GammaGroundBijections
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M}

/-- Any two actual definable singleton domains are bijective over the
same original Gamma ground, regardless of their tuple presentations. -/
def gammaGroundDefinablePointBijection
    (A : GammaGroundDefSet hc B Q) (D : GammaGroundDefSet hc B R)
    (a : A) (d : D) (hA : ∀ x : A, x = a) (hD : ∀ x : D, x = d) : GammaGroundBijection A D := by
  have he : D.carrier = {d.val} := by
    ext x
    constructor
    · intro hx
      exact congrArg Subtype.val (hD ⟨x,hx⟩)
    · intro hx
      exact hx.symm ▸ d.property
  have hd : GammaGroundDefinable hc B R {d.val} := he ▸ D.definable
  let f := (GammaGroundMap.const (R := R) A d.val hd).corestrict (fun _ => d.property)
  refine ⟨f,?_,?_⟩
  · intro x y _
    exact (hA x).trans (hA y).symm
  · intro y
    exact ⟨a,(hD y).symm⟩
end DiamondIntegral.Section3
