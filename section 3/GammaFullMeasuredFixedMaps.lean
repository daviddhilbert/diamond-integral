import «section 3».GammaFullMeasuredBijections
import «section 3».GammaVFIdentityJacobian

/-! Full Gamma comparisons that fix the VF tuple preserve measure exactly
when they preserve the given Gamma forms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaFullMeasuredFixedVF {U V : GammaGroundMeasuredVFData hc B k}
    (f : GammaGroundBijection U.domain V.domain)
    (hVF : ∀ p, (f.map p).val.1 = p.val.1)
    (hω : ∀ p, gammaGroundMeasuredVFWeight U p = gammaGroundMeasuredVFWeight V (f.map p)) :
    GammaFullMeasuredBijection U V :=
  ⟨f,fun p hp => ⟨1,gammaVFFixed_jacobian_one hκ hs hr hv f.map hVF p hp,
    by rw [map_one,mul_one]; exact hω p⟩⟩

end DiamondIntegral.Section3
