import «section 3».GammaSpecialDensityTransport
import «section 3».GammaSpecialJacobian

/-! The actual original-ground point bijection attached to a special
chain has Jacobian one at every independent source point. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n m l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hκ hs hr hv in
theorem gammaNativeSpecial_jacobian_one
    {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    {D : SpecialTransformations.Section5.DefSet (M := M) S n l}
    (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) (GammaChainDefinable.source B T.chain hT))
    (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) :
    HasMixedVFJacobianAt (gammaNativeSpecialBijection T hT).map p 1 := by
  let F := gammaNativeSpecialBijection (hc := hc) T hT
  let a : A := ⟨p.val,p.property⟩
  obtain ⟨L,hL,hdet⟩ := gammaSpecialChain_jacobian_one hc hκ hs hr hv T.chain hT a hp
  have hJ : HasMixedVFJacobianAt T.toMap a 1 := by
    obtain ⟨H,hH,hHL⟩ := hL
    exact ⟨H,hH,by simpa only [hdet] using hHL.hasJacobianAt⟩
  obtain ⟨H,⟨ρ,hρ⟩,hH⟩ := hJ
  refine ⟨H,⟨ρ,fun x hx => ?_⟩,hH⟩
  obtain ⟨ha,hf⟩ := hρ x hx
  refine ⟨ha,?_⟩
  rw [gammaNativeSpecialBijection_apply,gammaNativeSpecialBijection_apply]
  exact hf

end DiamondIntegral.Section3
