import «section 3».GammaFullMeasuredBijections

/-! A literal Gamma-definable restriction of a full measured bijection
retains its generic Jacobian measure identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
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

def gammaFullMeasuredRestriction {U V : GammaGroundMeasuredVFData hc B k}
    (f : GammaFullMeasuredBijection U V)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) k U.arity)) (hA : A.carrier ⊆ U.domain.carrier)
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) k V.arity)) (hD : D.carrier ⊆ V.domain.carrier)
    (g : GammaGroundBijection A D)
    (he : ∀ p, (g.map p).val = (f.map.map ⟨p.val,hA p.property⟩).val) :
    GammaFullMeasuredBijection (U.restrict A hA) (V.restrict D hD) where
  map := g
  measure := by
    intro p hp
    let i : A → U.domain := fun q => ⟨q.val,hA q.property⟩
    obtain ⟨L,hL⟩ := gammaGround_differentiable_of_independent hκ hs hr hv g.map p hp
    obtain ⟨F,hF,hFL⟩ := hL
    let K := (LinearMap.toMatrix' L).det
    have hK : HasMixedVFJacobianAt g.map p K := ⟨F,hF,hFL.hasJacobianAt⟩
    obtain ⟨J,hJ,hw⟩ := f.measure (i p) hp
    have hJK := mixedJacobian_eq_of_restriction f.map.map g.map i (fun _ => rfl) he p hJ hK
    refine ⟨K,hK,?_⟩
    change gammaGroundMeasuredVFWeight U (i p) =
      gammaGroundMeasuredVFWeight V ⟨(g.map p).val,hD (g.map p).property⟩ * Values.vfValueHom K
    rw [hw,hJK]
    congr 2
    exact Subtype.ext (he p).symm

end DiamondIntegral.Section3
