import «section 3».GammaMeasuredArrowLift

/-! Actual Gamma bijections satisfying the generic Jacobian measure
identity are closed under composition and inversion. No germ representative
or density choice is substituted for the given full map. -/
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

structure GammaFullMeasuredBijection (U V : GammaGroundMeasuredVFData hc B k) where
  map : GammaGroundBijection U.domain V.domain
  measure : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
    ∃ J : Section2.VF M, HasMixedVFJacobianAt map.map p J ∧
      gammaGroundMeasuredVFWeight U p = gammaGroundMeasuredVFWeight V (map.map p) * Values.vfValueHom J

namespace GammaFullMeasuredBijection
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {U V W : GammaGroundMeasuredVFData hc B k}

def comp (f : GammaFullMeasuredBijection U V) (g : GammaFullMeasuredBijection V W) :
    GammaFullMeasuredBijection U W where
  map := g.map.comp f.map
  measure := by
    intro p hp
    obtain ⟨J,K,hJ,hK,hC⟩ := gammaGround_jacobian_comp_of_independent hκ hs hr hv
      f.map.map g.map.map (GammaGroundMap.finiteFibres_of_injective f.map.bijective.injective) p hp
    obtain ⟨L,hL,hw⟩ := f.measure p hp
    obtain ⟨D,hD,hwg⟩ := g.measure (f.map.map p)
      (gammaGround_independent_map f.map.map (GammaGroundMap.finiteFibres_of_injective f.map.bijective.injective) hκ hr p hp)
    rw [hL.unique hJ] at hw
    rw [hD.unique hK] at hwg
    refine ⟨K*J,hC,?_⟩
    change gammaGroundMeasuredVFWeight U p =
      gammaGroundMeasuredVFWeight W (g.map.map (f.map.map p)) * Values.vfValueHom (K*J)
    rw [hw,hwg,map_mul,mul_assoc]

def symm (f : GammaFullMeasuredBijection U V) : GammaFullMeasuredBijection V U where
  map := f.map.symm
  measure := by
    intro p hp
    let q := f.map.symm.map p
    have hq := gammaGround_independent_map f.map.symm.map
      (GammaGroundMap.finiteFibres_of_injective f.map.symm.bijective.injective) hκ hr p hp
    obtain ⟨J,K,hJ,hK,hprod⟩ := gammaGround_jacobian_inverse_of_independent hκ hs hr hv f.map q hq
    have he : f.map.map q = p := f.map.map.apply_inverse f.map.bijective p
    rw [he] at hK
    obtain ⟨L,hL,hw⟩ := f.measure q hq
    rw [hL.unique hJ,he] at hw
    refine ⟨K,hK,?_⟩
    change gammaGroundMeasuredVFWeight V p = gammaGroundMeasuredVFWeight U q * Values.vfValueHom K
    rw [hw,mul_assoc,← map_mul,mul_comm J K,hprod,map_one,mul_one]

end GammaFullMeasuredBijection
end DiamondIntegral.Section3
