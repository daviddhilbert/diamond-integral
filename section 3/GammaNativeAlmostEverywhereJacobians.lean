import «section 3».GammaJacobianOneExceptionalDescent
import «section 3».GammaFullMeasuredBijections
import «section 3».GammaNativePullbackMeasuredLift
import Section9.SpecialJacobianGeneric
import Integration7.VFAlmostEverywhere

/-! The RV-density proof's intrinsic Jacobian-one statements apply at
the original Gamma ground, even when their real presentation has more
parameters. Arbitrary Gamma forms then pass through the same actual map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNative_jacobian_one_of_almostEverywhere
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n b}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (f : SpecialTransformations.Section5.Map A D) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f))
    (hJ : VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1))
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA)
    (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) :
    HasMixedVFJacobianAt (Section5.nativeGammaPointBijection hA hD
      (⟨Equiv.ofBijective f hf,hF⟩ : GammaIso B (carrier A) (carrier D))).map p 1 := by
  obtain ⟨Z,hZA,hZ,hJ⟩ := hJ
  apply gammaGround_jacobian_one_of_small_exception C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv hn _ Z.carrier
    ((vf_small_iff_companion hc C.saturated C.small hv hn Z).mpr hZ) _ p hp
  intro q hq
  obtain ⟨F,⟨ρ,hρ⟩,hFJ⟩ := hJ ⟨q.val,q.property⟩ hq
  refine ⟨F,⟨ρ,fun x hx => ?_⟩,hFJ⟩
  obtain ⟨hxA,hxF⟩ := hρ x hx
  refine ⟨hxA,?_⟩
  rw [Section5.nativeGammaPointBijection_apply,Section5.nativeGammaPointBijection_apply]
  exact hxF

def gammaFullMeasuredOfJacobianOne
    {U V : GammaGroundMeasuredVFData hc B n} (f : GammaGroundBijection U.domain V.domain)
    (hJ : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 → HasMixedVFJacobianAt f.map p 1)
    (hWeight : ∀ p, gammaGroundMeasuredVFWeight U p = gammaGroundMeasuredVFWeight V (f.map p)) :
    GammaFullMeasuredBijection U V :=
  ⟨f,fun p hp => ⟨1,hJ p hp,by rw [map_one,mul_one]; exact hWeight p⟩⟩

end DiamondIntegral.Section3
