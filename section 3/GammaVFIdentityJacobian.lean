import «section 3».GammaMeasuredArrowLift

/-! An original-ground map that fixes its VF tuple has actual Jacobian
one at independent points, irrespective of its auxiliary RV recoding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hκ hs hr hv in
theorem gammaVFFixed_jacobian_one
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n s)}
    (f : GammaGroundMap A D) (hf : ∀ a, (f a).val.1 = a.val.1)
    (a : A) (ha : AlgebraicIndependent (vfParameterField B.real) a.val.1) :
    HasMixedVFJacobianAt f a 1 := by
  obtain ⟨L,H,⟨ρ,hρ⟩,hHL⟩ := gammaGround_differentiable_of_independent hκ hs hr hv f a ha
  have hchart : IsVFChartAt f a (fun x => x) := by
    refine ⟨ρ,fun x hx => ?_⟩
    obtain ⟨hp,hH⟩ := hρ x hx
    have hRV := congrArg (fun q : Section2.Mixed M n s => q.2) hH
    exact ⟨hp,Prod.ext (hf ⟨(x,a.val.2),hp⟩) hRV⟩
  have hId : HasVFDerivativeAt (fun x : Fin n → Section2.VF M => x) a.val.1 LinearMap.id := by
    simpa only [LinearMap.id_apply,add_zero] using
      hasVFDerivativeAt_affine (LinearMap.id : (Fin n → Section2.VF M) →ₗ[Section2.VF M] (Fin n → Section2.VF M)) 0 a.val.1
  exact ⟨_,hchart,by simpa only [LinearMap.toMatrix'_id,Matrix.det_one] using hId.hasJacobianAt⟩

end DiamondIntegral.Section3
