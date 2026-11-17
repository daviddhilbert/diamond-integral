import «section 3».GammaGroundDifferentiation
import Section9.PermutationVolumeSigns
import Section9.LimitGeometry

/-! A Gamma map whose VF component is a coordinate permutation has its
actual permutation-sign Jacobian at every original-base independent
point. The value of that sign is one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaGroundVFPermutation_jacobian
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a)}
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n b)}
    (f : GammaGroundMap A D) (σ : Equiv.Perm (Fin n)) (hVF : ∀ q, (f q).val.1 = q.val.1 ∘ σ)
    (p : A) (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) :
    HasMixedVFJacobianAt f p (Equiv.Perm.sign σ : Section2.VF M) := by
  obtain ⟨L,H,⟨ρ,hρ⟩,hHL⟩ := gammaGround_differentiable_of_independent hκ hs hr hv f p hp
  have hChart : IsVFChartAt f p (fun x => x ∘ σ) := by
    refine ⟨ρ,fun x hx => ?_⟩
    obtain ⟨ha,hH⟩ := hρ x hx
    have hRV := congrArg (fun z : Section2.Mixed M n b => z.2) hH
    exact ⟨ha,Prod.ext (hVF ⟨(x,p.val.2),ha⟩) hRV⟩
  have hD : HasVFDerivativeAt (fun x => x ∘ σ) p.val.1 (vfReindexLinear σ) := by
    change HasVFDerivativeAt (fun x => vfReindexLinear σ x) p.val.1 (vfReindexLinear σ)
    simpa only [add_zero] using hasVFDerivativeAt_affine (vfReindexLinear (M := M) σ) 0 p.val.1
  exact ⟨_,hChart,by simpa only [det_vfReindexLinear] using hD.hasJacobianAt⟩

theorem gammaVFPermutationSign_value (σ : Equiv.Perm (Fin n)) :
    Values.vfValueHom (Equiv.Perm.sign σ : Section2.VF M) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · have he : (Equiv.Perm.sign σ : Section2.VF M) = -1 := by simp [h]
    rw [he,vfValue_neg,map_one]

end DiamondIntegral.Section3
