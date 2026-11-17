import «section 3».GammaGroundDifferentiation

/-! At an original-base independent point, two actual Gamma maps with
identical VF components have the same mixed VF Jacobian. Their RV labels
may differ; generic differentiability supplies each literal fixed-label
chart separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n a b c : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaGroundJacobian_transfer_VF
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a)}
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n b)}
    {E : GammaGroundDefSet hc B (rawMixedSpace (M := M) n c)}
    (f : GammaGroundMap A D) (g : GammaGroundMap A E)
    (hVF : ∀ p, (f p).val.1 = (g p).val.1)
    (p : A) (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1)
    (J : Section2.VF M) (hJ : HasMixedVFJacobianAt f p J) : HasMixedVFJacobianAt g p J := by
  obtain ⟨L,K,⟨σ,hσ⟩,hKL⟩ := gammaGround_differentiable_of_independent hκ hs hr hv g p hp
  obtain ⟨H,⟨ρ,hρ⟩,hHJ⟩ := hJ
  have hHK : Set.EqOn H K (vfBall p.val.1 (max ρ σ)) := by
    intro x hx
    obtain ⟨hxA,hxF⟩ := hρ x (vfBall_anti (le_max_left _ _) hx)
    obtain ⟨hxA',hxG⟩ := hσ x (vfBall_anti (le_max_right _ _) hx)
    let q : A := ⟨(x,p.val.2),hxA⟩
    exact (congrArg Prod.fst hxF).symm.trans ((hVF q).trans (congrArg Prod.fst hxG))
  exact ⟨K,⟨σ,hσ⟩,hHJ.congr_on_vfBall hHK⟩

end DiamondIntegral.Section3
