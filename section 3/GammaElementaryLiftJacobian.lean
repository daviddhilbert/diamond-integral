import «section 3».GammaSpecialJacobian
import «section 3».GammaMixedVFComparison
import IntegrationSection6.ElementaryLiftDiagram

/-! The actual elementary focus diagram has Jacobian one over the
original Gamma ground, before any choice of density is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7 SpecialTransformations.Section9
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaElementaryLift_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U : GammaRVObject B n} {i : Fin n} (D : ElementaryLiftDiagram U i)
    (p : typedLift U.object)
    (hp : AlgebraicIndependent (vfParameterField B.real) (show Fin n → Section2.VF M from p.val.1)) :
    HasMixedVFJacobianAt D.liftIso.equiv p 1 := by
  obtain ⟨L,hL,hdet⟩ := gammaSpecialChain_jacobian_one hc hκ hs hr hv
    D.special.special.chain D.special.invariant_graphs p hp
  have hJs : HasMixedVFJacobianAt D.special.special.chain.toMap p 1 := by
    obtain ⟨F,hF,hFL⟩ := hL
    refine ⟨F,hF,?_⟩
    simpa only [hdet] using hFL.hasJacobianAt
  have htarget : GammaSetDefinable B (carrier (typedLift
      (@elementary M (CanonicalStructure.normalize (M := M))
        (CanonicalStructure.normalized_model (M := M) inferInstance) U.codes n U.object i))) :=
    D.relabelIso.target_definable (gammaLogicInput B)
  obtain ⟨H,hH⟩ := gammaOriginalIso_differentiable hc hκ hs hr hv
    (gamma_typedLift_definable U) htarget D.liftIso p hp
  obtain ⟨F,hF,hFH⟩ := hH
  have hJ : HasMixedVFJacobianAt D.liftIso.equiv p (LinearMap.toMatrix' H).det :=
    ⟨F,hF,hFH.hasJacobianAt⟩
  have he : (LinearMap.toMatrix' H).det = 1 :=
    mixedJacobian_eq_of_vf_eq D.liftIso.equiv D.special.special.chain.toMap
      (fun q => D.up_vf _) p hJ hJs
  exact he ▸ hJ

end DiamondIntegral.Section3
