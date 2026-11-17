import «section 3».GammaOriginalLiftGraphs
import «section 3».GammaGroundEssentialVFMap
import Section9.SpecialJacobianGeneric
import Section5.GammaInvariantLogic

/-! A special chain with original-Gamma graph certificates has actual
Jacobian one at independent points over the original VF field. No real
codes of the Gamma parameters enter the independence hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {B : Base (M := M)} {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hc hκ hs hS hv in
theorem gammaSpecialChain_jacobian_one
    {A : SpecialTransformations.Section5.DefSet (M := M) S n r}
    {D : SpecialTransformations.Section5.DefSet (M := M) S n s}
    (T : Chain S n A D) (hT : GammaChainDefinable B T) (p : A)
    (hp : AlgebraicIndependent (vfParameterField B.real) (show Fin n → Section2.VF M from p.val.1)) :
    ∃ L : (Fin n → Section2.VF M) →ₗ[Section2.VF M] (Fin n → Section2.VF M),
      HasMixedVFDerivativeAt T.toMap p L ∧ (LinearMap.toMatrix' L).det = 1 := by
  revert p
  induction T with
  | nil A =>
    intro p hp
    let e : GammaIso B (carrier A) (carrier A) :=
      ⟨Equiv.refl _,GammaChainDefinable.graph (gammaLogicInput B) (.nil A) hT⟩
    obtain ⟨L,H,⟨ρ,hρ⟩,hH⟩ := gammaOriginalIso_differentiable hc hκ hs hS hv hT hT e p hp
    have hId : HasVFDerivativeAt (fun x : Fin n → Section2.VF M => x) p.val.1 LinearMap.id := by
      simpa only [LinearMap.id_apply,add_zero] using
        hasVFDerivativeAt_affine (LinearMap.id : (Fin n → Section2.VF M) →ₗ[Section2.VF M] (Fin n → Section2.VF M)) 0 p.val.1
    refine ⟨LinearMap.id,⟨_,⟨ρ,fun x hx => ?_⟩,hId⟩,?_⟩
    · obtain ⟨ha,_⟩ := hρ x hx
      exact ⟨ha,rfl⟩
    · rw [LinearMap.toMatrix'_id,Matrix.det_one]
  | @cons a b c A E D f tail ih =>
    intro p hp
    have hE := GammaChainDefinable.source B tail hT.2
    let single := Chain.cons f (Chain.nil E)
    have hsingle : GammaChainDefinable B single := ⟨hT.1,hE⟩
    let e : GammaIso B (carrier A) (carrier E) :=
      ⟨Equiv.ofBijective f.toMap f.bijective,
        GammaChainDefinable.graph (gammaLogicInput B) single hsingle⟩
    have hA := GammaChainDefinable.source B single hsingle
    obtain ⟨L,hL⟩ := gammaOriginalIso_differentiable hc hκ hs hS hv hA hE e p hp
    have hdet : (LinearMap.toMatrix' L).det = 1 := by
      cases f with
      | canonical A =>
        obtain ⟨H,⟨ρ,hρ⟩,hH⟩ := hL
        have heq : Set.EqOn H id (vfBall p.val.1 ρ) := by
          intro x hx
          obtain ⟨ha,he⟩ := hρ x hx
          exact (congrArg Prod.fst he).symm
        have hId : HasVFDerivativeAt id p.val.1 LinearMap.id := by
          change HasVFDerivativeAt (fun x : Fin n → Section2.VF M => x) p.val.1 LinearMap.id
          simpa only [LinearMap.id_apply,add_zero] using
            hasVFDerivativeAt_affine (LinearMap.id : (Fin n → Section2.VF M) →ₗ[Section2.VF M] (Fin n → Section2.VF M)) 0 p.val.1
        rw [(hH.congr_on_vfBall heq).unique hId,LinearMap.toMatrix'_id,Matrix.det_one]
      | centripetal F => exact centripetal_det_eq_one F p hL
    let F := Section5.nativeGammaPointBijection (hc := hc) hA hE e
    have he (x : (Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA)) :
        (F.map x).val = (e.equiv x).val := Section5.nativeGammaPointBijection_apply hA hE e x
    have hp' := gammaGround_independent_map F.map (GammaGroundMap.finiteFibres_of_injective F.bijective.injective)
      hκ hS p hp
    rw [he] at hp'
    obtain ⟨D,hD,hd⟩ := ih hT.2 (f.toMap p) hp'
    obtain ⟨H,hH,hHL⟩ := hL
    obtain ⟨K,hK,hKD⟩ := hD
    have hchain : HasVFDerivativeAt K (H p.val.1) D := hH.center.symm ▸ hKD
    refine ⟨D.comp L,⟨K ∘ H,hH.comp hK hHL,hchain.comp hHL⟩,?_⟩
    rw [LinearMap.toMatrix'_comp,Matrix.det_mul,hd,hdet,mul_one]

end DiamondIntegral.Section3
