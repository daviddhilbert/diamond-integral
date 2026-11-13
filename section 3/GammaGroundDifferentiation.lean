import «section 3».GammaGroundEssentialVFMap
import Section9.MixedInverseJacobian

/-! Fixed-label derivatives, determinant products and inverse products
at independent points over the original Gamma-ground VF field. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [hchar : CharZero (VFType (M := M))]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VFType (M := M)) G]
variable {n r s t : ℕ}
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
variable {C : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n t)}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : (VFType (M := M)), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hchar hκ hs hS hv

theorem gammaGround_differentiable_of_independent (f : GammaGroundMap A B) (a : A)
    (ha : AlgebraicIndependent (vfParameterField ground.real) a.val.1) :
    ∃ L : (Fin n → (VFType (M := M))) →ₗ[(VFType (M := M))] (Fin n → (VFType (M := M))), HasMixedVFDerivativeAt f a L := by
  obtain ⟨T, hT, hsmall, hfield, hDA, hDB, hgraph⟩ := f.realize hκ hS
  let DA : DefSet (rawMixedSpace (M := M) n r) T := ⟨A.carrier, hDA⟩
  let DB : DefSet (rawMixedSpace (M := M) n s) T := ⟨B.carrier, hDB⟩
  let F : Map DA DB := ⟨f.toFun, (relationDefinable_iff_product _).mpr hgraph⟩
  have haT : AlgebraicIndependent (vfParameterField T) a.val.1 := by rwa [hfield]
  exact mixedDifferentiableAt_of_independent hc hκ hs hsmall hv F a haT

theorem gammaGround_jacobian_comp_of_independent (f : GammaGroundMap A B) (g : GammaGroundMap B C)
    (hf : f.FiniteFibres) (a : A)
    (ha : AlgebraicIndependent (vfParameterField ground.real) a.val.1) :
    ∃ J K : (VFType (M := M)), HasMixedVFJacobianAt f a J ∧ HasMixedVFJacobianAt g (f a) K ∧
      HasMixedVFJacobianAt (g ∘ f) a (K * J) := by
  obtain ⟨L, hL⟩ := gammaGround_differentiable_of_independent hκ hs hS hv f a ha
  obtain ⟨D, hD⟩ := gammaGround_differentiable_of_independent hκ hs hS hv g (f a)
    (gammaGround_independent_map f hf hκ hS a ha)
  exact ⟨_, _, mixedVFJacobian_comp_of_full_derivative hL hD⟩

theorem gammaGround_jacobian_inverse_of_independent (f : GammaGroundBijection A B) (a : A)
    (ha : AlgebraicIndependent (vfParameterField ground.real) a.val.1) :
    ∃ J K : (VFType (M := M)), HasMixedVFJacobianAt f.map a J ∧
      HasMixedVFJacobianAt f.symm.map (f.map a) K ∧ K * J = 1 := by
  obtain ⟨L, hL⟩ := gammaGround_differentiable_of_independent hκ hs hS hv f.map a ha
  obtain ⟨D, hD⟩ := gammaGround_differentiable_of_independent hκ hs hS hv f.symm.map (f.map a)
    (gammaGround_independent_map f.map (GammaGroundMap.finiteFibres_of_injective f.bijective.injective) hκ hS a ha)
  refine ⟨_, _, ?_, ?_, mixedVFJacobian_inverse_product f.map f.symm.map
    (fun a => f.map.inverse_apply f.bijective a) a L D hL hD⟩
  · obtain ⟨F, hF, hder⟩ := hL
    exact ⟨F, hF, hder.hasJacobianAt⟩
  · obtain ⟨F, hF, hder⟩ := hD
    exact ⟨F, hF, hder.hasJacobianAt⟩

end DiamondIntegral.Section3
