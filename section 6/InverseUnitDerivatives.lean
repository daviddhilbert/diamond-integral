import «section 6».VFInterpolationTransitions
import «section 6».UniformMixedDifferentiability
import Section9.MixedInverseJacobian

/-! The inverse of an actual definable bijection with generic unit total
derivative also has generic unit total derivative. The inverse derivative
is obtained at the actual independent target point, not postulated. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

theorem inverse_generic_unit_derivative
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hf : Function.Bijective f)
    (hUnit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt f p)
    (q : B) (hInd : AlgebraicIndependent (vfParameterField S) q.val.1) :
    HasMixedUnitDerivativeAt (f.inverse hf) q := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  have hInv : Function.Injective (f.inverse hf) := by
    intro p z he
    have h := congrArg f he
    simpa only [Map.apply_inverse] using h
  have hInput := independent_map_of_finiteFibres hc (f.inverse hf)
    (Map.finiteFibres_of_injective hInv) q hInd
  obtain ⟨L,hL,hDet⟩ := hUnit (f.inverse hf q) hInput
  obtain ⟨D,hD⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv (f.inverse hf) q hInd
  have hAt : HasMixedVFDerivativeAt (f.inverse hf) (f (f.inverse hf q)) D := by
    simpa only [Map.apply_inverse] using hD
  have hProduct := mixedVFJacobian_inverse_product f (f.inverse hf) (Map.inverse_apply f hf)
    (f.inverse hf q) L D hL hAt
  refine ⟨D,hD,?_⟩
  simpa only [hDet,mul_one] using hProduct

end DiamondIntegral.Section6
