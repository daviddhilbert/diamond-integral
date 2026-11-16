import «section 6».UnaryRelativeMatchingMeasure

/-! Generic measured conjugation through arbitrary actual auxiliary
unit preparations. No RV matching is assumed, so this applies also to
the initial measured preparations before first-zero matching begins. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {A' : DefSet (rawMixedSpace (M := M) 1 a) S} {B' : DefSet (rawMixedSpace (M := M) 1 b) S}

theorem unary_unit_preparation_conjugate_jacobian
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (α : Map A A') (β : Map B B')
    (hα : UnaryRelativeApertureChain (G := G) A A' α)
    (hβ : UnaryRelativeApertureChain (G := G) B B' β)
    (f : Map A B) (hf : Function.Bijective f)
    (p : A') (hp : AlgebraicIndependent (vfParameterField S) p.val.1) (J : VF M)
    (hJ : HasMixedVFJacobianAt f (α.inverse (hα.bijective h00) p) J) :
    HasMixedVFJacobianAt (β.comp (f.comp (α.inverse (hα.bijective h00)))) p J := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  let inv := α.inverse (hα.bijective h00)
  have hInvInj : Function.Injective inv := by
    intro x y he
    have h := congrArg α he
    simpa only [inv,Map.apply_inverse] using h
  have hInvFin := Map.finiteFibres_of_injective hInvInj
  have hInvUnit := inverse_generic_unit_derivative h00 hc hκ hs hsmall hv α (hα.bijective h00)
    (fun a ha => hα.unit_derivative_of_independent h00 hc hκ hs hsmall hv a ha) p hp
  obtain ⟨J₀,K₀,hJ₀,hK₀,hFirst⟩ := mixedVFJacobian_comp_of_independent hc hκ hs hsmall hv inv f hInvFin p hp
  have hJ₀Eq : J₀=(1 : VF M) := hJ₀.unique hInvUnit.jacobian_one
  have hK₀Eq : K₀=J := hK₀.unique hJ
  let g := f.comp inv
  have hgFin : g.FiniteFibres := Map.finiteFibres_of_injective (hf.injective.comp hInvInj)
  have hFirst' : HasMixedVFJacobianAt g p J := by
    simpa only [g,Map.comp,Function.comp_def,hJ₀Eq,hK₀Eq,mul_one] using hFirst
  have hgInd := independent_map_of_finiteFibres hc g hgFin p hp
  have hTargetUnit := hβ.unit_derivative_of_independent h00 hc hκ hs hsmall hv (g p) hgInd
  obtain ⟨J₁,K₁,hJ₁,hK₁,hLast⟩ := mixedVFJacobian_comp_of_independent hc hκ hs hsmall hv g β hgFin p hp
  have hJ₁Eq : J₁=J := hJ₁.unique hFirst'
  have hK₁Eq : K₁=(1 : VF M) := hK₁.unique hTargetUnit.jacobian_one
  simpa only [g,inv,Map.comp,Function.comp_def,hJ₁Eq,hK₁Eq,one_mul] using hLast

end DiamondIntegral.Section6
