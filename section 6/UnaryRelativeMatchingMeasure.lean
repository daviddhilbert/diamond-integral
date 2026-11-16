import «section 6».UnaryRelativeMatchingForms
import «section 6».InverseUnitDerivatives
import «section 6».MixedGammaJacobianException
import «section 6».GammaMapArithmetic

/-! The literal auxiliary conjugate inherits the original generic
Gamma-Jacobian identity. Actual transported forms give one definable
VF-small exception, over the original base, for the full derivative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem HasMixedUnitDerivativeAt.jacobian_one
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    {f : Map A B} {p : A} (h : HasMixedUnitDerivativeAt f p) : HasMixedVFJacobianAt f p (1 : VF M) := by
  obtain ⟨L,⟨F,hF,hD⟩,hDet⟩ := h
  exact ⟨F,hF,by simpa only [hDet] using hD.hasJacobianAt⟩

namespace UnaryRelativePreparedMatching
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B} (H : UnaryRelativePreparedMatching (G := G) A B f)
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hsmall : Cardinal.mk S < κ)
variable (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hc hκ hs hsmall hv in
theorem generic_conjugate_jacobian (hf : Function.Bijective f)
    (p : H.source) (hp : AlgebraicIndependent (vfParameterField S) p.val.1)
    (J : VF M)
    (hJ : HasMixedVFJacobianAt f (H.sourceMap.inverse (H.sourceChain.bijective h00) p) J) :
    HasMixedVFJacobianAt H.map p J := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  let α := H.sourceMap
  let hα := H.sourceChain.bijective h00
  let inv := α.inverse hα
  have hInvInj : Function.Injective inv := by
    intro x y he
    have h := congrArg α he
    simpa only [inv,Map.apply_inverse] using h
  have hInvFin := Map.finiteFibres_of_injective hInvInj
  have hInvUnit := inverse_generic_unit_derivative h00 hc hκ hs hsmall hv α hα
    (fun a ha => H.sourceChain.unit_derivative_of_independent h00 hc hκ hs hsmall hv a ha) p hp
  obtain ⟨J₀,K₀,hJ₀,hK₀,hFirst⟩ := mixedVFJacobian_comp_of_independent hc hκ hs hsmall hv inv f hInvFin p hp
  have hJ₀Eq : J₀=(1 : VF M) := hJ₀.unique hInvUnit.jacobian_one
  have hK₀Eq : K₀=J := hK₀.unique hJ
  let g := f.comp inv
  have hgFin : g.FiniteFibres := Map.finiteFibres_of_injective (hf.injective.comp hInvInj)
  have hFirst' : HasMixedVFJacobianAt g p J := by
    simpa only [g,Map.comp,Function.comp_def,hJ₀Eq,hK₀Eq,mul_one] using hFirst
  have hgInd := independent_map_of_finiteFibres hc g hgFin p hp
  have hTargetUnit := H.targetChain.unit_derivative_of_independent h00 hc hκ hs hsmall hv (g p) hgInd
  obtain ⟨J₁,K₁,hJ₁,hK₁,hLast⟩ := mixedVFJacobian_comp_of_independent hc hκ hs hsmall hv
    g H.targetMap hgFin p hp
  have hJ₁Eq : J₁=J := hJ₁.unique hFirst'
  have hK₁Eq : K₁=(1 : VF M) := hK₁.unique hTargetUnit.jacobian_one
  rw [H.map_eq_conjugate h00]
  simpa only [g,inv,α,hα,Map.comp,Function.comp_def,hJ₁Eq,hK₁Eq,one_mul] using hLast

include hc hκ hs hsmall hv in
theorem measure_exception (hf : Function.Bijective f)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField S) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    ∃ E : DefSet (rawMixedSpace (M := M) 1 H.sourceArity) S,E.carrier ⊆ H.source.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E<1 ∧ ∀ p : H.source,p.val ∉ E.carrier →
        ∃ J : VF M,HasMixedVFJacobianAt H.map p J ∧
          vfValue J=(gammaMapValue (H.sourceForm h00 ω) p/gammaMapValue (H.targetForm h00 σ) (H.map p)).val := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  let ν := gammaMapDiv hc (H.sourceForm h00 ω) ((H.targetForm h00 σ).comp H.map)
  have hFinal (p : H.source) (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
      ∃ D,HasMixedVFDerivativeAt H.map p D ∧
        vfValue (LinearMap.toMatrix' D).det=(gammaMapValue ν p).val := by
    let inv := H.sourceMap.inverse (H.sourceChain.bijective h00)
    let a := inv p
    have hInvInj : Function.Injective inv := by
      intro x y he
      have h := congrArg H.sourceMap he
      simpa only [inv,Map.apply_inverse] using h
    have ha := independent_map_of_finiteFibres hc inv (Map.finiteFibres_of_injective hInvInj) p hp
    obtain ⟨J,hJ,hVal⟩ := hGeneric a ha
    have hFinalJ := H.generic_conjugate_jacobian h00 hc hκ hs hsmall hv hf p hp J hJ
    obtain ⟨D,hD⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv H.map p hp
    have hDetJ : HasMixedVFJacobianAt H.map p (LinearMap.toMatrix' D).det := by
      obtain ⟨F,hF,hFD⟩ := hD
      exact ⟨F,hF,hFD.hasJacobianAt⟩
    have hDet := hDetJ.unique hFinalJ
    have hSourceAt : H.sourceForm h00 ω p=ω a := rfl
    have hTargetAt : H.targetForm h00 σ (H.map p)=σ (f a) := by
      have hp' : H.sourceMap a=p := Map.apply_inverse H.sourceMap (H.sourceChain.bijective h00) p
      rw [← hp',H.commutes a,H.targetForm_transport h00 σ (f a)]
    have hRatio : gammaMapValue ν p=gammaMapValue ω a/gammaMapValue σ (f a) := by
      change gammaMapValue (H.sourceForm h00 ω) p /
        gammaMapValue (H.targetForm h00 σ) (H.map p)=_
      unfold gammaMapValue
      rw [hSourceAt,hTargetAt]
    refine ⟨D,hD,?_⟩
    rw [hDet,hRatio]
    exact hVal
  obtain ⟨E,hEA,hDim,hE⟩ := exists_mixedGammaJacobian_exception hc hs hsmall (by decide : 0<1) H.map ν hFinal
  refine ⟨E,hEA,hDim,fun p hp => ?_⟩
  obtain ⟨D,hD,hVal⟩ := hE p hp
  refine ⟨(LinearMap.toMatrix' D).det,?_,hVal⟩
  obtain ⟨F,hF,hFD⟩ := hD
  exact ⟨F,hF,hFD.hasJacobianAt⟩

end UnaryRelativePreparedMatching
end DiamondIntegral.Section6
