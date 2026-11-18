import «section 3».GammaNativeGroundIsomorphisms

/-! On full-weight native objects an original-Gamma label bijection
already has the native weight condition. Reuse the existing full-weight
isomorphism constructor without requiring equality of volume tuples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaNativeFullGroundIso (U V : GammaObjectAt B Set.univ n)
    (hU : GammaFullWeightAt U) (hV : GammaFullWeightAt V)
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V)) :
    GammaIsoAt U V := by
  let P := Section5.nativeRVGroundDomainEquiv (hc := hc) U
  let Q := Section5.nativeRVGroundDomainEquiv (hc := hc) V
  let e := P.symm.trans ((Equiv.ofBijective f.map f.bijective).trans Q)
  apply Section5.fullWeightIsoAtOfEquiv U V hU hV e
  apply GammaGraphDefinable.congr (Section5.groundRV_gamma_map f.map)
  intro p q
  constructor
  · rintro ⟨u,hu,hv⟩
    refine ⟨P u,hu,?_⟩
    change (Q (f.map (P.symm (P u)))).val = q.2
    rw [P.symm_apply_apply]
    exact hv
  · rintro ⟨u,hu,hv⟩
    exact ⟨P.symm u,hu,hv⟩

@[simp] theorem gammaNativeFullGroundIso_map (U V : GammaObjectAt B Set.univ n)
    (hU : GammaFullWeightAt U) (hV : GammaFullWeightAt V)
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    (Section5.nativeRVGroundIso (gammaNativeFullGroundIso U V hU hV f)).map u = f.map u := by
  apply Subtype.ext
  rfl

end DiamondIntegral.Section3
