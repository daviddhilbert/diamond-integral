import «section 3».GammaNativeGroundHighRestriction
import «section 3».GammaMeasuredIndexedGeometry
import «section 3».GammaGroundCarrierBijections
import «section 3».GammaNativeFiniteCodeExtensions

/-! Pure selected endpoint values agree with an actual native RV
presentation having the same labels, full locus and combined weight. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaNative_heterogeneous_measured_value {m : ℕ}
    (hnm : n=m) (U : GammaObjectAt B Set.univ (n+1)) (V : GammaObjectAt B Set.univ (m+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (hVol : ∀ u, (∏ i, Values.vrv ((Section5.nativeRVGroundVolume U u).val i)) =
      ∏ i, Values.vrv ((Section5.nativeRVGroundVolume V (f.map u)).val i))
    (hDensity : ∀ u, ω u = η (f.map u)) :
    gammaMeasuredPrincipalValue (gammaNativeMeasuredNormalization U ω) =
      gammaMeasuredPrincipalValue (gammaNativeMeasuredNormalization V η) := by
  subst m
  apply gammaMeasuredPrincipalValue_iso
  apply gammaNativeGroundMeasuredHom ω η f
  · intro u
    rw [gammaNativeHigh_domain_nonzero,gammaNativeHigh_domain_nonzero]
    have hprod := hVol u
    have hzero (W : GammaObjectAt B Set.univ (n+1))
        (w : Section5.nativeRVGroundDomain (hc := hc) W) :
        (∀ i, ((Section5.nativeRVGroundVolume W w).val i).val ≠ iRVZero) ↔
          (∏ i, Values.vrv ((Section5.nativeRVGroundVolume W w).val i)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      simp only [Finset.mem_univ,true_implies]
      apply forall_congr'
      intro i
      exact not_congr ((Values.vrv_eq_infinity_iff _).symm.trans
        (by rw [Values.infinity_eq_zero]))
    constructor
    · rintro ⟨v,hv,hn⟩
      have he : v = u := Subtype.ext hv
      subst v
      exact ⟨f.map u,rfl,(hzero V (f.map u)).mpr (hprod ▸ (hzero _ u).mp hn)⟩
    · rintro ⟨v,hv,hn⟩
      have he : v = f.map u := Subtype.ext hv
      subst v
      exact ⟨u,rfl,(hzero _ u).mpr (hprod.symm ▸ (hzero V (f.map u)).mp hn)⟩
  · intro u
    unfold gammaNativeCombinedWeight
    rw [hVol]
    exact congrArg (fun q => (cast (gammaCarrier hc) q.val).val *
      ∏ i, Values.vrv ((Section5.nativeRVGroundVolume V (f.map u)).val i)) (hDensity u)

end DiamondIntegral.Section3
