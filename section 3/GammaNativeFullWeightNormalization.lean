import «section 3».GammaNativeMeasuredNormalization
import «section 3».GammaNativeStructuralValues

/-! A full-weight native object is unchanged by normalization, including
its arbitrary original Gamma form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaNativeFullHigh_domain (U : GammaObjectAt B Set.univ (n+1)) (hfull : GammaFullWeightAt U) :
    (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) U).carrier := by
  rw [Section5.nativeRVGroundDomain_carrier,Section5.nativeRVGroundDomain_carrier]
  ext x
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx,?_⟩
    intro hl
    have hn := (@mem_rvLowDomain M N Set.univ n U.object.obj ⟨x,hx⟩).mp hl
    have he := hfull ⟨x,hx⟩
    exact Nat.not_succ_le_self n (he.ge.trans hn)

def gammaNativeFullWeightNormalizationHom (U : GammaObjectAt B Set.univ (n+1)) (hfull : GammaFullWeightAt U)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaGroundMeasuredRVHom
      (⟨Section5.nativeRVGroundObject U hfull,ω⟩ : GammaGroundMeasuredRVObject hc B (n+1))
      (gammaNativeMeasuredNormalization U ω) where
  bijection := GammaGroundBijection.ofCarrierEq (gammaNativeFullHigh_domain U hfull).symm
  preserves u := by
    let b : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U) :=
      (GammaGroundBijection.ofCarrierEq (gammaNativeFullHigh_domain U hfull).symm).map u
    have hu : gammaNativeHighLabelInclusion U b = u := Subtype.ext rfl
    have hv : (Section5.nativeRVGroundVolume U u).val =
        (Section5.nativeRVGroundVolume (gammaHighRestrictionAt U) b).val := by
      rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
      rfl
    change gammaGroundFormValue ω u * _ = gammaGroundFormValue ω (gammaNativeHighLabelInclusion U b) * _
    rw [hu]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    apply Subtype.ext
    exact congrFun hv j

theorem gammaUnaryAdmissible_full (U : GammaObjectAt B Set.univ 1)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject 0) : GammaFullWeightAt U := by
  apply (gammaFullWeightAt_iff_nonzero U).mpr
  intro u i hi
  have he : i=0 := Fin.fin_one_eq_zero i
  subst i
  exact hAd.nonzero u (hi.trans (CanonicalStructure.sortZero_normalize .rv))

end DiamondIntegral.Section3
