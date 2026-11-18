import «section 3».GammaNativeMeasuredIsomorphisms
import «section 3».GammaMeasuredNormalizationRows

/-! An actual original-ground label bijection restricts to the native
full-weight parts whenever it preserves that locus. Its genuine Gamma
weight equation then gives the normalized measured RV arrow directly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {U V : GammaObjectAt B Set.univ (n+1)}

def gammaNativeHighGroundBijection
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (hHigh : ∀ u, u.val ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier ↔
      (f.map u).val ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt V)).carrier) :
    GammaGroundBijection
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U))
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt V)) := by
  let g : GammaGroundMap
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U))
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt V)) :=
    (f.map.comp (gammaNativeHighLabelInclusion U)).corestrict
      (fun u => (hHigh (gammaNativeHighLabelInclusion U u)).mp u.property)
  refine ⟨g,?_,?_⟩
  · intro u v he
    have heval := congrArg Subtype.val he
    change (f.map (gammaNativeHighLabelInclusion U u)).val =
      (f.map (gammaNativeHighLabelInclusion U v)).val at heval
    have hf : f.map (gammaNativeHighLabelInclusion U u) = f.map (gammaNativeHighLabelInclusion U v) :=
      Subtype.ext heval
    apply Subtype.ext
    have hh := congrArg Subtype.val (f.bijective.injective hf)
    exact hh
  · intro v
    obtain ⟨u,hu⟩ := f.bijective.surjective (gammaNativeHighLabelInclusion V v)
    have hU : u.val ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier := by
      apply (hHigh u).mpr
      rw [hu]
      exact v.property
    let u' : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U) := ⟨u.val,hU⟩
    refine ⟨u',Subtype.ext ?_⟩
    change (f.map u).val = v.val
    exact congrArg Subtype.val hu

theorem gammaNativeHighGroundBijection_square
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (hHigh : ∀ u, u.val ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier ↔
      (f.map u).val ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt V)).carrier)
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)) :
    gammaNativeHighLabelInclusion V ((gammaNativeHighGroundBijection f hHigh).map u) =
      f.map (gammaNativeHighLabelInclusion U u) := Subtype.ext rfl

def gammaNativeGroundMeasuredHom
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (hHigh : ∀ u, u.val ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier ↔
      (f.map u).val ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt V)).carrier)
    (hWeight : ∀ u, gammaNativeCombinedWeight U ω u = gammaNativeCombinedWeight V η (f.map u)) :
    GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) where
  bijection := gammaNativeHighGroundBijection f hHigh
  preserves u := by
    apply Subtype.ext
    rw [gammaNativeMeasuredNormalization_weight,gammaNativeMeasuredNormalization_weight,
      gammaNativeHighGroundBijection_square]
    exact hWeight (gammaNativeHighLabelInclusion U u)

end DiamondIntegral.Section3
