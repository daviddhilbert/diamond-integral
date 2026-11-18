import «section 3».GammaNativeCoproductForms
import «section 3».GammaIndexedEssentialLabels
import «section 3».GammaGroundMeasuredRVSemiring

/-! Full-weight normalization commutes with a genuine tagged measured
coproduct, retaining each original Gamma form on its summand. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaNativeHighCoprod_domain (U V : GammaObjectAt B Set.univ (n+1)) :
    (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (gammaCoprodAt U V))).carrier =
      (gammaNativeTaggedDomain (hc := hc) (gammaHighRestrictionAt U) (gammaHighRestrictionAt V)).carrier := by
  let C := gammaCoprodAt U V
  ext x
  constructor
  · intro hx
    let w := gammaNativeHighLabelInclusion C ⟨x,hx⟩
    have hNZ := (gammaNativeHighLabel_mem C w).mp hx
    rcases (gammaNativeCoprod_domain (hc := hc) U V).le w.property with ⟨u,hu⟩|⟨v,hv⟩
    · have hVol := gammaNativeCoprod_volume_left U V u w hu.symm
      have huHigh := (gammaNativeHighLabel_mem U u).mpr (hVol ▸ hNZ)
      exact Or.inl ⟨⟨u.val,huHigh⟩,hu⟩
    · have hVol := gammaNativeCoprod_volume_right U V v w hv.symm
      have hvHigh := (gammaNativeHighLabel_mem V v).mpr (hVol ▸ hNZ)
      exact Or.inr ⟨⟨v.val,hvHigh⟩,hv⟩
  · rintro (⟨u,hu⟩|⟨v,hv⟩)
    · let a := gammaNativeHighLabelInclusion U u
      let w : Section5.nativeRVGroundDomain (hc := hc) C :=
        ⟨x,(gammaNativeCoprod_domain (hc := hc) U V).ge (Or.inl ⟨a,hu⟩)⟩
      apply (gammaNativeHighLabel_mem C w).mpr
      rw [gammaNativeCoprod_volume_left U V a w hu.symm]
      exact (gammaNativeHighLabel_mem U a).mp u.property
    · let a := gammaNativeHighLabelInclusion V v
      let w : Section5.nativeRVGroundDomain (hc := hc) C :=
        ⟨x,(gammaNativeCoprod_domain (hc := hc) U V).ge (Or.inr ⟨a,hv⟩)⟩
      apply (gammaNativeHighLabel_mem C w).mpr
      rw [gammaNativeCoprod_volume_right U V a w hv.symm]
      exact (gammaNativeHighLabel_mem V a).mp v.property

def gammaNativeCoprodNormalizationHom (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V)) :
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaCoprodAt U V) (gammaNativeCoprodForm U V ω η))
      ((gammaNativeMeasuredNormalization U ω).coprod (gammaNativeMeasuredNormalization V η)) := by
  let X := gammaNativeMeasuredNormalization U ω
  let Y := gammaNativeMeasuredNormalization V η
  let C := gammaCoprodAt U V
  let e : GammaGroundBijection
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt C)) (X.coprod Y).underlying.domain :=
    GammaGroundBijection.ofCarrierEq (gammaNativeHighCoprod_domain (hc := hc) U V)
  refine ⟨e,fun w => ?_⟩
  rcases (e.map w).property with ⟨u,hu⟩|⟨v,hv⟩
  · have he : e.map w = gammaGroundRVCoprodLeft X.underlying Y.underlying u := Subtype.ext hu.symm
    rw [he,gammaGroundMeasuredRVCoprod_combined_left]
    apply Subtype.ext
    rw [gammaNativeMeasuredNormalization_weight,gammaNativeMeasuredNormalization_weight]
    let a := gammaNativeHighLabelInclusion U u
    let b := gammaNativeHighLabelInclusion C w
    have hTag : b.val = rvLeftTag (rvObjectArity V.object.obj) a.val := hu.symm
    unfold gammaNativeCombinedWeight
    rw [gammaNativeCoprodForm_left U V ω η a b hTag,gammaNativeCoprod_volume_left U V a b hTag]
  · have he : e.map w = gammaGroundRVCoprodRight X.underlying Y.underlying v := Subtype.ext hv.symm
    rw [he,gammaGroundMeasuredRVCoprod_combined_right]
    apply Subtype.ext
    rw [gammaNativeMeasuredNormalization_weight,gammaNativeMeasuredNormalization_weight]
    let a := gammaNativeHighLabelInclusion V v
    let b := gammaNativeHighLabelInclusion C w
    have hTag : b.val = rvRightTag (rvObjectArity U.object.obj) a.val := hv.symm
    unfold gammaNativeCombinedWeight
    rw [gammaNativeCoprodForm_right U V ω η a b hTag,gammaNativeCoprod_volume_right U V a b hTag]

theorem gammaNativeMeasuredClass_coprod (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V)) :
    gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization (gammaCoprodAt U V) (gammaNativeCoprodForm U V ω η)) =
      gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization U ω) +
        gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization V η) :=
  (gammaGroundMeasuredRVClass_iso (asIso (gammaNativeCoprodNormalizationHom U V ω η))).trans
    (gammaGroundMeasuredRVClass_coprod _ _)

end DiamondIntegral.Section3
