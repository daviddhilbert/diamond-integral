import «section 3».GammaMixedSmallContractionValues
import «section 3».GammaMixedFullBijectionValues
import «section 3».GammaGroundMeasuredVFScissors

/-! The contraction value is invariant under cofull restriction and
the actual positive-degree measured essential groupoid. Small-domain
vanishing and additive scissors suffice; no cancellation is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hg : Cardinal.mk B.gamma < C.κ)
variable (hGenerated : VFGammaGeneratedBase B)
variable (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)

include hg δ hδ hδ1 in
theorem gammaMixed_cofull_restriction_value
    (U : GammaGroundMeasuredVFData hc B (n+1))
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (n+1) U.arity))
    (hA : A.carrier ⊆ U.domain.carrier)
    (hsmall : Section2.vfDimension (U.domain.sdiff A).carrier < ((n+1 : ℕ) : WithBot ℕ)) :
    gammaMixedContractionValue C hBC hv hg hGenerated U =
      gammaMixedContractionValue C hBC hv hg hGenerated (U.restrict A hA) := by
  have h := gammaMixed_binary_partition_values C hBC hv hg hGenerated δ hδ hδ1 U A hA
  rw [gammaMixed_small_contraction_value C hBC hv hg hGenerated
    (U.restrict (U.domain.sdiff A) (fun _ h => h.1)) hsmall,add_zero] at h
  exact h

include hg δ hδ hδ1 in
theorem gammaMixed_essential_contraction_values
    {U V : GammaGroundMeasuredVFData hc B (n+1)}
    (f : GammaGroundEssentialVFMap U.domain V.domain)
    (hf : f.PreservesGeneric Values.vfValueHom (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V)) :
    gammaMixedContractionValue C hBC hv hg hGenerated U =
      gammaMixedContractionValue C hBC hv hg hGenerated V := by
  let F : GammaFullMeasuredBijection (U.restrict f.source f.source_subset)
      (V.restrict f.target f.target_subset) := ⟨⟨f.map,f.bijective⟩,hf⟩
  exact (gammaMixed_cofull_restriction_value C hBC hv hg hGenerated δ hδ hδ1 U
    f.source f.source_subset f.source_small).trans
      ((gammaMixed_full_bijection_values C hBC hv hg hGenerated δ hδ hδ1 F).trans
        (gammaMixed_cofull_restriction_value C hBC hv hg hGenerated δ hδ hδ1 V
          f.target f.target_subset f.target_small).symm)

include hg δ hδ hδ1 in
theorem gammaMixed_measured_hom_contraction_values
    {U V : GammaGroundMeasuredVFData hc B (n+1)}
    (f : GammaGroundMeasuredVFHom C.uncountable.le C.saturated
      ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv U V) :
    gammaMixedContractionValue C hBC hv hg hGenerated U =
      gammaMixedContractionValue C hBC hv hg hGenerated V := by
  obtain ⟨g,_⟩ := f.property
  exact gammaMixed_essential_contraction_values C hBC hv hg hGenerated δ hδ hδ1 g.val g.property.toGeneric

end DiamondIntegral.Section3
