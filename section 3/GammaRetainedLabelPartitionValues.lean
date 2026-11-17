import «section 3».GammaRetainedLabelRestrictions
import «section 3».GammaStandardLabelPartitionValues
import Integration7.GammaRVLabelCuts

/-! Restrictions retain the actual old-label form. Pure RV label cuts
have native containing-context presentations with their literal domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n d : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRetained_label_partition_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : GammaRetainedMeasuredVFData hc B (n+1))
    (ρ : Fin d → Fin U.arity) (R : Set (Point (M := M) 0 d))
    (hR : GammaSetDefinable B R) (hRC : GammaSetDefinable B (Set.univ \ R)) :
    U.contractionValue C hBC hNames hGenerated =
      (U.labelCut C hNames ρ R hR).contractionValue C hBC hNames hGenerated +
      (U.labelCut C hNames ρ (Set.univ \ R) hRC).contractionValue C hBC hNames hGenerated := by
  let Q₀ := U.labelCut C hNames ρ R hR
  let Q₁ := U.labelCut C hNames ρ (Set.univ \ R) hRC
  let T := U.contraction C hBC hNames hGenerated
  let hT := U.contraction_gamma C hBC hNames hGenerated
  obtain ⟨P₀⟩ := standard_label_cut_presentation_on_equal_source T U.point_definable hT ρ R hR hNames
    (Q₀.nativeSet C hNames) (defSet_eq_of_carrier_eq rfl)
  obtain ⟨P₁⟩ := standard_label_cut_presentation_on_equal_source T U.point_definable hT ρ (Set.univ \ R) hRC hNames
    (Q₁.nativeSet C hNames) (defSet_eq_of_carrier_eq rfl)
  have h := gammaStandard_binary_label_partition_values C hBC hNames
    (A := U.nativeSet C hNames) (H₀ := Q₀.nativeSet C hNames) (H₁ := Q₁.nativeSet C hNames)
    U.point_definable Q₀.point_definable Q₁.point_definable U.finite Q₀.finite Q₁.finite
    ρ R hR hRC T hT P₀ P₁ U.form.extendByOne
  have h₀ := Q₀.contractionValue_eq C hBC hNames hGenerated hv hg δ hδ hδ1 P₀.contraction P₀.gamma
  have h₁ := Q₁.contractionValue_eq C hBC hNames hGenerated hv hg δ hδ hδ1 P₁.contraction P₁.gamma
  exact h.trans (congrArg₂ (· + ·) h₀.symm h₁.symm)

end DiamondIntegral.Section3
