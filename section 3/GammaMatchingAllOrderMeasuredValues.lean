import «section 3».GammaMatchingFamilyMeasuredValues

/-! The translated matching-family contractions have the actual
prepared pullback Gamma classes, by the checked rectangle construction
and its exact retained-label equation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation B (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames B ⊆ (C.base : Set M)}

theorem gammaMatching_family_all_order_measured_values
    (hBC : B.real ⊆ (C.base : Set M))
    (hvf : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (P : UniformBalancedPositionPreparation B C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M)
      ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity))))))
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) σ)
    (W : StandardContraction (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    let Q := P.inFixedContext
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.matching_prepared_family_gamma hfinH T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.matching_prepared_family_gamma hfinH W hW ω) := by
  intro Q hfinH
  rcases gamma_vf_two_order_cases σ with rfl | rfl
  · rcases gamma_vf_two_order_cases τ with rfl | rfl
    · exact gammaNativeRawMeasuredContraction_same_order C hBC hvf hg δ hδ hδ1
        Q.matching_prepared_family_gamma hfinH T W hT hW ω
    · exact gammaMatching_family_opposite_measured_values hBC hvf hg δ hδ hδ1 P hNonzero hfin ω T W hT hW
  · rcases gamma_vf_two_order_cases τ with rfl | rfl
    · exact (gammaMatching_family_opposite_measured_values hBC hvf hg δ hδ hδ1 P hNonzero hfin ω W T hW hT).symm
    · exact gammaNativeRawMeasuredContraction_same_order C hBC hvf hg δ hδ hδ1
        Q.matching_prepared_family_gamma hfinH T W hT hW ω

end DiamondIntegral.Section3
