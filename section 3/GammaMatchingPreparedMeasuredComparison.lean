import «section 3».GammaPreparedRectangleMeasuredComparison
import Integration7.MatchingFixedContextVolumeMaps

/-! The recorded-key matching construction from the RV-density proof
has a measured Gamma comparison for every retained Gamma form. All
preparations, label determination and nonzero-coordinate proofs are
the existing geometric constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {m : ℕ}

def gammaPreparedRectangleRVObject
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {H V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 m}
    (P : RectangleFamilyPullbackPreparation B V)
    (v : SpecialTransformations.Section5.Map H V) (hv : Function.Bijective v)
    (hvΓ : GammaGraphDefinable B (pointMapGraph v))
    (hvLabels : ∀ p : H, (v p).val.2 = p.val.2)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier H}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) m))
    (hQ : ∀ p : H, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    GammaGroundMeasuredRVObject hc B 2 := by
  let A := extendBase P.volumeTarget (Set.subset_univ _)
  let hAF := P.finite_volume C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) v hv hvΓ hfin
  let Ω := gammaPreparedRectangle_retained_form P v hv hvLabels Q hQ ω
  let hΩ : ∀ p q : Section5.nativeGammaPointDomain (carrier A) P.volume_target_gamma,
      p.val.2 = q.val.2 → Ω p = Ω q :=
    fun _ _ he => congrArg ω (Subtype.ext (congrArg (fun r => r ∘ P.volumeLabelIndex) he))
  exact gammaNativeMeasuredNormalization (gammaPullbackAt (Set.subset_univ _) A P.volume_target_gamma hAF)
    (gammaNativePullbackForm A P.volume_target_gamma hAF Ω hΩ)

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMatching_prepared_measured_comparison
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hvf : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 m}
    {F : UniformMixedCellPresentation B (carrier A)} {hBalanced : F.BalancedRows}
    {hNames : commonRealNames B ⊆ (C.base : Set M)}
    (P : UniformBalancedPositionPreparation B C F hBalanced hNames)
    (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M)
      ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity)))))
    (hQ : ∀ p : P.inFixedContext.matchingPreparedFamily, p.val.2 ∈ Q.carrier)
    (ω : GammaGroundVolumeForm hc B Q) :
    let R := P.inFixedContext
    ∃ LV : PreparedKeyLabelSpecialPreparation R.sourceSpecial
      (extendBase R.matchingVerticalTailDomain R.baseInclusion) R.matchingOldLabelIndex R.matchingTailKeyIndex
      (fun p hp => R.matching_vertical_tail_old_mem ⟨p,hp⟩) B,
    ∃ LH : PreparedKeyLabelSpecialPreparation R.targetSpecial
      (extendBase R.matchingHorizontalHeadDomain R.baseInclusion) R.matchingOldLabelIndex R.matchingHeadKeyIndex
      (fun p hp => R.matching_horizontal_head_old_mem ⟨p,hp⟩) B,
    Nonempty (GammaGroundMeasuredRVHom
      (gammaPreparedRectangleRVObject C hBC (R.matchingVerticalPullbackPreparation hNonzero LV)
        P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma
        P.matching_fixed_vertical_labels (R.matching_prepared_family_finite_labels hfin) Q hQ ω)
      (gammaPreparedRectangleRVObject C hBC (R.matchingHorizontalPullbackPreparation hNonzero LH)
        P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma
        P.matching_fixed_horizontal_labels (R.matching_prepared_family_finite_labels hfin) Q hQ ω)) := by
  intro R
  obtain ⟨LV⟩ := R.matching_vertical_recorded_preparation_exists
  obtain ⟨LH⟩ := R.matching_horizontal_recorded_preparation_exists
  refine ⟨LV,LH,⟨?_⟩⟩
  exact gammaPreparedRectangle_measured_comparison C hBC hvf
    (R.matchingVerticalPullbackPreparation hNonzero LV) (R.matchingHorizontalPullbackPreparation hNonzero LH)
    P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective
    P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective
    P.matching_fixed_vertical_gamma P.matching_fixed_horizontal_gamma
    P.matching_fixed_vertical_labels P.matching_fixed_horizontal_labels
    (P.matching_fixed_vertical_jacobian_one hc) (P.matching_fixed_horizontal_jacobian_one hc)
    (R.matching_prepared_family_finite_labels hfin) Q hQ ω
    (R.matching_vertical_prepared_labels_determine hNonzero LV)
    (R.matching_horizontal_prepared_labels_determine hNonzero LH)
    (R.matching_vertical_prepared_nonzero γ hγ hNonzero LV)
    (R.matching_horizontal_prepared_nonzero γ hγ hNonzero LH)

end DiamondIntegral.Section3
