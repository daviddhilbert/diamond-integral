import «section 3».GammaRectangleAllOrderMeasuredValues
import «section 3».GammaStandardRelativeMeasuredValues
import «section 3».GammaNativeRetainedFullMaps
import «section 3».GammaCanonicalPullbackMeasuredValues

/-! The RV-density rectangle-to-pullback argument transports arbitrary
Gamma forms through its actual relatively unary map and canonical
contraction. No comparison field is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRectangle_contraction_to_pullback_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {a b : ℕ}
    {H : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 a}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 b}
    (hH : GammaSetDefinable B (carrier H)) (hA : GammaSetDefinable B (carrier A))
    (hfinH : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier H}.Finite)
    (hfinA : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hRectH : RectangularRVFibres (carrier H)) (hRectA : RectangularRVFibres (carrier A))
    (hPull : IsRVPullback (carrier A))
    (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (η : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) b)))
    (f : SpecialTransformations.Section5.Map H A) (hf : Function.Bijective f)
    (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (hForm : ∀ p : H, η ⟨(f p).val.2,Set.mem_univ _⟩ = ω ⟨p.val.2,Set.mem_univ _⟩)
    (hJ : VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1))
    (α : Equiv.Perm (Fin 2)) (hi : UnaryRelative f (α 0))
    {σ : Equiv.Perm (Fin 2)} (T : StandardContraction H σ) (hT : GammaProgramDefinable B T.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hH hfinH T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativePullbackTotalMeasuredObject C hBC A hA hAF η) := by
  obtain ⟨FH⟩ := independent_rectangle_family_preparations_exists C hNames δ hδ hδ1 H hH hRectH
  obtain ⟨FA⟩ := independent_rectangle_family_preparations_exists C hNames δ hδ hδ1 A hA hRectA
  obtain ⟨R,hR⟩ : ∃ R : StandardContraction H α, GammaProgramDefinable B R.program := by
    rcases gamma_vf_two_order_cases α with rfl | rfl
    · exact ⟨FH.headContraction,FH.head_contraction_gamma hH⟩
    · exact ⟨FH.tailContraction,FH.tail_contraction_gamma hH⟩
  obtain ⟨E,hE⟩ : ∃ E : StandardContraction A α, GammaProgramDefinable B E.program := by
    rcases gamma_vf_two_order_cases α with rfl | rfl
    · exact ⟨FA.headContraction,FA.head_contraction_gamma hA⟩
    · exact ⟨FA.tailContraction,FA.tail_contraction_gamma hA⟩
  obtain ⟨K,hK,hCanonical⟩ := gammaCanonical_pullback_measured_value_exists C hBC A hA hAF η hfinA hPull
  let F := gammaNativeRetainedFullMap C hBC hv (by decide : 0 < 2) hH hA hfinH hfinA ω η f hf hfΓ hJ hForm
  have hRelative : ∀ p, ∀ j, j ≠ α 0 → (F.map.map p).val.1 j = p.val.1 j := by
    intro p j hj
    rw [gammaNativeRetainedFullMap_apply]
    exact hi ⟨p.val,p.property⟩ j hj
  have hFirst := gammaRectangle_all_order_measured_values C hBC hv hg hNames δ hδ hδ1 hH hfinH hRectH T R hT hR ω
  have hMiddle := gammaStandard_relative_measured_values C hBC hv hg δ hδ hδ1 hH hA hfinH hfinA ω η F hRelative R E hR hE
  have hLast := gammaRectangle_all_order_measured_values C hBC hv hg hNames δ hδ hδ1 hA hfinA hRectA E K hE hK η
  exact hFirst.trans (hMiddle.trans (hLast.trans hCanonical))

end DiamondIntegral.Section3
