import «section 3».GammaSelectedTailCompletionValues
import «section 3».GammaMeasuredContractionOrderTransport
import «section 3».GammaFirstTwoStandardMeasuredExchange
import Integration7.SelectedVFTailFirstTwoOrders

/-! Same-order comparison and first-two exchange hold for arbitrary
retained selected RV coordinates and complete original-Gamma densities.
The actual VF-tail programs supply all finite-fibre comparisons. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a d : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hg : Cardinal.mk B.gamma < C.κ)
variable (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)

theorem gammaSelected_vf_tail_swap_first_two (σ : Equiv.Perm (Fin (n+2))) :
    selectedVFTailPermutation d ((swapFirstTwo n).trans σ) =
      (swapFirstTwo (d+n)).trans (selectedVFTailPermutation d σ) := by
  have h0 : ((swapFirstTwo n).trans σ) 0 = σ (0 : Fin (n+1)).succ := by
    change σ (swapFirstTwo n 0) = _
    rw [swapFirstTwo_zero]
  have h1 : ((swapFirstTwo n).trans σ) (0 : Fin (n+1)).succ = σ 0 := by
    change σ (swapFirstTwo n (0 : Fin (n+1)).succ) = _
    rw [swapFirstTwo_one]
  have ht : ∀ j : Fin n, ((swapFirstTwo n).trans σ) j.succ.succ = σ j.succ.succ := by
    intro j
    change σ (swapFirstTwo n j.succ.succ) = _
    rw [swapFirstTwo_tail]
  obtain ⟨h0',h1',ht'⟩ := selected_vf_tail_first_two_orders (d := d) σ _ h0 h1 ht
  apply Equiv.ext
  intro j
  change selectedVFTailPermutation d ((swapFirstTwo n).trans σ) j =
    selectedVFTailPermutation d σ (swapFirstTwo (d+n) j)
  cases j using Fin.cases with
  | zero => rw [swapFirstTwo_zero]; exact h0'
  | succ j =>
    cases j using Fin.cases with
    | zero => rw [swapFirstTwo_one]; exact h1'
    | succ j => rw [swapFirstTwo_tail]; exact ht' j


include hv hg δ hδ hδ1 in
theorem gammaSelected_standard_same_order_values
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    {σ : Equiv.Perm (Fin (n+1))} (T E : StandardContraction A σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin E hE ω) := by
  obtain ⟨r,V,F,hF,hFVF,hFCon,hFullF⟩ := selected_rv_vf_tail_full_program_exists hc T.program
    (gamma_vfPermutationImage A hA σ) hT ρ
  obtain ⟨s,W,H,hH,hHVF,hHCon,hFullH⟩ := selected_rv_vf_tail_full_program_exists hc E.program
    (gamma_vfPermutationImage A hA σ) hE ρ
  let A' := nativeProgramSelectedRVVFTailLift hc A ρ
  let hA' := gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA
  let hfin' := native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  let R := selectedRVVFTailStandardContraction hc T ρ F
  let Z := selectedRVVFTailStandardContraction hc E ρ H
  let hR := gamma_selected_rv_vf_tail_standard_contraction hc T ρ F hFullF
  let hZ := gamma_selected_rv_vf_tail_standard_contraction hc E ρ H hFullH
  have hLeft := gammaSelected_tail_completion_value C hBC hA ρ hfin T hT F hFullF hFVF hFCon ω
  have hRight := gammaSelected_tail_completion_value C hBC hA ρ hfin E hE H hFullH hHVF hHCon ω
  have hMiddle := gammaNativeRawMeasuredContraction_same_order C hBC hv hg δ hδ hδ1 hA' hfin' R Z hR hZ ω
  exact hLeft.symm.trans (hMiddle.trans hRight)

include hv hg δ hδ hδ1 in
theorem gammaSelected_standard_first_two_values
    (hNames : commonRealNames B ⊆ (C.base : Set M)) (hGenerated : VFGammaGeneratedBase B)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+2) a)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    {σ : Equiv.Perm (Fin (n+2))} (T : StandardContraction A σ) (E : StandardContraction A ((swapFirstTwo n).trans σ))
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin E hE ω) := by
  obtain ⟨r,V,F,hF,hFVF,hFCon,hFullF⟩ := selected_rv_vf_tail_full_program_exists hc T.program
    (gamma_vfPermutationImage A hA σ) hT ρ
  obtain ⟨s,W,H,hH,hHVF,hHCon,hFullH⟩ := selected_rv_vf_tail_full_program_exists hc E.program
    (gamma_vfPermutationImage A hA ((swapFirstTwo n).trans σ)) hE ρ
  let A' := nativeProgramSelectedRVVFTailLift hc A ρ
  let hA' := gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA
  let hfin' := native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  let R := selectedRVVFTailStandardContraction hc T ρ F
  let Z := selectedRVVFTailStandardContraction hc E ρ H
  let hR := gamma_selected_rv_vf_tail_standard_contraction hc T ρ F hFullF
  let hZ := gamma_selected_rv_vf_tail_standard_contraction hc E ρ H hFullH
  have hLeft := gammaSelected_tail_completion_value C hBC hA ρ hfin T hT F hFullF hFVF hFCon ω
  have hRight := gammaSelected_tail_completion_value C hBC hA ρ hfin E hE H hFullH hHVF hHCon ω
  let hOrder := gammaSelected_vf_tail_swap_first_two (d := d) σ
  let Z' := standardChangeOrder Z hOrder
  let hZ' := gammaStandard_change_order Z hOrder hZ
  have hMiddle := gammaFirst_two_standard_measured_exchange C hBC hv hg hNames hGenerated δ hδ hδ1
    A' hA' hfin' ω R Z' hR hZ'
  have hChange := congrArg gammaMeasuredPrincipalValue
    (gammaRaw_measured_change_order C hBC hA' hfin' Z hOrder hZ ω)
  exact hLeft.symm.trans (hMiddle.trans (hChange.trans hRight))

end DiamondIntegral.Section3
