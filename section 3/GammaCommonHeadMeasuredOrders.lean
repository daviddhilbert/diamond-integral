import «section 3».GammaSelectedStandardMeasuredExchanges
import «section 3».GammaAppendedHeadMeasuredValues
import Integration7.SelectedCommonHeadOrderComparison

/-! The common-first-coordinate induction uses the smaller VF-arity
comparison on the actual contracted head, followed by the existing
coordinate and old-label charts. All densities are retained Gamma forms. -/
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a d : ℕ}

def GammaSelectedMeasuredOrderIndependent
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M)) (n : ℕ) : Prop :=
  ∀ {a d : ℕ} (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (σ τ : Equiv.Perm (Fin (n+1))) (T : StandardContraction A σ) (E : StandardContraction A τ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program),
    gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin E hE ω)

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaSelected_common_head_measured_orders
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (ih : GammaSelectedMeasuredOrderIndependent hc B C hBC n)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+2) a)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (σ υ : Equiv.Perm (Fin (n+2))) (h0 : σ 0 = υ 0)
    (T : StandardContraction A σ) (E : StandardContraction A υ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin E hE ω) := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  obtain ⟨τ,hOrder⟩ := contractionOrders_common_head σ υ h0
  let H := standardFirstHead T
  have hHead : GammaGraphDefinable B (pointMapGraph H.map) ∧ GammaSetDefinable B (carrier H.target) := by
    rcases T with ⟨b,V,P⟩
    cases P with
    | step H' tail => exact ⟨hT.1,hT.2.1⟩
  let hA' := gamma_headImage H.target hHead.2
  let ρ' := headVolumeIndex H ρ
  let η := gammaTotalRVCoordinateForm (headSelectedLabelIndex H (id : Fin a → Fin a)) ω
  let hfin' := head_selected_fibres_finite C.uncountable.le C.saturated hr H hHead.1 hHead.2 ρ
    (vfPermutation_selected_finite A σ ρ hfin)
  obtain ⟨D₀,hD₀,_,_,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr
    hGenerated hBC H.contractedSet hA' (Equiv.refl _)
  obtain ⟨Dτ,hDτ,_,_,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr
    hGenerated hBC H.contractedSet hA' τ
  have hRest := ih H.contractedSet hA' ρ' hfin' η (Equiv.refl _) τ D₀ Dτ hD₀ hDτ
  let F₀ := headTailAppendedStandardProgram σ H (Equiv.refl _) D₀
  let Fτ := headTailAppendedStandardProgram σ H τ Dτ
  let hF₀ := gammaHead_tail_appended_program hA σ H hHead.1 hHead.2 (Equiv.refl _) D₀ hD₀
  let hFτ := gammaHead_tail_appended_program hA σ H hHead.1 hHead.2 τ Dτ hDτ
  have hChart₀ := gammaAppended_head_measured_value C hBC hA σ H hHead.1 hHead.2 ρ hfin hfin'
    (Equiv.refl _) D₀ hD₀ ω
  have hChartτ := gammaAppended_head_measured_value C hBC hA σ H hHead.1 hHead.2 ρ hfin hfin'
    τ Dτ hDτ ω
  have hMiddle := hChart₀.symm.trans (hRest.trans hChartτ)
  let F₀' := standardChangeOrder F₀ (head_tail_identity_order σ)
  let hF₀' := gammaStandard_change_order F₀ (head_tail_identity_order σ) hF₀
  let E' := standardChangeOrder E hOrder
  let hE' := gammaStandard_change_order E hOrder hE
  have hLeft := gammaSelected_standard_same_order_values C hBC hv hg δ hδ hδ1 A hA ρ hfin ω T F₀' hT hF₀'
  have hRight := gammaSelected_standard_same_order_values C hBC hv hg δ hδ hδ1 A hA ρ hfin ω Fτ E' hFτ hE'
  have hChange₀ := congrArg gammaMeasuredPrincipalValue
    (gammaRaw_selected_measured_change_order C hBC hA ρ hfin F₀ (head_tail_identity_order σ) hF₀ ω)
  have hChangeE := congrArg gammaMeasuredPrincipalValue
    (gammaRaw_selected_measured_change_order C hBC hA ρ hfin E hOrder hE ω)
  exact hLeft.trans (hChange₀.trans (hMiddle.trans (hRight.trans hChangeE)))

end DiamondIntegral.Section3
