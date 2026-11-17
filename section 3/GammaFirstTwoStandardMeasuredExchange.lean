import «section 3».GammaTwoPartialMeasuredRows
import «section 3».GammaPositiveTailRawValues
import «section 3».GammaTwoHeadTailProducts
import Integration7.FirstTwoStandardVolumeExchange

/-! Exchanging the first two coordinates of arbitrary specified
standard programs preserves the complete original-Gamma measured value
in every positive dimension where the exchange is defined. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaFirst_two_standard_measured_exchange
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+2) a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+2) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    {σ : Equiv.Perm (Fin (n+2))}
    (T : StandardContraction A σ) (E : StandardContraction A ((swapFirstTwo n).trans σ))
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin E hE ω) := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  rcases T with ⟨b,V,P⟩
  rcases E with ⟨c,Z,Q⟩
  cases P with
  | step H tail =>
    cases tail with
    | step H₂ tail₂ =>
      cases Q with
      | step K etail =>
        cases etail with
        | step K₂ etail₂ =>
          let T : StandardContraction A σ := ⟨b,V,.step H (.step H₂ tail₂)⟩
          let E : StandardContraction A ((swapFirstTwo n).trans σ) := ⟨c,Z,.step K (.step K₂ etail₂)⟩
          let PT := twoHeadPartialProgram H H₂
          let PE := twoHeadPartialProgram K K₂
          have hPT : GammaPartialProgramDefinable B PT :=
            ⟨hT.1,hT.2.1,hT.2.2.1,hT.2.2.2.1,gamma_headImage H₂.target hT.2.2.2.1⟩
          have hPE : GammaPartialProgramDefinable B PE :=
            ⟨hE.1,hE.2.1,hE.2.2.1,hE.2.2.2.1,gamma_headImage K₂.target hE.2.2.2.1⟩
          let hfinT := partial_volume_fibres_finite C.uncountable.le C.saturated hr PT hPT
            (vfPermutation_finite_rv_fibres A σ hfin)
          have hfinE : ∀ x t, {s | (x,s) ∈ carrier K₂.contractedSet ∧
              s ∘ (PE.volumeIndex ∘ swapTwo.symm) = t}.Finite := by
            intro x t
            apply (partial_volume_fibres_finite C.uncountable.le C.saturated hr PE hPE
              (vfPermutation_finite_rv_fibres A ((swapFirstTwo n).trans σ) hfin) x (t ∘ swapTwo)).subset
            rintro s ⟨hs,ht⟩
            refine ⟨hs,funext (fun i => ?_)⟩
            have hi := congrFun ht (swapTwo i)
            simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hi
          let Ω := gammaTotalRVCoordinateForm (suffixIndex PT.rvArity_le) ω
          let Ξ := gammaTotalRVCoordinateForm (suffixIndex PE.rvArity_le) ω
          let LT := gammaNativePositiveProgramTrace C hBC hv tail₂ hT.2.2.2.2
            (gamma_partial_program_final_set PT hPT) PT.volumeIndex hfinT
            (GammaGroundDefSet.univ hc B (rawRVSpace _)) (fun _ => Set.mem_univ _) Ω
          let LE := gammaNativePositiveProgramTrace C hBC hv etail₂ hE.2.2.2.2
            (gamma_partial_program_final_set PE hPE) (PE.volumeIndex ∘ swapTwo.symm) hfinE
            (GammaGroundDefSet.univ hc B (rawRVSpace _)) (fun _ => Set.mem_univ _) Ξ
          have hRelated := gammaTwo_partial_measured_rows C hBC hv hg hNames hGenerated δ hδ hδ1
            (gamma_vfPermutationImage A hA σ) (vfPermutation_finite_rv_fibres A σ hfin)
            PT PE hPT hPE swapTwo (vfPrefix_permuted_swap A σ) hfinT hfinE ω
          have hTail := gammaNativePositiveProgramTrace_value_eq (C := C) (hBC := hBC) (hv := hv)
            hg δ hδ hδ1 LT LE hRelated
          rcases LT with ⟨j,L,traceL,hL⟩
          rcases LE with ⟨k,R,traceR,hR⟩
          have hj : j = n+1 := by have h := traceL.degree; omega
          have hk : k = n+1 := by have h := traceR.degree; omega
          subst j
          subst k
          change L.finalValue C.uncountable.le C.saturated hr hg =
            R.finalValue C.uncountable.le C.saturated hr hg at hTail
          have hd : n+2 = orderedVolumeDegree n 2 := by rw [orderedVolumeDegree_eq]
          have hLeft := gammaPositive_tail_raw_value C hBC hv hg hA hfin T hT ω tail₂ hT.2.2.2.2
            (gamma_partial_program_final_set PT hPT) PT.volumeIndex hfinT (suffixIndex PT.rvArity_le) L hd hL
            (fun w => (gammaTwo_head_tail_product H H₂ tail₂ w).trans
              (Equiv.prod_comp σ.symm (fun i => w (T.program.volumeIndex i))).symm)
            (fun i => by
              have h := two_head_tail_append_density_index H H₂ tail₂ i
              rw [ordered_append_density_index] at h
              exact h)
          have hRight := gammaPositive_tail_raw_value C hBC hv hg hA hfin E hE ω etail₂ hE.2.2.2.2
            (gamma_partial_program_final_set PE hPE) (PE.volumeIndex ∘ swapTwo.symm) hfinE
            (suffixIndex PE.rvArity_le) R hd hR
            (fun w => (gammaTwo_head_tail_permuted_product K K₂ etail₂ swapTwo.symm w).trans
              (Equiv.prod_comp ((swapFirstTwo n).trans σ).symm (fun i => w (E.program.volumeIndex i))).symm)
            (fun i => by
              have h := two_head_tail_append_density_index K K₂ etail₂ i
              rw [ordered_append_density_index] at h
              exact h)
          exact hLeft.symm.trans (hTail.trans hRight)

end DiamondIntegral.Section3
