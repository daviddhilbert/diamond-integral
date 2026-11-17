import «section 3».GammaNativeHeterogeneousMeasuredValues
import «section 3».GammaRawSelectedMeasuredContractions
import «section 3».GammaNativeRetainedFullMaps
import Integration7.HeadTailSelectedVolumeSelectors

/-! A fixed actual head followed by any specified tail has the same
complete Gamma measured value as that tail with the head tag retained.
The explicit common coordinate permutation preserves the full product. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {S : Set M} {n a d : ℕ}

theorem gammaHead_tail_appended_program
    {A : SpecialTransformations.Section5.DefSet (M := M) S (n+1) a}
    (hA : GammaSetDefinable B (carrier A)) (σ : Equiv.Perm (Fin (n+1)))
    (H : HeadPreparation (vfPermutationImage A σ))
    (hH : GammaGraphDefinable B (pointMapGraph H.map))
    (hTarget : GammaSetDefinable B (carrier H.target))
    (τ : Equiv.Perm (Fin n)) (D : StandardContraction H.contractedSet τ)
    (hD : GammaProgramDefinable B D.program) :
    GammaProgramDefinable B (headTailAppendedStandardProgram σ H τ D).program := by
  apply gamma_standardFromProgram
  exact ⟨H.gamma_permute_tail_map τ (gamma_vfPermutationImage A hA σ) hTarget hH,
    H.gamma_permute_tail_target τ hTarget,
    gamma_orderedCastSource D.program (H.permute_tail_contracted_set τ).symm hD⟩

theorem gammaAppended_head_measured_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+2) a}
    (hA : GammaSetDefinable B (carrier A)) (σ : Equiv.Perm (Fin (n+2)))
    (H : HeadPreparation (vfPermutationImage A σ))
    (hH : GammaGraphDefinable B (pointMapGraph H.map))
    (hTarget : GammaSetDefinable B (carrier H.target))
    (ρ : Fin d → Fin a)
    (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hfinH : ∀ x t, {r | (x,r) ∈ carrier H.contractedSet ∧ r ∘ headVolumeIndex H ρ = t}.Finite)
    (τ : Equiv.Perm (Fin (n+1))) (D : StandardContraction H.contractedSet τ)
    (hD : GammaProgramDefinable B D.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    let η := gammaTotalRVCoordinateForm (headSelectedLabelIndex H (id : Fin a → Fin a)) ω
    let F := headTailAppendedStandardProgram σ H τ D
    let hF := gammaHead_tail_appended_program hA σ H hH hTarget τ D hD
    gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC
      (gamma_headImage H.target hTarget) (headVolumeIndex H ρ) hfinH D hD η) =
      gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin F hF ω) := by
  intro η F hF
  let U := gammaNativeRawSelectedAt C hBC (gamma_headImage H.target hTarget) (headVolumeIndex H ρ) hfinH D hD
  let V := gammaNativeRawSelectedAt C hBC hA ρ hfin F hF
  have hDom : (Section5.nativeRVGroundDomain (hc := hc) U).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) V).carrier := by
    ext r
    rw [gammaNativeRawSelected_mem,gammaNativeRawSelected_mem]
    rfl
  let f := GammaGroundBijection.ofCarrierEq hDom
  apply gammaNative_heterogeneous_measured_value (by omega) U V
    (gammaNativeTotalRVForm U (suffixIndex D.program.rvArity_le) η)
    (gammaNativeTotalRVForm V (suffixIndex F.program.rvArity_le) ω) f
  · intro u
    rw [gammaNativeRawSelected_volume,gammaNativeRawSelected_volume]
    have hSel := head_tail_selected_volume_index_rotated σ H D ρ F.volumeIndex F.program.rvArity_le
      (head_tail_appended_volume_head σ H τ D) (head_tail_appended_volume_tail σ H τ D)
      (head_tail_appended_old_index σ H τ D)
    let e := (headVolumeOrderPermutation d σ).trans (finCongr (head_tail_selected_volume_degree (n+1) d))
    calc
      _ = ∏ i, Values.vrv (u.val (selectedStandardVolumeIndex D (headVolumeIndex H ρ) (e i))) :=
        (Equiv.prod_comp e (fun j => Values.vrv (u.val (selectedStandardVolumeIndex D (headVolumeIndex H ρ) j)))).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        exact congrArg (fun j => Values.vrv (u.val j)) (congrFun hSel i)
  · intro u
    apply congrArg ω
    apply Subtype.ext
    funext i
    exact congrArg u.val (head_tail_appended_old_index σ H τ D i)

end DiamondIntegral.Section3
