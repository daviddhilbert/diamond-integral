import «section 3».GammaNativeProgramRawValues
import «section 3».GammaNativePointFullMeasuredPermutations

/-! A full measured Gamma map changing the first coordinate of a
specified standard order preserves the literal raw contraction class.
Coordinate permutations use their actual Gamma Jacobian certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaStandard_relative_measured_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {n a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfinD : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier D}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (η : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) b)))
    (F : GammaFullMeasuredBijection
      (gammaPointMeasuredData A hA hfinA (gammaPointRetainedForm A hA
        (GammaGroundDefSet.univ hc B (rawRVSpace a)) id (fun _ => Set.mem_univ _) ω))
      (gammaPointMeasuredData D hD hfinD (gammaPointRetainedForm D hD
        (GammaGroundDefSet.univ hc B (rawRVSpace b)) id (fun _ => Set.mem_univ _) η)))
    {σ : Equiv.Perm (Fin (n+1))}
    (hi : ∀ p, ∀ j, j ≠ σ 0 → (F.map.map p).val.1 j = p.val.1 j)
    (T : StandardContraction A σ) (W : StandardContraction D σ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfinA T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hD hfinD W hW η) := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let PA := gammaNativeFullMeasuredPermutation C hBC hv A hA hfinA
    (GammaGroundDefSet.univ hc B (rawRVSpace a)) (fun _ => Set.mem_univ _) ω σ
  let PD := gammaNativeFullMeasuredPermutation C hBC hv D hD hfinD
    (GammaGroundDefSet.univ hc B (rawRVSpace b)) (fun _ => Set.mem_univ _) η σ
  let K := ((PA.symm C.uncountable.le C.saturated hr hv).comp C.uncountable.le C.saturated hr hv F).comp
    C.uncountable.le C.saturated hr hv PD
  have hK : ∀ p, ∀ j, j ≠ 0 → (K.map.map p).val.1 j = p.val.1 j := by
    intro p j hj
    let q := PA.map.symm.map p
    have hq : PA.map.map q = p := PA.map.map.apply_inverse PA.map.bijective p
    have hpi := congrArg (fun r => r.val.1 j) hq
    rw [gammaNativeFullMeasuredPermutation_VF] at hpi
    change (PD.map.map (F.map.map q)).val.1 j = p.val.1 j
    rw [gammaNativeFullMeasuredPermutation_VF]
    exact (hi q (σ j) (fun he => hj (σ.injective he))).trans hpi
  rw [← gammaNativeFullProgramValue_raw C hBC hv hg hA hfinA T hT ω,
    ← gammaNativeFullProgramValue_raw C hBC hv hg hD hfinD W hW η]
  exact gammaNativeFullProgramValue_relative C hBC hv hg δ hδ hδ1 T.program W.program hT hW
    (gamma_vfPermutationImage A hA σ) (gamma_vfPermutationImage D hD σ)
    (vfPermutation_finite_rv_fibres A σ hfinA) (vfPermutation_finite_rv_fibres D σ hfinD)
    (GammaGroundDefSet.univ hc B (rawRVSpace a)) (GammaGroundDefSet.univ hc B (rawRVSpace b))
    (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) ω η K hK

end DiamondIntegral.Section3
