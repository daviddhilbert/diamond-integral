import «section 4».GammaMeasuredProfileInvariance
import «section 4».GammaConstantPushforward
import «section 4».GammaFunctionPolynomial

/-! Degree-zero corrected-weight profiles are actual integer point masses
at original-base definable Gamma values, hence have the coefficient type
required by the manuscript's restricted polynomial source. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaZeroDegreeProfile
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaMeasuredProfileInvariance
open GammaIntegerFamilies GammaIndicators GammaIteratedIntegral GammaConstantPushforward EulerFunction
open GammaDefinableConvolution GammaPointAlgebra GammaNamesSubgroup

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem zero_arity_value_definable (B : Base (M := M))
    (μ : (Fin 0 → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    GammaDefinableClosureAtBase B (μ emptyTuple) := by
  apply (unary_definable_iff B {μ emptyTuple}).mp
  unfold MapDefinable at hμ
  convert hμ using 1
  ext z
  change z 0 = μ emptyTuple ↔ z 0 = μ (fun i : Fin 0 => z i.succ)
  rw [Subsingleton.elim (fun i : Fin 0 => z i.succ) emptyTuple]

theorem profile_zero_degree (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (I : Set (Fin 0 → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin 0 → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    (profile h00 hκ hs B hr hγ k I hI μ hμ).val =
      (if emptyTuple ∈ I then (1 : ℤ) else 0) • point k (toPaperGamma (μ emptyTuple)) := by
  have hconst (z : Fin 0 → Values.Gamma (M := M)) : correctedWeight μ z = μ emptyTuple := by
    have he : z = emptyTuple := Subsingleton.elim _ _
    rw [he]
    simp [correctedWeight]
  exact pushforward_constant h00 hκ hs B hr hγ k (correctedWeight μ) (correctedWeight_graph B μ hμ)
    (μ emptyTuple) hconst (indicatorFamily B I hI)

theorem profile_zero_degree_pointSubring (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (I : Set (Fin 0 → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin 0 → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    (⟨(profile h00 hκ hs B hr hγ k I hI μ hμ).val,
      (profile h00 hκ hs B hr hγ k I hI μ hμ).property⟩ : baseSubring B k) ∈ pointSubring B k := by
  let a : additiveNames B := ⟨toPaperGamma (μ emptyTuple), zero_arity_value_definable B μ hμ⟩
  refine ⟨AddMonoidAlgebra.single a (if emptyTuple ∈ I then (1 : ℤ) else 0), ?_⟩
  apply Subtype.ext
  rw [pointGroupRing_single]
  exact (profile_zero_degree h00 hκ hs B hr hγ k I hI μ hμ).symm

end DiamondIntegral.Section4.GammaZeroDegreeProfile
