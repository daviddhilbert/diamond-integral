import «section 4».GammaPushforwardConvolution
import «section 4».GammaMeasuredProfileInvariance
import «section 4».GammaObjectPolynomial

/-! Multiplicativity of actual corrected-weight profiles on products of
definable Gamma sets. This is proved before category-class descent. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaProfileProducts
open GammaOrderLogic GammaDefinableMaps GammaSumMap GammaIntegerFamilies GammaIndicators
open GammaProductFamilies GammaWeightProfiles GammaMeasuredProfileInvariance GammaPushforwardCongruence
open GammaHigherPushforward GammaPushforwardConvolution FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def productSet {n m : ℕ} (I : Set (Fin m → Values.Gamma (M := M)))
    (J : Set (Fin n → Values.Gamma (M := M))) : Set (Fin (n + m) → Values.Gamma (M := M)) :=
  {z | z ∘ headIndex n m ∈ I ∧ z ∘ tailIndex n m ∈ J}

theorem productSet_definable (B : Base (M := M)) {n m : ℕ}
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (J : Set (Fin n → Values.Gamma (M := M))) (hJ : GammaDefinable B J) :
    GammaDefinable B (productSet I J) :=
  GammaRelationLogic.inter_definable_base B _ _
    (GammaRelationLogic.preimage_definable_base B I hI (headIndex n m))
    (GammaRelationLogic.preimage_definable_base B J hJ (tailIndex n m))

theorem productSet_indicator (B : Base (M := M)) {n m : ℕ}
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (J : Set (Fin n → Values.Gamma (M := M))) (hJ : GammaDefinable B J) :
    indicatorFamily B (productSet I J) (productSet_definable B I hI J hJ) =
      productFamily B (indicatorFamily B I hI) (indicatorFamily B J hJ) := by
  apply Subtype.ext
  funext z
  by_cases hi : z ∘ headIndex n m ∈ I <;> by_cases hj : z ∘ tailIndex n m ∈ J <;>
    simp [indicatorFamily, productFamily, productSet, hi, hj]

theorem profile_product (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n m : ℕ)
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (J : Set (Fin n → Values.Gamma (M := M))) (hJ : GammaDefinable B J)
    (μ : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (σ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hσ : MapDefinable B σ) :
    (profile h00 hκ hs B hr hγ k (productSet I J) (productSet_definable B I hI J hJ)
      (sumMap μ σ) (sumMap_definable B μ σ hμ hσ)).val =
    (profile h00 hκ hs B hr hγ k I hI μ hμ).val * (profile h00 hκ hs B hr hγ k J hJ σ hσ).val := by
  have h := pushforward_congr h00 hκ hs B B hr hγ hr hγ k
    (correctedWeight (sumMap μ σ)) (sumMap (correctedWeight μ) (correctedWeight σ))
    (correctedWeight_graph B (sumMap μ σ) (sumMap_definable B μ σ hμ hσ))
    (graph_of_mapDefinable B _ (sumMap_definable B _ _
      (correctedWeight_definable B μ hμ) (correctedWeight_definable B σ hσ)))
    (indicatorFamily B (productSet I J) (productSet_definable B I hI J hJ))
    (productFamily B (indicatorFamily B I hI) (indicatorFamily B J hJ))
    (congrFun (correctedWeight_sumMap μ σ))
    (fun z => congrArg (fun f => f.val z) (productSet_indicator B I hI J hJ))
  exact h.trans (pushforward_sum_product h00 linear hκ hs B hr hγ hΓ k n m
    (correctedWeight μ) (correctedWeight σ) (correctedWeight_definable B μ hμ) (correctedWeight_definable B σ hσ)
    (indicatorFamily B I hI) (indicatorFamily B J hJ))

end DiamondIntegral.Section4.GammaProfileProducts
