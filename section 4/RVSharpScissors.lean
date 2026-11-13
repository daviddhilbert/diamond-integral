import «section 4».RVSharpCharts
import «section 4».RVMeasuredGroup
import «section 4».GammaChartOperations

/-! Taking full proper RV preimages preserves actual weighted scissors
and empty Gamma charts over the original parameter base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVSharpScissors
open RVMeasuredCharts RVMeasuredGroup RVSharpCharts GammaRVChartPresentation
open GammaOrderLogic GammaDefinableMaps GammaChartOperations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def weightedRaw {n : ℕ}
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (u : Fin n → M) : Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M) :=
  ⟨n, u, GammaWeightProfiles.correctedWeight μ (codeValues u)⟩

theorem weightedRaw_injective {n : ℕ}
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    Function.Injective (weightedRaw μ) := by
  intro u v h
  have he : (u, GammaWeightProfiles.correctedWeight μ (codeValues u)) =
      (v, GammaWeightProfiles.correctedWeight μ (codeValues v)) :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact congrArg Prod.fst he

theorem packed_ofTotal (B : Base (M := M)) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    packed (sharpChart (ofTotal B n I hI μ hμ)) = weightedRaw μ '' sharp I := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.val, u.property, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩

theorem sharp_union {n : ℕ} (I J : Set (Fin n → Values.Gamma (M := M))) :
    sharp (I ∪ J) = sharp I ∪ sharp J := by
  ext u
  change (Proper u ∧ (codeValues u ∈ I ∨ codeValues u ∈ J)) ↔
    ((Proper u ∧ codeValues u ∈ I) ∨ (Proper u ∧ codeValues u ∈ J))
  exact and_or_left

theorem sharp_inter {n : ℕ} (I J : Set (Fin n → Values.Gamma (M := M))) :
    sharp (I ∩ J) = sharp I ∩ sharp J := by
  ext u
  change (Proper u ∧ (codeValues u ∈ I ∧ codeValues u ∈ J)) ↔
    ((Proper u ∧ codeValues u ∈ I) ∧ (Proper u ∧ codeValues u ∈ J))
  tauto

theorem sharp_scissor (B : Base (M := M)) (n : ℕ)
    (I J : Set (Fin n → Values.Gamma (M := M)))
    (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
    (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    Scissor (sharpChart (ofTotal B n I hI μ hμ)) (sharpChart (ofTotal B n J hJ μ hμ))
      (sharpChart (ofTotal B n (I ∪ J) hU μ hμ)) (sharpChart (ofTotal B n (I ∩ J) hN μ hμ)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [packed_ofTotal, packed_ofTotal, packed_ofTotal, sharp_union, Set.image_union]
  · rw [packed_ofTotal, packed_ofTotal, packed_ofTotal, sharp_inter, Set.image_inter (weightedRaw_injective μ)]

theorem sharp_empty (B : Base (M := M)) (n : ℕ)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    (sharpChart (ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) μ hμ)).domain = ∅ := by
  ext u
  change (Proper u ∧ codeValues u ∈ (∅ : Set (Fin n → Values.Gamma (M := M)))) ↔ False
  exact ⟨fun h => h.2, fun h => h.elim⟩

end DiamondIntegral.Section4.RVSharpScissors
