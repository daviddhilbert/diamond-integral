import «section 3».MeasuredNativeProductPartitions
import «section 3».MeasuredTensorBoxValues
import «section 3».TensorBoxRemainderPartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r n N : ℕ}

theorem gammaGroundMeasuredTensorGridBox_value_sum
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (H : Fin N → GammaGroundGammaPiece hc B n) :
    gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      ∑ bc, (gammaGroundTensorGridBox X G A H bc).measuredValue f hf := by
  apply X.measured_finite_disjoint_full_preimage_partition G f hf
    (fun bc => (gammaGroundTensorGridBox X G A H bc).residue)
    (fun bc => (gammaGroundTensorGridBox X G A H bc).gamma)
    (fun bc => (gammaGroundTensorGridBox X G A H bc).residue_subset)
    (fun bc => (gammaGroundTensorGridBox X G A H bc).gamma_subset)
    (gammaGroundTensorGridBox_disjoint X G A H)
  intro u hu a ha
  exact gammaGroundTensorGridBox_cover X G A H ⟨(u,a),hu,ha⟩

/-- Source selection retains a positive identity with the complete
Gamma weight on every matched and residual product cell. -/
theorem gammaGroundMeasuredTensorGrid_selected_value_split
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (H : Fin N → GammaGroundGammaPiece hc B n) :
    gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      (∑ bc : GammaGroundTensorGridCoveredIndex X G A H, (gammaGroundTensorGridBox X G A H bc.val).measuredValue f hf) +
      (∑ bc : GammaGroundTensorGridUncoveredIndex X G A H, (gammaGroundTensorGridBox X G A H bc.val).measuredValue f hf) := by
  rw [gammaGroundMeasuredTensorGridBox_value_sum X G f hf A H,
    positive_sum_subtype_as_ite (fun bc => gammaGroundTensorGridNonempty X G A H bc ∧ gammaGroundTensorGridSelected bc)
      (fun bc => (gammaGroundTensorGridBox X G A H bc).measuredValue f hf),
    positive_sum_subtype_as_ite (fun bc => gammaGroundTensorGridNonempty X G A H bc ∧ ¬ gammaGroundTensorGridSelected bc)
      (fun bc => (gammaGroundTensorGridBox X G A H bc).measuredValue f hf),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro bc _
  by_cases hne : gammaGroundTensorGridNonempty X G A H bc
  · by_cases hs : gammaGroundTensorGridSelected bc <;> simp [hne,hs]
  · have hz := (gammaGroundTensorGridBox X G A H bc).measuredValue_eq_zero_of_not_nonempty f hf hne
    simp [hne,hz]

/-- Whole disjoint matched target boxes and their residual grid form a
positive partition with the prescribed full target Gamma weight. -/
theorem gammaGroundMeasuredTensorBox_disjoint_remainder_value_split
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (E : Fin N → GammaGroundTensorBox X G)
    (hd : ∀ i j, i ≠ j → Disjoint (E i).source.carrier (E j).source.carrier) :
    gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      (∑ i, (E i).measuredValue f hf) +
      ∑ c : GammaGroundTensorGridUncoveredIndex X G (fun i => (E i).residue) (fun i => (E i).gamma),
        (gammaGroundTensorGridBox X G (fun i => (E i).residue) (fun i => (E i).gamma) c.val).measuredValue f hf := by
  calc
    _ = ∑ i : GammaGroundTensorRemainderIndex E, (gammaGroundTensorRemainderBox E i).measuredValue f hf := by
      apply X.measured_finite_disjoint_full_preimage_partition G f hf
        (fun i => (gammaGroundTensorRemainderBox E i).residue) (fun i => (gammaGroundTensorRemainderBox E i).gamma)
        (fun i => (gammaGroundTensorRemainderBox E i).residue_subset) (fun i => (gammaGroundTensorRemainderBox E i).gamma_subset)
        (gammaGroundTensorRemainderBox_disjoint E hd)
      intro u hu a ha
      exact gammaGroundTensorRemainderBox_cover E ⟨(u,a),hu,ha⟩
    _ = _ := Fintype.sum_sum_type _
end DiamondIntegral.Section3
