import «section 3».NativeBoxResidualPartitions
import «section 3».MeasuredTensorGridPartitions
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m : ℕ}
variable {ι J : Type} [Fintype ι] {P : Space LRV M} {U : GammaGroundDefSet hc B P}

theorem gammaGroundMeasuredTensorParentRemainder_value_split
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (hd : ∀ i l, i ≠ l → Disjoint ((t (tag i)).comp (E i).inclusion).image.carrier
      ((t (tag l)).comp (E l).inclusion).image.carrier) (f : J → (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : ∀ j, FullGammaFunction (integrationGammaBase B) (f j)) (j : J) :
    gammaGroundMeasuredRESDirectSumClass (Y j).measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H j) (f j) (hf j)) =
      (∑ a, (gammaGroundTensorChildren Y H tag E j a).measuredValue (f j) (hf j)) +
        ∑ c : GammaGroundTensorParentRemainderIndex Y H tag E j,
          (gammaGroundTensorParentRemainderBox Y H tag E j c).measuredValue (f j) (hf j) :=
  gammaGroundMeasuredTensorBox_disjoint_remainder_value_split (Y j) (H j) (f j) (hf j) (gammaGroundTensorChildren Y H tag E j)
    (gammaGroundTensorChildren_disjoint Y H t tag E hd j)

omit [Fintype ι] in
theorem gammaGroundTensorBoxInParent_measuredValue
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (f : J → (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : ∀ j, FullGammaFunction (integrationGammaBase B) (f j))
    (j : J) (i : {i // tag i = j}) :
    (gammaGroundTensorBoxInParent Y H tag E j i).measuredValue (f j) (hf j) =
      (E i.val).measuredValue (f (tag i.val)) (hf (tag i.val)) := by
  rcases i with ⟨i,he⟩
  subst j
  rfl

/-- Regrouping matched children by their parent and retaining all
residual cells gives a positive decomposition of the entire parent sum. -/
theorem gammaGroundMeasuredTensorParents_residual_value_split [Fintype J]
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (f : J → (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : ∀ j, FullGammaFunction (integrationGammaBase B) (f j))
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (hd : ∀ i l, i ≠ l → Disjoint ((t (tag i)).comp (E i).inclusion).image.carrier
      ((t (tag l)).comp (E l).inclusion).image.carrier) :
    (∑ j, gammaGroundMeasuredRESDirectSumClass (Y j).measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H j) (f j) (hf j))) =
      (∑ i : ι, (E i).measuredValue (f (tag i)) (hf (tag i))) +
        ∑ j : J, ∑ c : GammaGroundTensorParentRemainderIndex Y H tag E j,
          (gammaGroundTensorParentRemainderBox Y H tag E j c).measuredValue (f j) (hf j) := by
  have hp (j : J) := gammaGroundMeasuredTensorParentRemainder_value_split Y H t tag E hd f hf j
  calc
    _ = ∑ j : J, ((∑ a, (gammaGroundTensorChildren Y H tag E j a).measuredValue (f j) (hf j)) +
        ∑ c : GammaGroundTensorParentRemainderIndex Y H tag E j,
          (gammaGroundTensorParentRemainderBox Y H tag E j c).measuredValue (f j) (hf j)) :=
      Finset.sum_congr rfl (fun j _ => hp j)
    _ = (∑ j : J, ∑ a, (gammaGroundTensorChildren Y H tag E j a).measuredValue (f j) (hf j)) + _ := Finset.sum_add_distrib
    _ = (∑ j : J, ∑ i : {i // tag i = j}, (E i.val).measuredValue (f (tag i.val)) (hf (tag i.val))) + _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have he := Equiv.sum_comp (gammaGroundTensorChildEnumeration tag j)
        (fun i => (gammaGroundTensorBoxInParent Y H tag E j i).measuredValue (f j) (hf j))
      change (∑ a, (gammaGroundTensorBoxInParent Y H tag E j (gammaGroundTensorChildEnumeration tag j a)).measuredValue (f j) (hf j)) = _
      rw [he]
      exact Finset.sum_congr rfl (fun i _ => gammaGroundTensorBoxInParent_measuredValue Y H tag E f hf j i)
    _ = _ := by rw [positive_sum_fibres tag (fun i => (E i).measuredValue (f (tag i)) (hf (tag i)))]
end DiamondIntegral.Section3
