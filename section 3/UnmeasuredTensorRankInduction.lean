import «section 3».RankLayerResidualAtlas
import «section 3».RankLayerResidualCovers
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k m n : ℕ}

def GammaGroundTensorRankLayerTwoSidedCover.sourceFamily
    {L R : GammaGroundTensorRankLayer hc B k m}
    {F : GammaGroundBijection L.object.domain R.object.domain}
    (C : GammaGroundTensorRankLayerTwoSidedCover L R F) :
    GammaGroundTensorRankLayerMatchedFamily L C.MatchedIndex :=
  ⟨fun c => c.1,C.sourceBox,C.sourceMap_disjoint⟩

def GammaGroundTensorRankLayerTwoSidedCover.targetFamily
    {L R : GammaGroundTensorRankLayer hc B k m}
    {F : GammaGroundBijection L.object.domain R.object.domain}
    (C : GammaGroundTensorRankLayerTwoSidedCover L R F) :
    GammaGroundTensorRankLayerMatchedFamily R C.MatchedIndex :=
  ⟨C.targetParent,C.targetBox,C.targetMap_disjoint⟩

/-- The actual two-sided residual construction is the induction step
for the positive unmeasured tensor kernel. -/
theorem gammaGroundTensorRankLayer_kernel_step {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (ih : ∀ l q : List (GammaGroundNativeTensorChart hc B k),
      (∀ Z ∈ l, Z.gammaDegree ≤ n) → (∀ Z ∈ q, Z.gammaDegree ≤ n) →
      gammaGroundUnmeasuredTensorMap ((l.map GammaGroundNativeTensorChart.value).sum) =
        gammaGroundUnmeasuredTensorMap ((q.map GammaGroundNativeTensorChart.value).sum) →
      gammaGroundUnmeasuredCoefficientCongruence ((l.map GammaGroundNativeTensorChart.value).sum)
        ((q.map GammaGroundNativeTensorChart.value).sum))
    (L R : GammaGroundTensorRankLayer hc B k (1+n))
    (h : gammaGroundUnmeasuredTensorMap L.value = gammaGroundUnmeasuredTensorMap R.value) :
    gammaGroundUnmeasuredCoefficientCongruence L.value R.value := by
  obtain ⟨e⟩ := L.iso_of_equal_images R h
  let F : GammaGroundBijection L.object.domain R.object.domain := e.hom
  obtain ⟨C⟩ := gammaGroundTensorRankLayer_two_sided_cover hκ hs h00 hsmall hγsmall hΓ L R F
  obtain ⟨l,hl,hlrank⟩ := C.sourceFamily.residual_lower_normal_form h00
    C.sourceHyperplanes C.source_union_or_hyperplane
  obtain ⟨q,hq,hqrank⟩ := C.targetFamily.residual_lower_normal_form h00
    C.targetHyperplanes C.target_union_or_hyperplane
  let eRes : C.sourceFamily.residualObject ≅ C.targetFamily.residualObject :=
    asIso (show _ ⟶ _ from C.residualBijection)
  have hres : gammaGroundUnmeasuredTensorMap ((l.map GammaGroundNativeTensorChart.value).sum) =
      gammaGroundUnmeasuredTensorMap ((q.map GammaGroundNativeTensorChart.value).sum) := by
    calc
      _ = gammaGroundRVSemiringClass C.sourceFamily.residualObject := by
        rw [← hl]
        exact C.sourceFamily.residual_value_image
      _ = gammaGroundRVSemiringClass C.targetFamily.residualObject := gammaGroundRVSemiringClass_iso eRes
      _ = _ := by rw [← hq]; exact C.targetFamily.residual_value_image.symm
  have hL := C.sourceFamily.value_split
  have hR := C.targetFamily.value_split
  rw [hl] at hL
  rw [hq] at hR
  rw [hL,hR]
  exact gammaGroundUnmeasuredCoefficientCongruence.add C.matched_congruence (ih l q hlrank hqrank hres)

/-- Every equality of homogeneous positive tensor images is generated
by the elementary coefficient translations, before groupification. -/
theorem gammaGroundNativeTensor_kernel_congruence {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (m : ℕ) (l q : List (GammaGroundNativeTensorChart hc B k)) (hbound : m ≤ k)
    (hl : ∀ Z ∈ l, Z.gammaDegree ≤ m) (hq : ∀ Z ∈ q, Z.gammaDegree ≤ m)
    (h : gammaGroundUnmeasuredTensorMap ((l.map GammaGroundNativeTensorChart.value).sum) =
      gammaGroundUnmeasuredTensorMap ((q.map GammaGroundNativeTensorChart.value).sum)) :
    gammaGroundUnmeasuredCoefficientCongruence ((l.map GammaGroundNativeTensorChart.value).sum)
      ((q.map GammaGroundNativeTensorChart.value).sum) := by
  induction m generalizing l q with
  | zero =>
    rw [gammaGroundNativeTensor_rank_zero_kernel_trivial l q hl hq h]
    exact gammaGroundUnmeasuredCoefficientCongruence.refl _
  | succ n ih =>
    have hb : 1+n ≤ k := by omega
    obtain ⟨L,hL⟩ := gammaGroundNativeTensor_rank_layer_normal_form l hb (by simpa only [Nat.add_comm 1 n] using hl)
    obtain ⟨R,hR⟩ := gammaGroundNativeTensor_rank_layer_normal_form q hb (by simpa only [Nat.add_comm 1 n] using hq)
    have hLR : gammaGroundUnmeasuredTensorMap L.value = gammaGroundUnmeasuredTensorMap R.value := by
      rw [← hL,← hR]
      exact h
    rw [hL,hR]
    apply gammaGroundTensorRankLayer_kernel_step hκ hs h00 hsmall hγsmall hΓ _ L R hLR
    intro l q hl hq he
    exact ih l q (by omega) hl hq he
end DiamondIntegral.Section3
