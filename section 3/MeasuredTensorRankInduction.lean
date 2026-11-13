import «section 3».MeasuredRankLayerResidualReduction
import «section 3».MeasuredTensorRankZero
import «section 3».MeasuredRankLayerResidualCovers
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

def GammaGroundMeasuredTensorRankLayerTwoSidedCover.sourceFamily
    {L R : GammaGroundMeasuredTensorRankLayer hc B k m}
    {F : GammaGroundBijection L.object.underlying.domain R.object.underlying.domain}
    (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) :
    GammaGroundTensorRankLayerMatchedFamily L.unmeasured C.MatchedIndex :=
  ⟨fun c => c.1,C.sourceBox,C.sourceMap_disjoint⟩

def GammaGroundMeasuredTensorRankLayerTwoSidedCover.targetFamily
    {L R : GammaGroundMeasuredTensorRankLayer hc B k m}
    {F : GammaGroundBijection L.object.underlying.domain R.object.underlying.domain}
    (C : GammaGroundMeasuredTensorRankLayerTwoSidedCover L R F) :
    GammaGroundTensorRankLayerMatchedFamily R.unmeasured C.MatchedIndex :=
  ⟨C.targetParent,C.targetBox,C.targetMap_disjoint⟩

/-- The actual two-sided residual construction is the induction step
for the positive measured tensor kernel. -/
theorem gammaGroundMeasuredTensorRankLayer_kernel_step {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (ih : ∀ l q : List (GammaGroundMeasuredNativeTensorChart hc B k),
      (∀ Z ∈ l, Z.underlying.gammaDegree ≤ n) → (∀ Z ∈ q, Z.underlying.gammaDegree ≤ n) →
      gammaGroundMeasuredTensorMap ((l.map GammaGroundMeasuredNativeTensorChart.value).sum) =
        gammaGroundMeasuredTensorMap ((q.map GammaGroundMeasuredNativeTensorChart.value).sum) →
      gammaGroundMeasuredCoefficientCongruence ((l.map GammaGroundMeasuredNativeTensorChart.value).sum)
        ((q.map GammaGroundMeasuredNativeTensorChart.value).sum))
    (L R : GammaGroundMeasuredTensorRankLayer hc B k (1+n))
    (h : gammaGroundMeasuredTensorMap L.value = gammaGroundMeasuredTensorMap R.value) :
    gammaGroundMeasuredCoefficientCongruence L.value R.value := by
  obtain ⟨e⟩ := L.iso_of_equal_images R h
  let F : GammaGroundBijection L.object.underlying.domain R.object.underlying.domain := e.hom.bijection
  obtain ⟨C⟩ := gammaGroundMeasuredTensorRankLayer_two_sided_cover hκ hs h00 hsmall hγsmall hΓ L R F e.hom.preserves
  obtain ⟨l,hl,hlrank⟩ := GammaGroundMeasuredTensorResidual.lower_normal_form L C.sourceFamily hκ hs h00 hsmall hγsmall
    C.sourceHyperplanes C.source_union_or_hyperplane
  obtain ⟨q,hq,hqrank⟩ := GammaGroundMeasuredTensorResidual.lower_normal_form R C.targetFamily hκ hs h00 hsmall hγsmall
    C.targetHyperplanes C.target_union_or_hyperplane
  let HRes : GammaGroundMeasuredRVHom (GammaGroundMeasuredTensorResidual.object L C.sourceFamily)
      (GammaGroundMeasuredTensorResidual.object R C.targetFamily) :=
    { bijection := C.residualBijection
      preserves := by
        intro x
        have hs' := L.object.restrict_weight (L.object.underlying.domain.sdiff C.sourceUnion) (fun _ h => h.1) x
        have ht' := R.object.restrict_weight (R.object.underlying.domain.sdiff C.targetUnion) (fun _ h => h.1)
          (C.residualBijection.map x)
        have he : (⟨(C.residualBijection.map x).val,(C.residualBijection.map x).property.1⟩ : R.object.underlying.domain) =
            F.map ⟨x.val,x.property.1⟩ := Subtype.ext (C.residualBijection_agrees x)
        exact hs'.trans ((e.hom.preserves ⟨x.val,x.property.1⟩).trans ((congrArg R.object.combinedWeight he).symm.trans ht'.symm)) }
  let eRes : (GammaGroundMeasuredTensorResidual.object L C.sourceFamily) ≅
      (GammaGroundMeasuredTensorResidual.object R C.targetFamily) := asIso (show _ ⟶ _ from HRes)
  have hres : gammaGroundMeasuredTensorMap ((l.map GammaGroundMeasuredNativeTensorChart.value).sum) =
      gammaGroundMeasuredTensorMap ((q.map GammaGroundMeasuredNativeTensorChart.value).sum) := by
    calc
      _ = gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredTensorResidual.object L C.sourceFamily) := by
        rw [← hl]
        exact GammaGroundMeasuredTensorResidual.value_image L C.sourceFamily
      _ = gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredTensorResidual.object R C.targetFamily) := gammaGroundMeasuredRVSemiringClass_iso eRes
      _ = _ := by rw [← hq]; exact (GammaGroundMeasuredTensorResidual.value_image R C.targetFamily).symm
  have hL := GammaGroundMeasuredTensorResidual.value_split L C.sourceFamily
  have hR := GammaGroundMeasuredTensorResidual.value_split R C.targetFamily
  rw [hl] at hL
  rw [hq] at hR
  rw [hL,hR]
  exact gammaGroundMeasuredCoefficientCongruence.add C.matched_congruence (ih l q hlrank hqrank hres)

/-- Every equality of homogeneous positive tensor images is generated
by the elementary coefficient translations, before groupification. -/
theorem gammaGroundMeasuredNativeTensor_kernel_congruence {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (m : ℕ) (l q : List (GammaGroundMeasuredNativeTensorChart hc B k)) (hbound : m ≤ k)
    (hl : ∀ Z ∈ l, Z.underlying.gammaDegree ≤ m) (hq : ∀ Z ∈ q, Z.underlying.gammaDegree ≤ m)
    (h : gammaGroundMeasuredTensorMap ((l.map GammaGroundMeasuredNativeTensorChart.value).sum) =
      gammaGroundMeasuredTensorMap ((q.map GammaGroundMeasuredNativeTensorChart.value).sum)) :
    gammaGroundMeasuredCoefficientCongruence ((l.map GammaGroundMeasuredNativeTensorChart.value).sum)
      ((q.map GammaGroundMeasuredNativeTensorChart.value).sum) := by
  induction m generalizing l q with
  | zero =>
    rw [gammaGroundMeasuredNativeTensor_rank_zero_kernel_trivial l q hl hq h]
    exact gammaGroundMeasuredCoefficientCongruence.refl _
  | succ n ih =>
    have hb : 1+n ≤ k := by omega
    obtain ⟨L,hL⟩ := gammaGroundMeasuredNativeTensor_rank_layer_normal_form l hb (by simpa only [Nat.add_comm 1 n] using hl)
    obtain ⟨R,hR⟩ := gammaGroundMeasuredNativeTensor_rank_layer_normal_form q hb (by simpa only [Nat.add_comm 1 n] using hq)
    have hLR : gammaGroundMeasuredTensorMap L.value = gammaGroundMeasuredTensorMap R.value := by
      rw [← hL,← hR]
      exact h
    rw [hL,hR]
    apply gammaGroundMeasuredTensorRankLayer_kernel_step hκ hs h00 hsmall hγsmall hΓ _ L R hLR
    intro l q hl hq he
    exact ih l q (by omega) hl hq he
end DiamondIntegral.Section3
