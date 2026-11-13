import «section 3».MeasuredTensorRankInduction
import «section 3».MeasuredTensorDegreeReassembly
import Mathlib.RingTheory.Congruence.Hom
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

/-- The reverse kernel inclusion for the actual positive measured
tensor map, with arbitrary RES coefficients and Gamma domains. -/
theorem gammaGroundMeasuredTensor_kernel_generated {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (a b : GammaGroundMeasuredPositiveTensor hc B)
    (h : gammaGroundMeasuredTensorMap a = gammaGroundMeasuredTensorMap b) :
    gammaGroundMeasuredCoefficientCongruence a b := by
  obtain ⟨l,rfl⟩ := gammaGroundMeasuredTensor_normalized_piece_normal_form hκ hs h00 hsmall hγsmall a
  obtain ⟨q,rfl⟩ := gammaGroundMeasuredTensor_normalized_piece_normal_form hκ hs h00 hsmall hγsmall b
  let degree := fun t : GammaGroundNormalizedMeasuredTensorPiece hc B => t.residueDegree+t.gammaDegree
  let support := ((l++q).map degree).toFinset
  have hl : ∀ t ∈ l, degree t ∈ support := by
    intro t ht
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,List.mem_append_left q ht,rfl⟩)
  have hq : ∀ t ∈ q, degree t ∈ support := by
    intro t ht
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,List.mem_append_right l ht,rfl⟩)
  rw [← positive_list_sum_by_degree degree GammaGroundNormalizedMeasuredTensorPiece.value l support hl,
    ← positive_list_sum_by_degree degree GammaGroundNormalizedMeasuredTensorPiece.value q support hq]
  apply gammaGroundMeasuredCoefficientCongruence.finsetSum support
  intro k _
  have hldegree : ∀ t ∈ gammaGroundMeasuredTensorPiecesInDegree k l, t.residueDegree+t.gammaDegree = k := by
    intro t ht
    exact of_decide_eq_true (List.mem_filter.mp ht).2
  have hqdegree : ∀ t ∈ gammaGroundMeasuredTensorPiecesInDegree k q, t.residueDegree+t.gammaDegree = k := by
    intro t ht
    exact of_decide_eq_true (List.mem_filter.mp ht).2
  obtain ⟨l',hl',hlrank⟩ := gammaGroundMeasuredTensorPiece_homogeneous_native_charts h00
    (gammaGroundMeasuredTensorPiecesInDegree k l) k hldegree
  obtain ⟨q',hq',hqrank⟩ := gammaGroundMeasuredTensorPiece_homogeneous_native_charts h00
    (gammaGroundMeasuredTensorPiecesInDegree k q) k hqdegree
  have he := gammaGroundMeasuredTensorPiecesInDegree_images_equal l q h k
  rw [hl',hq'] at he
  change gammaGroundMeasuredCoefficientCongruence
    (((gammaGroundMeasuredTensorPiecesInDegree k l).map GammaGroundNormalizedMeasuredTensorPiece.value).sum)
    (((gammaGroundMeasuredTensorPiecesInDegree k q).map GammaGroundNormalizedMeasuredTensorPiece.value).sum)
  rw [hl',hq']
  exact gammaGroundMeasuredNativeTensor_kernel_congruence hκ hs h00 hsmall hγsmall hΓ k l' q' (Nat.le_refl k) hlrank hqrank he

theorem gammaGroundMeasuredCoefficientCongruence_eq_ker {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B) =
      RingCon.ker (gammaGroundMeasuredTensorMap (hc := hc) (ground := B)) := by
  apply le_antisymm gammaGroundMeasuredCoefficientCongruence_le_ker
  intro a b h
  exact gammaGroundMeasuredTensor_kernel_generated hκ hs h00 hsmall hγsmall hΓ a b h

theorem gammaGroundMeasuredCoefficientQuotientMap_bijective {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Bijective (gammaGroundMeasuredCoefficientQuotientMap (hc := hc) (B := B)) := by
  refine ⟨?_,gammaGroundMeasuredCoefficientQuotientMap_surjective hκ hs h00 hsmall hγsmall hΓ⟩
  exact RingCon.lift_injective_iff.mpr
    (gammaGroundMeasuredCoefficientCongruence_eq_ker hκ hs h00 hsmall hγsmall hΓ)

/-- The positive measured tensor comparison after precisely the
explicit coefficient-translation congruence. -/
def gammaGroundMeasuredCoefficientQuotientEquiv {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    GammaGroundMeasuredCoefficientQuotient hc B ≃+* GammaGroundMeasuredRVPositiveSemiring hc B :=
  RingEquiv.ofBijective gammaGroundMeasuredCoefficientQuotientMap
    (gammaGroundMeasuredCoefficientQuotientMap_bijective hκ hs h00 hsmall hγsmall hΓ)

@[simp] theorem gammaGroundMeasuredCoefficientQuotientEquiv_class {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (a : GammaGroundMeasuredPositiveTensor hc B) :
    gammaGroundMeasuredCoefficientQuotientEquiv hκ hs h00 hsmall hγsmall hΓ
      ((gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).mk' a) =
        gammaGroundMeasuredTensorMap a := rfl
end DiamondIntegral.Section3
