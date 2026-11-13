import «section 3».UnmeasuredTensorRankInduction
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

def gammaGroundTensorPiecesInDegree (k : ℕ) (l : List (GammaGroundUnmeasuredTensorPiece hc B)) :=
  l.filter (fun t => decide (t.residueDegree+t.gammaDegree = k))

theorem gammaGroundTensorPiecesInDegree_term_values (k : ℕ) (l : List (GammaGroundUnmeasuredTensorPiece hc B)) :
    ((gammaGroundTensorTermsInDegree k (l.map GammaGroundUnmeasuredTensorPiece.asTerm)).map
      GammaGroundUnmeasuredTensorTerm.value).sum =
    ((gammaGroundTensorPiecesInDegree k l).map GammaGroundUnmeasuredTensorPiece.value).sum := by
  simp only [gammaGroundTensorTermsInDegree,gammaGroundTensorPiecesInDegree,List.filter_map,List.map_map]
  rfl

theorem gammaGroundTensorPiecesInDegree_images_equal
    (l q : List (GammaGroundUnmeasuredTensorPiece hc B))
    (h : gammaGroundUnmeasuredTensorMap ((l.map GammaGroundUnmeasuredTensorPiece.value).sum) =
      gammaGroundUnmeasuredTensorMap ((q.map GammaGroundUnmeasuredTensorPiece.value).sum)) (k : ℕ) :
    gammaGroundUnmeasuredTensorMap (((gammaGroundTensorPiecesInDegree k l).map GammaGroundUnmeasuredTensorPiece.value).sum) =
      gammaGroundUnmeasuredTensorMap (((gammaGroundTensorPiecesInDegree k q).map GammaGroundUnmeasuredTensorPiece.value).sum) := by
  have ht : gammaGroundUnmeasuredTensorMap
      (((l.map GammaGroundUnmeasuredTensorPiece.asTerm).map GammaGroundUnmeasuredTensorTerm.value).sum) =
      gammaGroundUnmeasuredTensorMap
      (((q.map GammaGroundUnmeasuredTensorPiece.asTerm).map GammaGroundUnmeasuredTensorTerm.value).sum) := by
    rw [List.map_map,List.map_map]
    exact h
  have he := gammaGroundTensorTermsInDegree_images_equal _ _ ht k
  rw [gammaGroundTensorPiecesInDegree_term_values,gammaGroundTensorPiecesInDegree_term_values] at he
  exact he

/-- The reverse kernel inclusion for the actual positive unmeasured
tensor map, with arbitrary RES coefficients and Gamma domains. -/
theorem gammaGroundUnmeasuredTensor_kernel_generated {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (a b : GammaGroundUnmeasuredPositiveTensor hc B)
    (h : gammaGroundUnmeasuredTensorMap a = gammaGroundUnmeasuredTensorMap b) :
    gammaGroundUnmeasuredCoefficientCongruence a b := by
  obtain ⟨l,rfl⟩ := gammaGroundUnmeasuredTensor_piece_normal_form a
  obtain ⟨q,rfl⟩ := gammaGroundUnmeasuredTensor_piece_normal_form b
  let degree := fun t : GammaGroundUnmeasuredTensorPiece hc B => t.residueDegree+t.gammaDegree
  let support := ((l++q).map degree).toFinset
  have hl : ∀ t ∈ l, degree t ∈ support := by
    intro t ht
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,List.mem_append_left q ht,rfl⟩)
  have hq : ∀ t ∈ q, degree t ∈ support := by
    intro t ht
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,List.mem_append_right l ht,rfl⟩)
  rw [← positive_list_sum_by_degree degree GammaGroundUnmeasuredTensorPiece.value l support hl,
    ← positive_list_sum_by_degree degree GammaGroundUnmeasuredTensorPiece.value q support hq]
  apply gammaGroundUnmeasuredCoefficientCongruence.finsetSum support
  intro k _
  have hldegree : ∀ t ∈ gammaGroundTensorPiecesInDegree k l, t.residueDegree+t.gammaDegree = k := by
    intro t ht
    exact of_decide_eq_true (List.mem_filter.mp ht).2
  have hqdegree : ∀ t ∈ gammaGroundTensorPiecesInDegree k q, t.residueDegree+t.gammaDegree = k := by
    intro t ht
    exact of_decide_eq_true (List.mem_filter.mp ht).2
  obtain ⟨l',hl',hlrank⟩ := gammaGroundTensorPiece_homogeneous_native_charts h00
    (gammaGroundTensorPiecesInDegree k l) k hldegree (by intro t ht; have := hldegree t ht; omega)
  obtain ⟨q',hq',hqrank⟩ := gammaGroundTensorPiece_homogeneous_native_charts h00
    (gammaGroundTensorPiecesInDegree k q) k hqdegree (by intro t ht; have := hqdegree t ht; omega)
  have he := gammaGroundTensorPiecesInDegree_images_equal l q h k
  rw [hl',hq'] at he
  change gammaGroundUnmeasuredCoefficientCongruence
    (((gammaGroundTensorPiecesInDegree k l).map GammaGroundUnmeasuredTensorPiece.value).sum)
    (((gammaGroundTensorPiecesInDegree k q).map GammaGroundUnmeasuredTensorPiece.value).sum)
  rw [hl',hq']
  exact gammaGroundNativeTensor_kernel_congruence hκ hs h00 hsmall hγsmall hΓ k l' q' (Nat.le_refl k) hlrank hqrank he

theorem gammaGroundUnmeasuredCoefficientCongruence_eq_ker {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B) =
      RingCon.ker (gammaGroundUnmeasuredTensorMap (hc := hc) (ground := B)) := by
  apply le_antisymm gammaGroundUnmeasuredCoefficientCongruence_le_ker
  intro a b h
  exact gammaGroundUnmeasuredTensor_kernel_generated hκ hs h00 hsmall hγsmall hΓ a b h

theorem gammaGroundUnmeasuredCoefficientQuotientMap_bijective {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Bijective (gammaGroundUnmeasuredCoefficientQuotientMap (hc := hc) (B := B)) := by
  refine ⟨?_,gammaGroundUnmeasuredCoefficientQuotientMap_surjective hκ hs h00 hsmall hγsmall hΓ⟩
  exact RingCon.lift_injective_iff.mpr
    (gammaGroundUnmeasuredCoefficientCongruence_eq_ker hκ hs h00 hsmall hγsmall hΓ)

/-- The positive unmeasured tensor comparison after precisely the
explicit coefficient-translation congruence. -/
def gammaGroundUnmeasuredCoefficientQuotientEquiv {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    GammaGroundUnmeasuredCoefficientQuotient hc B ≃+* GammaGroundRVPositiveSemiring hc B :=
  RingEquiv.ofBijective gammaGroundUnmeasuredCoefficientQuotientMap
    (gammaGroundUnmeasuredCoefficientQuotientMap_bijective hκ hs h00 hsmall hγsmall hΓ)

@[simp] theorem gammaGroundUnmeasuredCoefficientQuotientEquiv_class {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (a : GammaGroundUnmeasuredPositiveTensor hc B) :
    gammaGroundUnmeasuredCoefficientQuotientEquiv hκ hs h00 hsmall hγsmall hΓ
      ((gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).mk' a) =
        gammaGroundUnmeasuredTensorMap a := rfl
end DiamondIntegral.Section3
