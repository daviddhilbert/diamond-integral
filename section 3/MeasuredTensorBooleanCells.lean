import «section 3».TensorBooleanCells
import «section 3».MeasuredNativeGammaPartitions
import «section 3».MeasuredRESWeightPartitions
import «section 3».MeasuredLocalMonomialCongruence
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
variable (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
  (hf : FullGammaFunction (integrationGammaBase B) f)

def gammaGroundMeasuredTensorBooleanCell (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (A : Fin N → GammaGroundDefSet hc B (rawRVSpace X.obj.underlying.arity))
    (H : Fin N → GammaGroundGammaPiece hc B n) (b c : Fin N → Bool) :
    GammaGroundMeasuredPositiveTensor hc B :=
  gammaGroundMeasuredRESDirectSumClass (X.restrict (gammaGroundBooleanAtom X.obj.underlying.domain A b)
    (gammaGroundBooleanAtom_subset X.obj.underlying.domain A b)) ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (gammaGroundBooleanAtom G H c) f hf)

/-- Independent finite Boolean partitions of the two factors give a
positive tensor grid in the original degrees. -/
theorem gammaGroundMeasuredTensor_boolean_cells
    (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (A : Fin N → GammaGroundDefSet hc B (rawRVSpace X.obj.underlying.arity))
    (H : Fin N → GammaGroundGammaPiece hc B n) :
    gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      ∑ b : Fin N → Bool, ∑ c : Fin N → Bool, gammaGroundMeasuredTensorBooleanCell f hf X G A H b c := by
  have hx := gammaGroundMeasuredRESDirectSumClass_finite_partition X (gammaGroundBooleanAtom X.obj.underlying.domain A)
    (gammaGroundBooleanAtom_disjoint X.obj.underlying.domain A) (gammaGroundBooleanAtom_cover X.obj.underlying.domain A)
  have hg := gammaGroundMeasuredGammaSemiringClass_native_finite_partition G (gammaGroundBooleanAtom G H)
    (gammaGroundBooleanAtom_disjoint G H) (gammaGroundBooleanAtom_cover G H) f hf
  rw [hx,hg,TensorProduct.sum_tmul]
  simp_rw [TensorProduct.tmul_sum]
  rfl

/-- Each prescribed subrectangle is the positive sum of exactly its
selected cells in the same grid as the original product. -/
theorem gammaGroundMeasuredTensor_rectangle_boolean_cells
    (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (A : Fin N → GammaGroundDefSet hc B (rawRVSpace X.obj.underlying.arity))
    (H : Fin N → GammaGroundGammaPiece hc B n)
    (hA : ∀ i, (A i).carrier ⊆ X.obj.underlying.domain.carrier) (hH : ∀ i, (H i).carrier ⊆ G.carrier)
    (i : Fin N) :
    gammaGroundMeasuredRESDirectSumClass (X.restrict (A i) (hA i)) ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H i) f hf) =
      ∑ b : Fin N → Bool, ∑ c : Fin N → Bool,
        if b i = true ∧ c i = true then gammaGroundMeasuredTensorBooleanCell f hf X G A H b c else 0 := by
  let Xi := X.restrict (A i) (hA i)
  let I := {b : Fin N → Bool // b i = true}
  let RA : I → GammaGroundDefSet hc B (rawRVSpace X.obj.underlying.arity) := fun b => gammaGroundBooleanAtom X.obj.underlying.domain A b.val
  let GH : I → GammaGroundGammaPiece hc B n := fun c => gammaGroundBooleanAtom G H c.val
  have hdR : ∀ b c : I, b ≠ c → Disjoint (RA b).carrier (RA c).carrier := fun b c h =>
    gammaGroundBooleanAtom_disjoint X.obj.underlying.domain A b.val c.val (fun he => h (Subtype.ext he))
  have hdG : ∀ b c : I, b ≠ c → Disjoint (GH b).carrier (GH c).carrier := fun b c h =>
    gammaGroundBooleanAtom_disjoint G H b.val c.val (fun he => h (Subtype.ext he))
  have hcR : ∀ x, x ∈ Xi.obj.underlying.domain.carrier ↔ ∃ b : I, x ∈ (RA b).carrier :=
    gammaGroundBooleanAtom_selected_cover X.obj.underlying.domain A i (hA i)
  have hcG : ∀ γ, γ ∈ (H i).carrier ↔ ∃ c : I, γ ∈ (GH c).carrier :=
    gammaGroundBooleanAtom_selected_cover G H i (hH i)
  have hx := gammaGroundMeasuredRESDirectSumClass_finite_partition Xi RA hdR hcR
  have hg := gammaGroundMeasuredGammaSemiringClass_native_finite_partition (H i) GH hdG hcG f hf
  have hx' : gammaGroundMeasuredRESDirectSumClass Xi = ∑ b : I,
      gammaGroundMeasuredRESDirectSumClass (X.restrict (RA b) (gammaGroundBooleanAtom_subset X.obj.underlying.domain A b.val)) := by
    rw [hx]
    apply Finset.sum_congr rfl
    intro b _
    exact gammaGroundMeasuredRESDirectSumClass_weight_bijection _ _ (GammaGroundBijection.id (RA b)) (fun _ => rfl)
  change gammaGroundMeasuredRESDirectSumClass Xi ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H i) f hf) = _
  rw [hx',hg,TensorProduct.sum_tmul]
  simp_rw [TensorProduct.tmul_sum]
  exact positive_sum_two_subtypes_as_ite (fun b : Fin N → Bool => b i = true)
    (fun c : Fin N → Bool => c i = true) (gammaGroundMeasuredTensorBooleanCell f hf X G A H)

theorem gammaGroundMeasuredRESDirectSumClass_of_empty (X : GammaGroundMeasuredRESObject hc B r)
    (hX : X.obj.underlying.domain.carrier = ∅) : gammaGroundMeasuredRESDirectSumClass X = 0 := by
  have h : gammaGroundMeasuredRESClass X = 0 := by
    apply gammaGroundMeasuredRESToRVKPlus_injective
    simpa only [gammaGroundMeasuredRESToRVKPlus_class,map_zero] using gammaGroundMeasuredRVClass_of_empty X.obj hX
  have hh := congrArg (DirectSum.of (GammaGroundMeasuredRESKPlus hc B) r) h
  simpa only [gammaGroundMeasuredRESDirectSumClass,map_zero] using hh

theorem gammaGroundMeasuredGammaSemiringClass_native_of_empty (G : GammaGroundGammaPiece hc B n)
    (hG : G.carrier = ∅) : gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) = 0 := by
  have he : G = GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)) :=
    gammaGroundDefSet_eq_of_carrier_eq hG
  rw [he,gammaGroundMeasuredGammaSemiringClass_single_empty]

/-- A nonzero positive cell has points in both factors. The proof only
uses the zero classes of empty objects and does not use cancellation. -/
theorem gammaGroundMeasuredTensorBooleanCell_nonempty_of_ne_zero
    (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (A : Fin N → GammaGroundDefSet hc B (rawRVSpace X.obj.underlying.arity))
    (H : Fin N → GammaGroundGammaPiece hc B n) (b c : Fin N → Bool)
    (h : gammaGroundMeasuredTensorBooleanCell f hf X G A H b c ≠ 0) :
    (gammaGroundBooleanAtom X.obj.underlying.domain A b).carrier.Nonempty ∧
      (gammaGroundBooleanAtom G H c).carrier.Nonempty := by
  constructor
  · by_contra hn
    have he : (gammaGroundBooleanAtom X.obj.underlying.domain A b).carrier = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hn ⟨x,hx⟩)
    apply h
    unfold gammaGroundMeasuredTensorBooleanCell
    rw [gammaGroundMeasuredRESDirectSumClass_of_empty _ he,TensorProduct.zero_tmul]
  · by_contra hn
    have he : (gammaGroundBooleanAtom G H c).carrier = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hn ⟨x,hx⟩)
    apply h
    unfold gammaGroundMeasuredTensorBooleanCell
    rw [gammaGroundMeasuredGammaSemiringClass_native_of_empty f hf _ he,TensorProduct.tmul_zero]

/-- Any finite disjoint product partition is a positive tensor scissor
identity. Separate Boolean partitions of RES and Gamma provide one common
grid, so no equality or cancellation in RV is used as a substitute. -/
theorem gammaGroundMeasuredTensor_disjoint_product_partition
    (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (A : Fin N → GammaGroundDefSet hc B (rawRVSpace X.obj.underlying.arity))
    (H : Fin N → GammaGroundGammaPiece hc B n)
    (hA : ∀ i, (A i).carrier ⊆ X.obj.underlying.domain.carrier) (hH : ∀ i, (H i).carrier ⊆ G.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint ((A i).carrier ×ˢ (H i).carrier) ((A j).carrier ×ˢ (H j).carrier))
    (hcov : ∀ a ∈ X.obj.underlying.domain.carrier, ∀ γ ∈ G.carrier,
      ∃ i, a ∈ (A i).carrier ∧ γ ∈ (H i).carrier) :
    gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      ∑ i, gammaGroundMeasuredRESDirectSumClass (X.restrict (A i) (hA i)) ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H i) f hf) := by
  let cell := gammaGroundMeasuredTensorBooleanCell f hf X G A H
  have hs (b c : Fin N → Bool) :
      (∑ i : Fin N, if b i = true ∧ c i = true then cell b c else 0) = cell b c := by
    by_cases hz : cell b c = 0
    · simp only [hz,ite_self,Finset.sum_const_zero]
    · obtain ⟨⟨a,ha⟩,⟨γ,hγ⟩⟩ := gammaGroundMeasuredTensorBooleanCell_nonempty_of_ne_zero f hf X G A H b c hz
      obtain ⟨i,hai,hγi⟩ := hcov a ha.1 γ hγ.1
      have hi : b i = true ∧ c i = true := ⟨(ha.2 i).mp hai,(hγ.2 i).mp hγi⟩
      rw [Finset.sum_eq_single i]
      · exact ite_eq_left hi
      · intro j _ hji
        apply ite_eq_right
        intro hj
        have h1 : (a,γ) ∈ ((A i).carrier ×ˢ (H i).carrier) := ⟨hai,hγi⟩
        have h2 : (a,γ) ∈ ((A j).carrier ×ˢ (H j).carrier) :=
          ⟨(ha.2 j).mpr hj.1,(hγ.2 j).mpr hj.2⟩
        exact Set.disjoint_left.mp (hd i j (Ne.symm hji)) h1 h2
      · intro hn
        exact False.elim (hn (Finset.mem_univ i))
  calc
    _ = ∑ b : Fin N → Bool, ∑ c : Fin N → Bool, cell b c :=
      gammaGroundMeasuredTensor_boolean_cells f hf X G A H
    _ = ∑ b : Fin N → Bool, ∑ c : Fin N → Bool,
        ∑ i : Fin N, if b i = true ∧ c i = true then cell b c else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      exact (hs b c).symm
    _ = ∑ b : Fin N → Bool, ∑ i : Fin N, ∑ c : Fin N → Bool,
        if b i = true ∧ c i = true then cell b c else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ i : Fin N, ∑ b : Fin N → Bool, ∑ c : Fin N → Bool,
        if b i = true ∧ c i = true then cell b c else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (gammaGroundMeasuredTensor_rectangle_boolean_cells f hf X G A H hA hH i).symm

/-- The same positive partition theorem applies directly to actual full
RV-preimage rectangles. Temporary value representatives are proof
witnesses only; the factors and tensor identity keep the original ground. -/
theorem gammaGroundMeasuredTensor_disjoint_full_preimage_partition
    (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (A : Fin N → GammaGroundDefSet hc B (rawRVSpace X.obj.underlying.arity))
    (H : Fin N → GammaGroundGammaPiece hc B n)
    (hA : ∀ i, (A i).carrier ⊆ X.obj.underlying.domain.carrier) (hH : ∀ i, (H i).carrier ⊆ G.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint
      ((A i).prod (gammaGroundRVUnitGammaPreimage (H i))).carrier
      ((A j).prod (gammaGroundRVUnitGammaPreimage (H j))).carrier)
    (hcov : ∀ a ∈ X.obj.underlying.domain.carrier, ∀ u ∈ (gammaGroundRVUnitGammaPreimage G).carrier,
      ∃ i, a ∈ (A i).carrier ∧ u ∈ (gammaGroundRVUnitGammaPreimage (H i)).carrier) :
    gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      ∑ i, gammaGroundMeasuredRESDirectSumClass (X.restrict (A i) (hA i)) ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H i) f hf) := by
  apply gammaGroundMeasuredTensor_disjoint_product_partition f hf X G A H hA hH
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨hai,hγi⟩ ⟨haj,hγj⟩
    obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective n z.2
    have hui : rvUnitTupleValues u ∈ (H i).carrier := hu.symm ▸ hγi
    have huj : rvUnitTupleValues u ∈ (H j).carrier := hu.symm ▸ hγj
    have h1 : (z.1,u) ∈ ((A i).prod (gammaGroundRVUnitGammaPreimage (H i))).carrier := ⟨hai,hui⟩
    have h2 : (z.1,u) ∈ ((A j).prod (gammaGroundRVUnitGammaPreimage (H j))).carrier := ⟨haj,huj⟩
    exact Set.disjoint_left.mp (hd i j hij) h1 h2
  · intro a ha γ hγ
    obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective n γ
    have huG : u ∈ (gammaGroundRVUnitGammaPreimage G).carrier := by
      change rvUnitTupleValues u ∈ G.carrier
      exact hu.symm ▸ hγ
    obtain ⟨i,hai,hui⟩ := hcov a ha u huG
    refine ⟨i,hai,?_⟩
    change rvUnitTupleValues u ∈ (H i).carrier at hui
    exact hu ▸ hui
end DiamondIntegral.Section3
