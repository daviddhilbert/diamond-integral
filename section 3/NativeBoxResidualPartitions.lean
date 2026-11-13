import «section 3».NativeBoxImagePullback
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

def gammaGroundTensorChildEnumeration (tag : ι → J) (j : J) :=
  (Fintype.equivFin {i // tag i = j}).symm

def gammaGroundTensorChildren
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i))) (j : J) :=
  fun a => gammaGroundTensorBoxInParent Y H tag E j (gammaGroundTensorChildEnumeration tag j a)

abbrev GammaGroundTensorParentRemainderIndex
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i))) (j : J) :=
  GammaGroundTensorGridUncoveredIndex (Y j) (H j)
    (fun a => (gammaGroundTensorChildren Y H tag E j a).residue)
    (fun a => (gammaGroundTensorChildren Y H tag E j a).gamma)

def gammaGroundTensorParentRemainderBox
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i))) (j : J)
    (c : GammaGroundTensorParentRemainderIndex Y H tag E j) : GammaGroundTensorBox (Y j) (H j) :=
  gammaGroundTensorGridBox (Y j) (H j)
    (fun a => (gammaGroundTensorChildren Y H tag E j a).residue)
    (fun a => (gammaGroundTensorChildren Y H tag E j a).gamma) c.val

theorem gammaGroundTensorChildren_disjoint
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (hd : ∀ i l, i ≠ l → Disjoint ((t (tag i)).comp (E i).inclusion).image.carrier
      ((t (tag l)).comp (E l).inclusion).image.carrier)
    (j : J) (a b : Fin (Fintype.card {i // tag i = j})) (hab : a ≠ b) :
    Disjoint (gammaGroundTensorChildren Y H tag E j a).source.carrier
      (gammaGroundTensorChildren Y H tag E j b).source.carrier :=
  gammaGroundTensorBox_children_disjoint Y H t tag E hd j _ _
    (fun he => hab ((gammaGroundTensorChildEnumeration tag j).injective he))

theorem gammaGroundTensorParentRemainder_value_split
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (hd : ∀ i l, i ≠ l → Disjoint ((t (tag i)).comp (E i).inclusion).image.carrier
      ((t (tag l)).comp (E l).inclusion).image.carrier) (j : J) :
    gammaGroundRESDirectSumClass (Y j).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (H j)) =
      (∑ a, (gammaGroundTensorChildren Y H tag E j a).value) +
        ∑ c : GammaGroundTensorParentRemainderIndex Y H tag E j,
          (gammaGroundTensorParentRemainderBox Y H tag E j c).value :=
  gammaGroundTensorBox_disjoint_remainder_value_split (Y j) (H j) (gammaGroundTensorChildren Y H tag E j)
    (gammaGroundTensorChildren_disjoint Y H t tag E hd j)

/-- Residual cells give exactly the preimage, in one parent chart, of
the complement of all matched ambient images. -/
theorem gammaGroundTensorParentRemainder_source_cover
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (ht : ∀ j, Function.Injective (t j))
    (hd : ∀ j l, j ≠ l → Disjoint (t j).image.carrier (t l).image.carrier)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (j : J) (x : gammaGroundNativeProductDomain (Y j) (H j)) :
    (t j x).val ∉ (gammaGroundDefSetFiniteUnion Finset.univ
      (fun i => ((t (tag i)).comp (E i).inclusion).image)).carrier ↔
        ∃ c : GammaGroundTensorParentRemainderIndex Y H tag E j,
          x.val ∈ (gammaGroundTensorParentRemainderBox Y H tag E j c).source.carrier := by
  rw [gammaGroundTensorBox_child_image_pullback Y H t ht hd tag E j x]
  have he : (¬ ∃ i : {i // tag i = j}, x.val ∈ (gammaGroundTensorBoxInParent Y H tag E j i).source.carrier) ↔
      ∀ a, x.val ∉ (gammaGroundTensorChildren Y H tag E j a).source.carrier := by
    constructor
    · intro hn a ha
      exact hn ⟨gammaGroundTensorChildEnumeration tag j a,ha⟩
    · intro hn ⟨i,hi⟩
      exact hn ((gammaGroundTensorChildEnumeration tag j).symm i)
        (by simpa only [gammaGroundTensorChildren,Equiv.apply_symm_apply] using hi)
  rw [he]
  exact gammaGroundTensorGrid_uncovered_source_cover (Y j) (H j) (gammaGroundTensorChildren Y H tag E j) x

/-- The whole Gamma factor of a nonempty residual rectangle is
exceptional, provided the original parent was generically matched. -/
theorem gammaGroundTensorParentRemainder_gamma_cover
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (ht : ∀ j, Function.Injective (t j))
    (hd : ∀ j l, j ≠ l → Disjoint (t j).image.carrier (t l).image.carrier)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (Q : J → Finset (GammaGroundCharacterHyperplane B m))
    (hcover : ∀ j (x : gammaGroundNativeProductDomain (Y j) (H j)),
      (t j x).val ∈ (gammaGroundDefSetFiniteUnion Finset.univ
        (fun i => ((t (tag i)).comp (E i).inclusion).image)).carrier ∨
          ∃ h ∈ Q j, rvUnitTupleValues x.val.1 ∈ h.carrier)
    (j : J) (c : GammaGroundTensorParentRemainderIndex Y H tag E j) :
    ∀ γ ∈ (gammaGroundTensorParentRemainderBox Y H tag E j c).gamma.carrier,
      ∃ h ∈ Q j, γ ∈ h.carrier := by
  let A := gammaGroundTensorParentRemainderBox Y H tag E j c
  obtain ⟨a,ha⟩ := c.property.1.1
  intro γ hγ
  obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective m γ
  have huA : rvUnitTupleValues u ∈ A.gamma.carrier := hu.symm ▸ hγ
  let x : gammaGroundNativeProductDomain (Y j) (H j) := ⟨(u,a),A.gamma_subset huA,A.residue_subset ha⟩
  have hnot := (gammaGroundTensorParentRemainder_source_cover Y H t ht hd tag E j x).mpr ⟨c,huA,ha⟩
  rcases hcover j x with hm | ⟨h,hh,hγh⟩
  · exact False.elim (hnot hm)
  · have hv : rvUnitTupleValues u ∈ h.carrier := hγh
    exact ⟨h,hh,hu ▸ hv⟩

theorem positive_sum_fibres {A : Type} [AddCommMonoid A] [Fintype J]
    (tag : ι → J) (f : ι → A) :
    (∑ j : J, ∑ i : {i // tag i = j}, f i.val) = ∑ i, f i := by
  calc
    _ = ∑ j : J, ∑ i : ι, if tag i = j then f i else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact positive_sum_subtype_as_ite (fun i => tag i = j) f
    _ = ∑ i : ι, ∑ j : J, if tag i = j then f i else 0 := Finset.sum_comm
    _ = _ := by simp

omit [Fintype ι] in
theorem gammaGroundTensorBoxInParent_value
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (j : J) (i : {i // tag i = j}) :
    (gammaGroundTensorBoxInParent Y H tag E j i).value = (E i.val).value := by
  rcases i with ⟨i,he⟩
  subst j
  rfl

/-- Regrouping matched children by their parent and retaining all
residual cells gives a positive decomposition of the entire parent sum. -/
theorem gammaGroundTensorParents_residual_value_split [Fintype J]
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (hd : ∀ i l, i ≠ l → Disjoint ((t (tag i)).comp (E i).inclusion).image.carrier
      ((t (tag l)).comp (E l).inclusion).image.carrier) :
    (∑ j, gammaGroundRESDirectSumClass (Y j).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (H j))) =
      (∑ i : ι, (E i).value) +
        ∑ j : J, ∑ c : GammaGroundTensorParentRemainderIndex Y H tag E j,
          (gammaGroundTensorParentRemainderBox Y H tag E j c).value := by
  have hp (j : J) := gammaGroundTensorParentRemainder_value_split Y H t tag E hd j
  calc
    _ = ∑ j : J, ((∑ a, (gammaGroundTensorChildren Y H tag E j a).value) +
        ∑ c : GammaGroundTensorParentRemainderIndex Y H tag E j,
          (gammaGroundTensorParentRemainderBox Y H tag E j c).value) :=
      Finset.sum_congr rfl (fun j _ => hp j)
    _ = (∑ j : J, ∑ a, (gammaGroundTensorChildren Y H tag E j a).value) + _ := Finset.sum_add_distrib
    _ = (∑ j : J, ∑ i : {i // tag i = j}, (E i.val).value) + _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have he := Equiv.sum_comp (gammaGroundTensorChildEnumeration tag j)
        (fun i => (gammaGroundTensorBoxInParent Y H tag E j i).value)
      change (∑ a, (gammaGroundTensorBoxInParent Y H tag E j (gammaGroundTensorChildEnumeration tag j a)).value) = _
      rw [he]
      exact Finset.sum_congr rfl (fun i _ => gammaGroundTensorBoxInParent_value Y H tag E j i)
    _ = _ := by rw [positive_sum_fibres tag (fun i => (E i).value)]
end DiamondIntegral.Section3
