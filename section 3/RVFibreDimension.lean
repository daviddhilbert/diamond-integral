import «section 3».RVDimensionBridge
import «section 3».DefinableBijections
import Section4.RVFibreInvariance

/-! Definition 3.2 and Lemma 3.3 (`RV:fiber:dim:same`). The value on the
empty set is bottom. The maximum is compared with the actual section 2
dimension over precisely the original base together with the VF point.
The reusable invariance theorem is applied only after that comparison. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Set
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r m s : ℕ}

def rvFibreDimension (A : DefSet (rawMixedSpace (M := M) n r) S) : WithBot ℕ := by
  classical
  exact if A.carrier.Nonempty then (rvFibreDim A : WithBot ℕ) else ⊥

theorem rvFibreDimension_eq_bot_iff (A : DefSet (rawMixedSpace (M := M) n r) S) :
    rvFibreDimension A = ⊥ ↔ A.carrier = ∅ := by
  classical
  by_cases hA : A.carrier.Nonempty
  · simp [rvFibreDimension, hA, Set.nonempty_iff_ne_empty.mp hA]
  · simp [rvFibreDimension, hA, Set.not_nonempty_iff_eq_empty.mp hA]

/-- Every original-base fibre dimension is bounded by the stated maximum,
including fibres that are empty and points outside the VF projection. -/
theorem rv_fibre_dimension_le (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n r) S) (a : Fin n → Section2.VF M) :
    Section2.rvDimension (S ∪ Set.range (vfValues a)) (fixedVFFibre A a).carrier ≤
      rvFibreDimension A := by
  classical
  by_cases hf : (fixedVFFibre A a).carrier.Nonempty
  · obtain ⟨t, ht⟩ := hf
    have hA : A.carrier.Nonempty := ⟨(a, t), ht⟩
    rw [rvDimension_eq_companion hc _ ⟨t, ht⟩, rvFibreDimension, if_pos hA]
    exact_mod_cast (le_ciSup (rvFibreDim_bounded A) (⟨(a, t), ht⟩ : A))
  · have he := Set.not_nonempty_iff_eq_empty.mp hf
    rw [he, Section2.rvDimension_empty]
    exact bot_le

/-- On a nonempty set the bound is attained by an actual VF fibre.
Together with `rv_fibre_dimension_le`, this identifies Definition 3.2
with the maximum of the section 2 dimensions, rather than a new rank. -/
theorem rv_fibre_dimension_attained (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hne : A.carrier.Nonempty) :
    ∃ a : Fin n → Section2.VF M,
      Section2.rvDimension (S ∪ Set.range (vfValues a)) (fixedVFFibre A a).carrier =
        rvFibreDimension A := by
  obtain ⟨p, hp⟩ := rvFibreDim_attained A hne
  refine ⟨p.val.1, ?_⟩
  have hf : (fixedVFFibre A p.val.1).carrier.Nonempty := ⟨p.val.2, p.property⟩
  rw [rvDimension_eq_companion hc _ hf, rvFibreDimension, if_pos hne, hp]

theorem rv_fibre_dimension_le_zero_iff (A : DefSet (rawMixedSpace (M := M) n r) S) :
    rvFibreDimension A ≤ 0 ↔ ∀ a : Fin n → Section2.VF M,
      {t : Fin r → Section2.RVInfinity M | (a, t) ∈ A.carrier}.Finite := by
  classical
  constructor
  · intro h
    by_cases hA : A.carrier.Nonempty
    · have hd : rvFibreDim A ≤ 0 := by
        have hh : (rvFibreDim A : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := by
          simpa only [rvFibreDimension, if_pos hA, Nat.cast_zero] using h
        exact_mod_cast hh
      exact (rvFibreDim_eq_zero_iff_finite_fibres A).mp (Nat.eq_zero_of_le_zero hd)
    · intro a
      have he : {t : Fin r → Section2.RVInfinity M | (a, t) ∈ A.carrier} = ∅ := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun ht => hA ⟨(a, t), ht⟩
      rw [he]
      exact Set.finite_empty
  · intro h
    have hd := (rvFibreDim_eq_zero_iff_finite_fibres A).mpr h
    unfold rvFibreDimension
    split_ifs <;> simp [hd]

/-- Lemma 3.3 at a fixed small real base. The hypotheses of the imported
rank theorem are discharged using the earlier RV exchange theorem. No
new assumption of dimension invariance is introduced. -/
theorem lemma_3_3 (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk S < κ)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : DefinableBijection A B) :
    rvFibreDimension A = rvFibreDimension B := by
  classical
  have hne : A.carrier.Nonempty ↔ B.carrier.Nonempty := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨(f.map ⟨a, ha⟩).val, (f.map ⟨a, ha⟩).property⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha⟩ := f.bijective.surjective ⟨b, hb⟩
      exact ⟨a.val, a.property⟩
  have hd := SpecialTransformations.Section4.lemma_4_13 hc
    (rvExchangeInput_of_earlier hκ hs h00) hκ hs hsmall f.map f.bijective
  unfold rvFibreDimension
  rw [hne, hd]

end DiamondIntegral.Section3
