import «section 3».GammaGroundRVDimensionConsequences
import «section 3».GammaGroundRVFibreDimension
import «section 3».RVFibreDimension
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r : ℕ}

def gammaGroundRVFibreDimension (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) : WithBot ℕ :=
  if A.carrier.Nonempty then (gammaGroundRVFibreDim A : WithBot ℕ) else ⊥

theorem gammaGroundRVFibreDim_eq_zero_iff_finite_fibres
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) :
    gammaGroundRVFibreDim A = 0 ↔ ∀ a : Fin n → Section2.VF M,
      {t : Fin r → CanonicalRV.RVSort M | (a, t) ∈ A.carrier}.Finite := by
  constructor
  · intro hz a
    by_cases hne : (gammaGroundFixedVFFibre A a).carrier.Nonempty
    · obtain ⟨t, ht⟩ := hne
      let p : A := ⟨(a, t), ht⟩
      have hd := le_ciSup (gammaGroundRVFibreDim_bounded A) p
      change gammaGroundRVDim (gammaGroundFixedVFFibre A a) ≤ gammaGroundRVFibreDim A at hd
      rw [hz] at hd
      exact (gammaGroundRVDim_eq_zero_iff_finite _).mp (Nat.eq_zero_of_le_zero hd)
    · have he := Set.not_nonempty_iff_eq_empty.mp hne
      change (gammaGroundFixedVFFibre A a).carrier.Finite
      rw [he]
      exact Set.finite_empty
  · intro hfin
    apply Nat.eq_zero_of_le_zero
    apply ciSup_le'
    intro a
    exact ((gammaGroundRVDim_eq_zero_iff_finite _).mpr (hfin a.val.1)).le

@[simp] theorem gammaGroundRVFibreDimension_eq_bot_iff
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) :
    gammaGroundRVFibreDimension A = ⊥ ↔ A.carrier = ∅ := by
  by_cases hA : A.carrier.Nonempty
  · simp [gammaGroundRVFibreDimension, hA, Set.nonempty_iff_ne_empty.mp hA]
  · simp [gammaGroundRVFibreDimension, hA, Set.not_nonempty_iff_eq_empty.mp hA]

theorem gammaGroundRV_fibre_dimension_le
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) (a : Fin n → Section2.VF M) :
    gammaGroundRVDimension (gammaGroundFixedVFFibre A a) ≤ gammaGroundRVFibreDimension A := by
  by_cases hf : (gammaGroundFixedVFFibre A a).carrier.Nonempty
  · obtain ⟨t, ht⟩ := hf
    have hA : A.carrier.Nonempty := ⟨(a, t), ht⟩
    have hf' : (gammaGroundFixedVFFibre A a).carrier.Nonempty := ⟨t, ht⟩
    rw [gammaGroundRVDimension, if_pos hf', gammaGroundRVFibreDimension, if_pos hA]
    exact_mod_cast (le_ciSup (gammaGroundRVFibreDim_bounded A) (⟨(a, t), ht⟩ : A))
  · rw [gammaGroundRVDimension, if_neg hf]
    exact bot_le

theorem gammaGroundRV_fibre_dimension_attained
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) (hne : A.carrier.Nonempty) :
    ∃ a : Fin n → Section2.VF M,
      gammaGroundRVDimension (gammaGroundFixedVFFibre A a) = gammaGroundRVFibreDimension A := by
  obtain ⟨p, hp⟩ := gammaGroundRVFibreDim_attained A hne
  refine ⟨p.val.1, ?_⟩
  have hf : (gammaGroundFixedVFFibre A p.val.1).carrier.Nonempty := ⟨p.val.2, p.property⟩
  rw [gammaGroundRVDimension, if_pos hf, gammaGroundRVFibreDimension, if_pos hne, hp]

end DiamondIntegral.Section3
