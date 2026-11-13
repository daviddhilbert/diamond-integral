import «section 3».GammaGroundRVFibreComparison
import «section 3».GammaGroundVFCategories
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
theorem gammaGroundRV_fibre_dimension_le_zero_iff
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) :
    gammaGroundRVFibreDimension A ≤ 0 ↔
      ∀ a : Fin n → Section2.VF M, {t | (a, t) ∈ A.carrier}.Finite := by
  constructor
  · intro h
    by_cases hA : A.carrier.Nonempty
    · have hd : gammaGroundRVFibreDim A ≤ 0 := by
        have hh : (gammaGroundRVFibreDim A : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := by
          simpa only [gammaGroundRVFibreDimension, if_pos hA, Nat.cast_zero] using h
        exact_mod_cast hh
      exact (gammaGroundRVFibreDim_eq_zero_iff_finite_fibres A).mp (Nat.eq_zero_of_le_zero hd)
    · intro a
      have he : {t | (a, t) ∈ A.carrier} = ∅ := by
        ext t
        exact ⟨fun ht => hA ⟨(a, t), ht⟩, False.elim⟩
      rw [he]
      exact Set.finite_empty
  · intro hf
    have hd := (gammaGroundRVFibreDim_eq_zero_iff_finite_fibres A).mpr hf
    unfold gammaGroundRVFibreDimension
    split_ifs <;> simp [hd]

variable [TopologicalSpace (Section2.VF M)] {k : ℕ}
theorem GammaGroundVFObject.rvFibreDimension_le_zero (U : GammaGroundVFObject hc ground k) :
    gammaGroundRVFibreDimension U.domain ≤ 0 :=
  (gammaGroundRV_fibre_dimension_le_zero_iff U.domain).mpr U.finite

def GammaGroundVFObject.ofDimensions
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (hVF : Section2.vfDimension A.carrier ≤ (k : WithBot ℕ))
    (hRV : gammaGroundRVFibreDimension A ≤ 0) : GammaGroundVFObject hc ground k :=
  ⟨n, r, A, hVF, (gammaGroundRV_fibre_dimension_le_zero_iff A).mp hRV⟩
end DiamondIntegral.Section3
