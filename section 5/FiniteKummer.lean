import «section 5».KummerRootCharacters
import Mathlib.FieldTheory.KummerExtension

/-! Finite Kummer classification in an actual simple field extension.
The irreducibility and generation hypotheses are displayed explicitly.
The later Laurent-series bridge must prove them at each finite level. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Polynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} {a : K} {r : L}

/-- A generating root and a primitive root of unity make the extension
an actual splitting field; no splitting-field instance is an input. -/
theorem kummerSplittingField (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hroot : r ^ n = algebraMap K L a)
    (hgen : Algebra.adjoin K ({r} : Set L) = ⊤) :
    IsSplittingField K L (X ^ n - C a) := {
  splits' := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hζ.map_of_injective (algebraMap K L).injective) hroot
  adjoin_rootSet' := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero hn a)]
    simp [hroot]
}

/-- Every finite character is realized, with its values in the base field. -/
def finiteKummerEquiv {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hirr : Irreducible (X ^ n - C a))
    (hroot : r ^ n = algebraMap K L a)
    (hgen : Algebra.adjoin K ({r} : Set L) = ⊤) :
    (L ≃ₐ[K] L) ≃* rootsOfUnity n K := by
  letI : NeZero n := ⟨ne_zero_of_irreducible_X_pow_sub_C hirr⟩
  letI := kummerSplittingField (NeZero.pos n) hζ hroot hgen
  exact autEquivRootsOfUnity
    ⟨ζ, (mem_primitiveRoots (NeZero.pos n)).mpr hζ⟩ hirr L

theorem finiteKummerEquiv_smul {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hirr : Irreducible (X ^ n - C a))
    (hroot : r ^ n = algebraMap K L a)
    (hgen : Algebra.adjoin K ({r} : Set L) = ⊤) (σ : L ≃ₐ[K] L) :
    ((finiteKummerEquiv hζ hirr hroot hgen σ).val : K) • r = σ r := by
  letI : NeZero n := ⟨ne_zero_of_irreducible_X_pow_sub_C hirr⟩
  letI := kummerSplittingField (NeZero.pos n) hζ hroot hgen
  exact autEquivRootsOfUnity_smul
    ⟨ζ, (mem_primitiveRoots (NeZero.pos n)).mpr hζ⟩ hirr L hroot σ

theorem finiteKummerEquiv_ratio {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hirr : Irreducible (X ^ n - C a)) (hr : r ≠ 0)
    (hroot : r ^ n = algebraMap K L a)
    (hgen : Algebra.adjoin K ({r} : Set L) = ⊤) (σ : L ≃ₐ[K] L) :
    algebraMap K L ((finiteKummerEquiv hζ hirr hroot hgen σ).val : K) =
      kummerRatio σ r := by
  apply (eq_div_iff hr).mpr
  exact (Algebra.smul_def _ _).symm.trans
    (finiteKummerEquiv_smul hζ hirr hroot hgen σ)

/-- The inverse classification gives the actual automorphism for a multiplier. -/
def finiteKummerAutomorphism {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hirr : Irreducible (X ^ n - C a))
    (hroot : r ^ n = algebraMap K L a)
    (hgen : Algebra.adjoin K ({r} : Set L) = ⊤) (η : rootsOfUnity n K) :
    L ≃ₐ[K] L := (finiteKummerEquiv hζ hirr hroot hgen).symm η

theorem finiteKummerAutomorphism_root {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hirr : Irreducible (X ^ n - C a))
    (hroot : r ^ n = algebraMap K L a)
    (hgen : Algebra.adjoin K ({r} : Set L) = ⊤) (η : rootsOfUnity n K) :
    finiteKummerAutomorphism hζ hirr hroot hgen η r = (η.val : K) • r := by
  have h := finiteKummerEquiv_smul hζ hirr hroot hgen
    (finiteKummerAutomorphism hζ hirr hroot hgen η)
  rw [finiteKummerAutomorphism, MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem finiteKummer_degree {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hirr : Irreducible (X ^ n - C a))
    (hroot : r ^ n = algebraMap K L a)
    (hgen : Algebra.adjoin K ({r} : Set L) = ⊤) : Module.finrank K L = n := by
  have hn := Nat.pos_of_ne_zero (ne_zero_of_irreducible_X_pow_sub_C hirr)
  letI := kummerSplittingField hn hζ hroot hgen
  exact finrank_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩ hirr L

end DiamondIntegral.Section5
