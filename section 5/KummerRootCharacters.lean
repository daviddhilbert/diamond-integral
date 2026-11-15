import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Root-choice-independent finite Kummer characters used in Remark 5.13.
These are actual algebraic automorphisms of fields. The Laurent-series
generation/basis and the inverse-limit/RV identifications remain separate
bridges; this file does not assume those identifications as inputs. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def kummerRatio (σ : L ≃ₐ[K] L) (r : L) : L := σ r / r

theorem kummerRatio_pow_one {n : ℕ} {t : K} {r : L}
    (hr : r ≠ 0) (hroot : r ^ n = algebraMap K L t) (σ : L ≃ₐ[K] L) :
    kummerRatio σ r ^ n = 1 := by
  have hfix : σ (r ^ n) = r ^ n := by rw [hroot, σ.commutes]
  change (σ r / r) ^ n = 1
  rw [div_pow, ← map_pow, hfix, div_self (pow_ne_zero n hr)]

def kummerRootRatio {n : ℕ} {t : K} {r : L}
    (hr : r ≠ 0) (hroot : r ^ n = algebraMap K L t) (σ : L ≃ₐ[K] L) :
    rootsOfUnity n L :=
  ⟨Units.mk0 (kummerRatio σ r) (div_ne_zero ((map_ne_zero σ).mpr hr) hr),
    (mem_rootsOfUnity' n _).mpr (kummerRatio_pow_one hr hroot σ)⟩

theorem rootsOfUnity_fixed_of_base {n : ℕ}
    (hbase : ∀ ζ : rootsOfUnity n L, ∃ c : K, algebraMap K L c = (ζ.val : L))
    (σ : L ≃ₐ[K] L) (ζ : rootsOfUnity n L) : σ (ζ.val : L) = (ζ.val : L) := by
  obtain ⟨c, hc⟩ := hbase ζ
  rw [← hc, σ.commutes]

theorem kummerRatio_cocycle (σ τ : L ≃ₐ[K] L) {r : L} (hr : r ≠ 0) :
    kummerRatio (σ * τ) r = σ (kummerRatio τ r) * kummerRatio σ r := by
  simp only [kummerRatio, AlgEquiv.mul_apply, map_div₀]
  field_simp [hr, (map_ne_zero σ).mpr hr]

def kummerCharacter {n : ℕ} {t : K} {r : L}
    (hr : r ≠ 0) (hroot : r ^ n = algebraMap K L t)
    (hfix : ∀ (σ : L ≃ₐ[K] L) (ζ : rootsOfUnity n L), σ (ζ.val : L) = (ζ.val : L)) :
    (L ≃ₐ[K] L) →* rootsOfUnity n L where
  toFun := kummerRootRatio hr hroot
  map_one' := by
    apply rootsOfUnity.coe_injective
    change kummerRatio (1 : L ≃ₐ[K] L) r = 1
    simp [kummerRatio, hr]
  map_mul' σ τ := by
    apply rootsOfUnity.coe_injective
    change kummerRatio (σ * τ) r = kummerRatio σ r * kummerRatio τ r
    rw [kummerRatio_cocycle σ τ hr]
    have hh := hfix σ (kummerRootRatio hr hroot τ)
    change σ (kummerRatio τ r) = kummerRatio τ r at hh
    rw [hh, mul_comm]

/-- Changing a chosen root does not change the Kummer ratio when the
relevant roots of unity are fixed by the automorphism. -/
theorem kummerRatio_root_independent {n : ℕ} {r s : L}
    (hr : r ≠ 0) (hs : s ≠ 0) (hpow : s ^ n = r ^ n)
    (σ : L ≃ₐ[K] L)
    (hfix : ∀ ζ : rootsOfUnity n L, σ (ζ.val : L) = (ζ.val : L)) :
    kummerRatio σ s = kummerRatio σ r := by
  have hζ : (s / r) ^ n = 1 := by rw [div_pow, hpow, div_self (pow_ne_zero n hr)]
  let ζ : rootsOfUnity n L :=
    ⟨Units.mk0 (s / r) (div_ne_zero hs hr), (mem_rootsOfUnity' n _).mpr hζ⟩
  have hh := hfix ζ
  change σ (s / r) = s / r at hh
  rw [map_div₀] at hh
  apply (div_eq_div_iff hs hr).mpr
  exact ((div_eq_div_iff ((map_ne_zero σ).mpr hr) hr).mp hh).trans (mul_comm s (σ r))

theorem kummerRatio_pow (σ : L ≃ₐ[K] L) (r : L) (d : ℕ) :
    kummerRatio σ (r ^ d) = kummerRatio σ r ^ d := by
  simp only [kummerRatio, map_pow, div_pow]

/-- Compatibility for arbitrary, not necessarily coherently chosen, roots
at levels n and n*d. -/
theorem kummerRatio_transition {n d : ℕ} {t : K} {r s : L}
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hroot : r ^ n = algebraMap K L t) (hsroot : s ^ (n * d) = algebraMap K L t)
    (σ : L ≃ₐ[K] L)
    (hfix : ∀ ζ : rootsOfUnity n L, σ (ζ.val : L) = (ζ.val : L)) :
    kummerRatio σ r = kummerRatio σ s ^ d := by
  have hp : (s ^ d) ^ n = r ^ n := by
    rw [← pow_mul, Nat.mul_comm d n, hsroot, hroot]
  exact (kummerRatio_root_independent hr (pow_ne_zero d hs) hp σ hfix).symm.trans
    (kummerRatio_pow σ s d)

/-- For a simple algebraic extension generated as a base algebra by r,
the ratio already determines the automorphism. -/
theorem kummerRatio_injective {r : L} (hr : r ≠ 0)
    (hgen : Algebra.adjoin K ({r} : Set L) = ⊤) :
    Function.Injective (fun σ : L ≃ₐ[K] L => kummerRatio σ r) := by
  intro σ τ h
  have he : σ r = τ r := by
    change σ r / r = τ r / r at h
    exact (div_left_inj' hr).mp h
  have hhom : σ.toAlgHom = τ.toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact he
  exact AlgEquiv.coe_toAlgHom_injective hhom

end DiamondIntegral.Section5
