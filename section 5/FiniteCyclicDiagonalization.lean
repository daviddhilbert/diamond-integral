import «section 5».FiniteRootProjection
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RepresentationTheory.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Every finite complex cyclic representation has actual character
coordinates. This supplies the linear-algebra step in the comparison,
including the zero-dimensional representation. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Module Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem finite_cyclic_character_basis (N : ℕ+)
    (ρ : Representation ℂ (rootsOfUnity (N : ℕ) ℂ) V) :
    ∃ n : ℕ, ∃ b : Basis (Fin n) ℂ V, ∃ a : Fin n → ℤ,
      ∀ (ζ : rootsOfUnity (N : ℕ) ℂ) i,
        ρ ζ (b i) = ((ζ.val ^ a i : ℂˣ) : ℂ) • b i := by
  let ζ₀ : rootsOfUnity (N : ℕ) ℂ := finiteRootProjection N windingRootSystem
  let f : Module.End ℂ V := ρ ζ₀
  have hf : f ^ (N : ℕ) = 1 := by
    change (ρ ζ₀) ^ (N : ℕ) = 1
    rw [← map_pow]
    have hz : ζ₀ ^ (N : ℕ) = 1 := by
      apply Subtype.ext
      exact windingRootSystem.property.1 N
    rw [hz, map_one]
  have hsep : (X ^ (N : ℕ) - C (1 : ℂ)).Separable :=
    separable_X_pow_sub_C 1 (by exact_mod_cast N.ne_zero) one_ne_zero
  have hs : f.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    hsep.squarefree (by simp [hf])
  let dec := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.eigenspaces_iSupIndep hs.iSup_eigenspace_eq_top
  let I := (μ : ℂ) × Fin (Module.finrank ℂ (f.eigenspace μ))
  let b : Basis I ℂ V := dec.collectedBasis (fun μ => Module.finBasis ℂ (f.eigenspace μ))
  letI : Fintype I := FiniteDimensional.fintypeBasisIndex b
  have hv (i : I) : f.HasEigenvector i.1 (b i) :=
    ⟨dec.collectedBasis_mem _ i, b.ne_zero i⟩
  have hpow (i : I) : i.1 ^ (N : ℕ) = 1 := by
    have h := (hv i).pow_apply (N : ℕ)
    rw [hf] at h
    change b i = i.1 ^ (N : ℕ) • b i at h
    have hz : (i.1 ^ (N : ℕ) - 1) • b i = 0 := by
      rw [sub_smul, one_smul, ← h, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (b.ne_zero i))
  have hw : ∀ i : I, ∃ j : ℕ, j < (N : ℕ) ∧ (ζ₀.val : ℂ) ^ j = i.1 := by
    intro i
    exact (windingRootSystem_primitive N).eq_pow_of_pow_eq_one (hpow i)
  choose a ha_bound ha using hw
  have haction (ζ : rootsOfUnity (N : ℕ) ℂ) (i : I) :
      ρ ζ (b i) = ((ζ.val ^ (a i : ℤ) : ℂˣ) : ℂ) • b i := by
    obtain ⟨j, _, hj⟩ := (windingRootSystem_primitive N).eq_pow_of_pow_eq_one
      ((mem_rootsOfUnity' (N : ℕ) ζ.val).mp ζ.property)
    have hz : ζ = ζ₀ ^ j := by
      apply rootsOfUnity.coe_injective
      exact hj.symm
    rw [hz, map_pow]
    change (f ^ j) (b i) = _
    rw [(hv i).pow_apply]
    congr 1
    rw [← ha i]
    simp [zpow_natCast, pow_mul, Nat.mul_comm]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, b.reindex e, fun i => (a (e.symm i) : ℤ), ?_⟩
  intro ζ i
  simpa only [Basis.reindex_apply] using haction ζ (e.symm i)

end DiamondIntegral.Section5
