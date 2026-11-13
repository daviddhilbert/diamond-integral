import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A quotient element is nonzero if each finite set of defining
relations has a finite-characteristic character that separates it.
Only finitely many relations occur in any ideal-membership witness. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.FiniteRelationSeparation
variable {R : Type*} [CommRing R]

theorem not_mem_span (relations : Set R) (x : R)
    (separate : ∀ s : Finset R, (s : Set R) ⊆ relations →
      ∃ n : ℕ, ∃ f : R →+* ZMod n, f x ≠ 0 ∧ ∀ r ∈ s, f r = 0) :
    x ∉ Ideal.span relations := by
  intro hx
  obtain ⟨s, hs, hxs⟩ := Submodule.mem_span_finite_of_mem_span hx
  obtain ⟨n, f, hfx, hf⟩ := separate s hs
  have hle : Ideal.span (s : Set R) ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro r hr
    exact hf r hr
  exact hfx (hle hxs)

theorem quotient_ne_zero (relations : Set R) (x : R)
    (separate : ∀ s : Finset R, (s : Set R) ⊆ relations →
      ∃ n : ℕ, ∃ f : R →+* ZMod n, f x ≠ 0 ∧ ∀ r ∈ s, f r = 0) :
    Ideal.Quotient.mk (Ideal.span relations) x ≠ 0 := by
  intro hx
  exact not_mem_span relations x separate (Ideal.Quotient.eq_zero_iff_mem.mp hx)

end DiamondIntegral.Section4.FiniteRelationSeparation
