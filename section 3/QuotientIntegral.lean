import Mathlib.GroupTheory.Congruence.Basic

/-! The algebraic step in Theorem 3.22. Surjectivity and the exact kernel
equality are explicit mathematical premises. This module neither supplies
the HK kernel theorem nor asserts a lift over arbitrary RV parameter bases.
It applies separately to the measured and unmeasured congruences. -/

noncomputable section

namespace DiamondIntegral.Section3

universe u v

variable {R : Type u} {V : Type v} [AddMonoid R] [AddMonoid V]

def integralFromKernel (L : R →+ V) (hsurj : Function.Surjective L)
    (c : AddCon R) (hker : c = AddCon.ker L) : V ≃+ c.Quotient := by
  subst c
  exact (AddCon.quotientKerEquivOfSurjective L hsurj).symm

theorem integralFromKernel_characterization (L : R →+ V) (hsurj : Function.Surjective L)
    (c : AddCon R) (hker : c = AddCon.ker L) (a : V) (u : R) :
    integralFromKernel L hsurj c hker a = c.mk' u ↔ a = L u := by
  subst c
  exact (AddCon.quotientKerEquivOfSurjective L hsurj).symm_apply_eq

theorem integralFromKernel_unique (L : R →+ V) (hsurj : Function.Surjective L)
    (c : AddCon R) (hker : c = AddCon.ker L) (I : V →+ c.Quotient)
    (hI : ∀ u, I (L u) = c.mk' u) :
    I = (integralFromKernel L hsurj c hker).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨u, rfl⟩ := hsurj a
  exact (hI u).trans ((integralFromKernel_characterization L hsurj c hker (L u) u).mpr rfl).symm

end DiamondIntegral.Section3
