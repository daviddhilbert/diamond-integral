import «section 3».GroupifiedCongruences

/-! Semiring isomorphisms extend canonically to their ring completions. -/

noncomputable section
namespace DiamondIntegral.Section3
open Algebra.GrothendieckAddGroup
universe u v
variable {R : Type u} {T : Type v} [CommSemiring R] [CommSemiring T]

def ringCompletionCongr (e : R ≃+* T) : RingCompletion R ≃+* RingCompletion T := by
  let F := liftRingHom (ofRingHom.comp e.toRingHom)
  let B := liftRingHom (ofRingHom.comp e.symm.toRingHom)
  have hBF : B.comp F = RingHom.id _ := by
    apply ringHom_ext
    intro a
    change B (F (of a)) = of a
    rw [show F (of a) = of (e a) from liftRingHom_apply_of _ _]
    rw [show B (of (e a)) = of (e.symm (e a)) from liftRingHom_apply_of _ _, e.symm_apply_apply]
  have hFB : F.comp B = RingHom.id _ := by
    apply ringHom_ext
    intro a
    change F (B (of a)) = of a
    rw [show B (of a) = of (e.symm a) from liftRingHom_apply_of _ _]
    rw [show F (of (e.symm a)) = of (e (e.symm a)) from liftRingHom_apply_of _ _, e.apply_symm_apply]
  exact RingEquiv.ofRingHom F B hFB hBF

@[simp] theorem ringCompletionCongr_of (e : R ≃+* T) (a : R) :
    ringCompletionCongr e (of a) = of (e a) := by
  change liftRingHom (ofRingHom.comp e.toRingHom) (of a) = of (e a)
  exact liftRingHom_apply_of _ _

def semiringIntegralFromKernel (L : R →+* T) (hsurj : Function.Surjective L)
    (c : RingCon R) (hker : c = RingCon.ker L) : T ≃+* c.Quotient := by
  subst c
  exact (RingCon.quotientKerEquivOfSurjective L hsurj).symm

theorem semiringIntegralFromKernel_characterization (L : R →+* T) (hsurj : Function.Surjective L)
    (c : RingCon R) (hker : c = RingCon.ker L) (a : T) (u : R) :
    semiringIntegralFromKernel L hsurj c hker a = c.mk' u ↔ a = L u := by
  subst c
  exact (RingCon.quotientKerEquivOfSurjective L hsurj).symm_apply_eq

end DiamondIntegral.Section3
