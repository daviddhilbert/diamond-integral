import Mathlib.RingTheory.Congruence.Basic

/-! An additive invariant descends through one semiring relation when
it respects that relation in every multiplicative context. This permits
homogeneous coefficient extraction without additive cancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace DiamondIntegral.Section3
variable {R W : Type*} [CommSemiring R] [AddCommMonoid W]

theorem principal_additive_context_descent
    (φ : R →+ W) (p q : R) (hpq : ∀ z, φ (z*p) = φ (z*q))
    {x y : R} (h : RingConGen.Rel (fun a b => a = p ∧ b = q) x y) :
    ∀ z, φ (z*x) = φ (z*y) := by
  induction h with
  | of x y h => rcases h with ⟨rfl,rfl⟩; exact hpq
  | refl x => intro z; rfl
  | symm h ih => intro z; exact (ih z).symm
  | trans h k ih ik => intro z; exact (ih z).trans (ik z)
  | add h k ih ik =>
    intro z
    rw [mul_add,mul_add,φ.map_add,φ.map_add,ih,ik]
  | @mul a b c d h k ih ik =>
    intro z
    calc
      φ (z*(a*c)) = φ ((z*c)*a) := congrArg φ (by ac_rfl)
      _ = φ ((z*c)*b) := ih (z*c)
      _ = φ ((z*b)*c) := congrArg φ (by ac_rfl)
      _ = φ ((z*b)*d) := ik (z*b)
      _ = φ (z*(b*d)) := congrArg φ (by ac_rfl)

theorem principal_additive_descent
    (φ : R →+ W) (p q : R) (hpq : ∀ z, φ (z*p) = φ (z*q))
    {x y : R} (h : ringConGen (fun a b => a = p ∧ b = q) x y) : φ x = φ y := by
  simpa only [one_mul] using principal_additive_context_descent φ p q hpq h 1

end DiamondIntegral.Section3
