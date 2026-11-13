import Mathlib.Algebra.Ring.Equiv

/-! Transport multiplication across an additive equivalence while
retaining the original addition, zero and natural scalar multiplication. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
universe u v
variable {A : Type u} [AddCommMonoid A] {R : Type v} [CommSemiring R]

@[instance_reducible]
def additiveTransportCommMonoid (e : A ≃+ R) : CommMonoid A where
  mul a b := e.symm (e a * e b)
  one := e.symm 1
  mul_assoc a b c := by
    change e.symm (e (e.symm (e a * e b)) * e c) = e.symm (e a * e (e.symm (e b * e c)))
    rw [e.apply_symm_apply, e.apply_symm_apply, mul_assoc]
  one_mul a := by
    change e.symm (e (e.symm 1) * e a) = a
    rw [e.apply_symm_apply, one_mul, e.symm_apply_apply]
  mul_one a := by
    change e.symm (e a * e (e.symm 1)) = a
    rw [e.apply_symm_apply, mul_one, e.symm_apply_apply]
  mul_comm a b := by
    change e.symm (e a * e b) = e.symm (e b * e a)
    rw [mul_comm]

@[instance_reducible]
def additiveTransportCommSemiring (e : A ≃+ R) : CommSemiring A := by
  letI := additiveTransportCommMonoid e
  exact {
    toAddCommMonoid := inferInstance
    toCommMonoid := inferInstance
    zero_mul := fun a => by
      change e.symm (e 0 * e a) = 0
      rw [map_zero, zero_mul, map_zero]
    mul_zero := fun a => by
      change e.symm (e a * e 0) = 0
      rw [map_zero, mul_zero, map_zero]
    left_distrib := fun a b c => by
      change e.symm (e a * e (b + c)) = e.symm (e a * e b) + e.symm (e a * e c)
      rw [map_add, mul_add, map_add]
    right_distrib := fun a b c => by
      change e.symm (e (a + b) * e c) = e.symm (e a * e c) + e.symm (e b * e c)
      rw [map_add, add_mul, map_add]
    natCast := fun n => n • (1 : A)
    natCast_zero := zero_nsmul _
    natCast_succ := fun n => by rw [succ_nsmul] }

def additiveTransportRingEquiv (e : A ≃+ R) :
    letI := additiveTransportCommSemiring e
    A ≃+* R := by
  letI := additiveTransportCommSemiring e
  exact { e with map_mul' := fun a b => e.apply_symm_apply (e a * e b) }

end DiamondIntegral.Section3
