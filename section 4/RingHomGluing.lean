import Mathlib.Tactic.Ring

/-! Two ring homomorphisms can be glued along a common reference map
when their respective differences annihilate one another. -/

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section4.RingHomGluing
variable {A R : Type*} [CommRing A] [CommRing R]

def glue (h g z : A →+* R)
    (cross : ∀ p q, (h p - z p) * (g q - z q) = 0) : A →+* R where
  toFun p := h p + g p - z p
  map_zero' := by simp
  map_one' := by simp
  map_add' p q := by simp only [map_add]; ring
  map_mul' p q := by
    simp only [map_mul]
    calc
      h p * h q + g p * g q - z p * z q =
          (h p + g p - z p) * (h q + g q - z q) -
            (h p - z p) * (g q - z q) - (h q - z q) * (g p - z p) := by ring
      _ = (h p + g p - z p) * (h q + g q - z q) := by rw [cross, cross]; ring

theorem glue_apply (h g z : A →+* R)
    (cross : ∀ p q, (h p - z p) * (g q - z q) = 0) (p : A) :
    glue h g z cross p = h p + g p - z p := rfl

end DiamondIntegral.Section4.RingHomGluing
