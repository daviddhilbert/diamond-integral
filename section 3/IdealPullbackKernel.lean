import Mathlib.RingTheory.Ideal.Maps
set_option autoImplicit false
namespace DiamondIntegral.Section3
variable {T B A R : Type*} [CommRing T] [CommRing B] [CommRing A] [CommRing R]

/-- A commuting presentation square sends the full pullback of an
annihilated ideal into the actual kernel, including presentation ambiguity. -/
theorem ideal_pullback_le_kernel (q : T →+* B) (f : T →+* A) (u : B →+* A)
    (hcomm : f = u.comp q) (J : Ideal B) (hJ : J ≤ RingHom.ker u) :
    Ideal.comap q J ≤ RingHom.ker f := by
  intro x hx
  change f x = 0
  rw [hcomm,RingHom.comp_apply]
  exact hJ hx

/-- Killing specified generators kills their whole ideal, before any
choice of representatives in a surjective tensor presentation. -/
theorem ideal_span_pullback_le_kernel {ι : Type*} (p : ι → B)
    (q : T →+* B) (f : T →+* A) (u : B →+* A)
    (hcomm : f = u.comp q) (hp : ∀ i, u (p i) = 0) :
    Ideal.comap q (Ideal.span (Set.range p)) ≤ RingHom.ker f := by
  apply ideal_pullback_le_kernel q f u hcomm
  apply Ideal.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact hp i
end DiamondIntegral.Section3
