import Section4.PositivePresentation
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
universe u v
variable {Obj : Type u} {A : Type v} [CommSemiring A]

/-- A homomorphism into the universal positive semiring is surjective
once every actual object generator has a preimage. -/
theorem positivePresentation_surjective_of_generators (P : PositiveGrothendieck.Presentation Obj)
    (F : A →+* PositiveGrothendieck.KPlus P)
    (h : ∀ o, ∃ a, F a = PositiveGrothendieck.of P o) : Function.Surjective F := by
  have hpoly : ∀ p : MvPolynomial Obj ℕ, ∃ a, F a = PositiveGrothendieck.quotientHom P p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C n =>
      refine ⟨n,?_⟩
      have hn : MvPolynomial.C n = (n : MvPolynomial Obj ℕ) := map_natCast MvPolynomial.C n
      rw [hn,map_natCast,map_natCast]
    | add p q hp hq =>
      obtain ⟨a,ha⟩ := hp
      obtain ⟨b,hb⟩ := hq
      exact ⟨a+b,by rw [map_add,ha,hb,map_add]⟩
    | mul_X p o hp =>
      obtain ⟨a,ha⟩ := hp
      obtain ⟨b,hb⟩ := h o
      exact ⟨a*b,by rw [map_mul,ha,hb]; exact (map_mul (PositiveGrothendieck.quotientHom P) p (MvPolynomial.X o)).symm⟩
  intro z
  obtain ⟨p,hp⟩ := (PositiveGrothendieck.congruence P).mk'_surjective z
  obtain ⟨a,ha⟩ := hpoly p
  exact ⟨a,ha.trans hp⟩
end DiamondIntegral.Section3
