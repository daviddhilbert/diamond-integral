import Section4.PositivePresentation
import Section4.PositiveAdditivePresentation

noncomputable section
namespace DiamondIntegral.Section3
open SpecialTransformations.Section4

/-- Generator extensionality also holds for a noncommutative target semiring. -/
theorem positivePresentationHom_ext {Obj R : Type*} (P : PositiveGrothendieck.Presentation Obj)
    [Semiring R] {F G : PositiveGrothendieck.KPlus P →+* R}
    (h : ∀ a, F (PositiveGrothendieck.of P a) = G (PositiveGrothendieck.of P a)) : F = G := by
  have hpoly : F.comp (PositiveGrothendieck.quotientHom P) =
      G.comp (PositiveGrothendieck.quotientHom P) := by
    apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · exact h
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := (PositiveGrothendieck.congruence P).mk'_surjective z
  exact DFunLike.congr_fun hpoly p

/-- Additive generator extensionality keeps the native target additive structure. -/
theorem positiveAdditivePresentationHom_ext {Obj R : Type*} (P : PositiveAdditiveGrothendieck.Presentation Obj)
    [AddZeroClass R] {F G : PositiveAdditiveGrothendieck.KPlus P →+ R}
    (h : ∀ a, F (PositiveAdditiveGrothendieck.of P a) = G (PositiveAdditiveGrothendieck.of P a)) : F = G := by
  have hfree : F.comp (PositiveAdditiveGrothendieck.quotientHom P) =
      G.comp (PositiveAdditiveGrothendieck.quotientHom P) := by
    apply Finsupp.addHom_ext'
    intro a
    apply AddMonoidHom.ext_nat
    exact h a
  apply AddMonoidHom.ext
  intro z
  obtain ⟨p, rfl⟩ := (PositiveAdditiveGrothendieck.congruence P).mk'_surjective z
  exact DFunLike.congr_fun hfree p

end DiamondIntegral.Section3
