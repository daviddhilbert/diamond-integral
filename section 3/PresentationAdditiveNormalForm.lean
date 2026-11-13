import «section 3».PresentationHomExt
import Mathlib.Algebra.BigOperators.Ring.List

/-! Product relations reduce every polynomial class to a finite sum
of actual object generators. No cancellation or uniqueness is assumed. -/
noncomputable section
namespace DiamondIntegral.Section3
open SpecialTransformations.Section4

theorem positivePresentation_additive_normal_form {Obj : Type*} (P : PositiveGrothendieck.Presentation Obj)
    (x : PositiveGrothendieck.KPlus P) :
    ∃ l : List Obj, x = (l.map (PositiveGrothendieck.of P)).sum := by
  obtain ⟨p, rfl⟩ := (PositiveGrothendieck.congruence P).mk'_surjective x
  change ∃ l : List Obj, PositiveGrothendieck.quotientHom P p = (l.map (PositiveGrothendieck.of P)).sum
  induction p using MvPolynomial.induction_on with
  | C n =>
    refine ⟨List.replicate n P.unit, ?_⟩
    have hC : (MvPolynomial.C n : MvPolynomial Obj ℕ) = n := map_natCast MvPolynomial.C n
    rw [hC, map_natCast]
    simp only [List.map_replicate, List.sum_replicate, PositiveGrothendieck.of_unit, nsmul_eq_mul, mul_one]
  | add p q hp hq =>
    obtain ⟨l, hl⟩ := hp
    obtain ⟨r, hr⟩ := hq
    exact ⟨l ++ r, by rw [map_add, hl, hr, List.map_append, List.sum_append]⟩
  | mul_X p a hp =>
    obtain ⟨l, hl⟩ := hp
    refine ⟨l.map (fun b => P.product b a), ?_⟩
    rw [map_mul, hl]
    change (l.map (PositiveGrothendieck.of P)).sum * PositiveGrothendieck.of P a = _
    simp only [List.map_map, Function.comp_def, PositiveGrothendieck.of_product]
    exact (List.sum_map_mul_right l (PositiveGrothendieck.of P) (PositiveGrothendieck.of P a)).symm

theorem positivePresentation_additive_induction {Obj : Type*} (P : PositiveGrothendieck.Presentation Obj)
    {motive : PositiveGrothendieck.KPlus P → Prop} (hzero : motive 0)
    (hof : ∀ a, motive (PositiveGrothendieck.of P a))
    (hadd : ∀ a b, motive a → motive b → motive (a + b)) (x : PositiveGrothendieck.KPlus P) : motive x := by
  obtain ⟨l, rfl⟩ := positivePresentation_additive_normal_form P x
  induction l with
  | nil => exact hzero
  | cons a l ih => exact hadd _ _ (hof a) ih

theorem positivePresentation_additiveHom_ext {Obj R : Type*} (P : PositiveGrothendieck.Presentation Obj)
    [AddZeroClass R] {F G : PositiveGrothendieck.KPlus P →+ R}
    (h : ∀ a, F (PositiveGrothendieck.of P a) = G (PositiveGrothendieck.of P a)) : F = G := by
  apply AddMonoidHom.ext
  intro x
  apply positivePresentation_additive_induction P (motive := fun x => F x = G x) _ h _ x
  · simp only [map_zero]
  · intro a b ha hb
    simp only [map_add, ha, hb]

theorem positivePresentation_additive_surjective {Obj A : Type*} (P : PositiveGrothendieck.Presentation Obj)
    [AddZeroClass A] (f : A →+ PositiveGrothendieck.KPlus P)
    (hof : ∀ a, ∃ x, f x = PositiveGrothendieck.of P a) : Function.Surjective f := by
  intro x
  apply positivePresentation_additive_induction P (motive := fun x => ∃ a, f a = x) _ hof _ x
  · exact ⟨0, map_zero f⟩
  · rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, (map_add f x y).trans (congrArg₂ (· + ·) hx hy)⟩

end DiamondIntegral.Section3
