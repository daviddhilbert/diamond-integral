import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Group.TypeTags.Hom
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type*} [Field K] [IsAlgClosed K]

@[instance_reducible] def algebraicallyClosedUnitsDivisibleNat : DivisibleBy (Additive Kˣ) ℕ :=
  divisibleByOfSMulRightSurj _ _ (by
    intro n hn y
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (y.toMul : K) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      intro he
      rw [he,zero_pow hn] at hz
      exact Units.ne_zero y.toMul hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0),?_⟩
    change (Units.mk0 z hz0)^n = y.toMul
    exact Units.ext hz)

@[instance_reducible] def algebraicallyClosedUnitsDivisibleInt : DivisibleBy (Additive Kˣ) ℤ := by
  letI : DivisibleBy (Additive Kˣ) ℕ := algebraicallyClosedUnitsDivisibleNat
  exact AddGroup.divisibleByIntOfDivisibleByNat (Additive Kˣ)

/-- Divisibility extends a multiplicative character along any injective
group map; the extension equation retains every original character value. -/
theorem character_extends_of_divisible {A B C : Type*}
    [CommGroup A] [CommGroup B] [CommGroup C] [DivisibleBy (Additive C) ℤ]
    (i : A →* B) (hi : Function.Injective i) (χ : A →* C) :
    ∃ ψ : B →* C, ψ.comp i = χ := by
  obtain ⟨ψ,hψ⟩ := (Module.Baer.of_divisible (Additive C)).extension_property_addMonoidHom
    i.toAdditive hi χ.toAdditive
  refine ⟨MonoidHom.toAdditive.symm ψ,?_⟩
  apply MonoidHom.toAdditive.injective
  exact hψ

theorem algebraicallyClosed_character_extends {A B : Type*}
    [CommGroup A] [CommGroup B] (i : A →* B) (hi : Function.Injective i)
    (χ : A →* Kˣ) : ∃ ψ : B →* Kˣ, ψ.comp i = χ := by
  letI : DivisibleBy (Additive Kˣ) ℤ := algebraicallyClosedUnitsDivisibleInt
  exact character_extends_of_divisible i hi χ

end DiamondIntegral.Section3
