import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Hom.Defs
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {A C : Type*} [AddCommGroup A] [CommGroup C] {n : ℕ}

def DiagonalWeightsFaithful (C : Type*) [CommGroup C]
    {A : Type*} [AddCommGroup A] {n : ℕ} (w : Fin n → A) : Prop :=
  ∀ χ : Multiplicative A →* C, (∀ i, χ (Multiplicative.ofAdd (w i)) = 1) → χ = 1

theorem character_eq_one_of_joint_generators (a b : Fin n → A)
    (hgen : AddSubgroup.closure (Set.range a ∪ Set.range b) = ⊤)
    (χ : Multiplicative A →* C)
    (ha : ∀ i, χ (Multiplicative.ofAdd (a i)) = 1)
    (hb : ∀ i, χ (Multiplicative.ofAdd (b i)) = 1) : χ = 1 := by
  have hχ : ∀ y ∈ AddSubgroup.closure (Set.range a ∪ Set.range b),
      χ (Multiplicative.ofAdd y) = 1 := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · exact ha i
      · exact hb i
    | zero => exact χ.map_one
    | add y z _ _ hy hz =>
      change χ (Multiplicative.ofAdd y * Multiplicative.ofAdd z) = 1
      rw [map_mul,hy,hz,mul_one]
    | neg y _ hy =>
      change χ (Multiplicative.ofAdd y)⁻¹ = 1
      rw [map_inv,hy,inv_one]
  ext x
  exact hχ x.toAdd (by rw [hgen]; trivial)

theorem diagonalWeightsFaithful_of_generators (a : Fin n → A)
    (ha : AddSubgroup.closure (Set.range a) = ⊤) : DiagonalWeightsFaithful C a := by
  intro χ hχ
  apply character_eq_one_of_joint_generators a a
  · simpa using ha
  · exact hχ
  · exact hχ

end DiamondIntegral.Section3
