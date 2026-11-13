import Mathlib.RingTheory.TensorProduct.Maps

/-! The standard balanced tensor of commutative semirings and its
natural map for a commuting coefficient diagram. Pure tensors map to
products, and that formula uniquely determines the map. -/

noncomputable section
namespace DiamondIntegral.Section3
universe u v w x
variable {R : Type u} {A : Type v} {B : Type w} {V : Type x}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [CommSemiring V]
variable [Algebra R A] [Algebra R B] [Algebra R V]
open scoped TensorProduct

def balancedTensorMap (f : A →ₐ[R] V) (g : B →ₐ[R] V) : A ⊗[R] B →ₐ[R] V :=
  Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)

@[simp] theorem balancedTensorMap_tmul (f : A →ₐ[R] V) (g : B →ₐ[R] V) (a : A) (b : B) :
    balancedTensorMap f g (a ⊗ₜ[R] b) = f a * g b := rfl

theorem balancedTensorMap_unique (f : A →ₐ[R] V) (g : B →ₐ[R] V) (F : A ⊗[R] B →ₐ[R] V)
    (hF : ∀ a b, F (a ⊗ₜ[R] b) = f a * g b) : F = balancedTensorMap f g := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => exact hF a b
  | add z w hz hw => simp only [map_add, hz, hw]

end DiamondIntegral.Section3
