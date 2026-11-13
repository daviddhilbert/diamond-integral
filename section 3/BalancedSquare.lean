import «section 3».BalancedTensor

/-! A commuting square of coefficient-preserving semiring maps determines
the balanced tensor map without choosing a coefficient structure on its
target in advance. -/

noncomputable section
namespace DiamondIntegral.Section3
universe u v w x
variable {R : Type u} {A : Type v} {B : Type w} {V : Type x}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [CommSemiring V]
variable [Algebra R A] [Algebra R B]
open scoped TensorProduct

def balancedSquareMap (f : A →+* V) (g : B →+* V)
    (hcomm : f.comp (algebraMap R A) = g.comp (algebraMap R B)) : A ⊗[R] B →+* V := by
  letI : Algebra R V := (f.comp (algebraMap R A)).toAlgebra
  let F : A →ₐ[R] V := { f with commutes' := fun _ => rfl }
  let G : B →ₐ[R] V := {
    g with
    commutes' := by
      intro r
      exact congrArg (fun h : R →+* V => h r) hcomm.symm }
  exact (balancedTensorMap F G).toRingHom

@[simp] theorem balancedSquareMap_tmul (f : A →+* V) (g : B →+* V)
    (hcomm : f.comp (algebraMap R A) = g.comp (algebraMap R B)) (a : A) (b : B) :
    balancedSquareMap f g hcomm (a ⊗ₜ[R] b) = f a * g b := rfl

theorem balancedSquareMap_unique (f : A →+* V) (g : B →+* V)
    (hcomm : f.comp (algebraMap R A) = g.comp (algebraMap R B)) (F : A ⊗[R] B →+* V)
    (hF : ∀ a b, F (a ⊗ₜ[R] b) = f a * g b) : F = balancedSquareMap f g hcomm := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => exact hF a b
  | add z w hz hw => simp only [map_add, hz, hw]

end DiamondIntegral.Section3
