import «section 3».CompletionTensor
import «section 3».CompletionDirectSum
import «section 4».RingTensorCongruence

/-! Completing a balanced product comparison retains its pure-tensor
formula on arbitrary differences of positive classes. -/

set_option autoImplicit false
noncomputable section
open Algebra.GrothendieckAddGroup
open DiamondIntegral.Section3
open scoped TensorProduct

namespace DiamondIntegral.Section4.CompletionTensorMapFormula
variable {R A B V : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B] [CommSemiring V]
  [Algebra R A] [Algebra R B]

theorem hom_ext {T : Type*} [CommRing T]
    (f g : CompletionTensor (R := R) (A := A) (B := B) →+* T)
    (h : ∀ a b, f (of a ⊗ₜ[RingCompletion R] of b) = g (of a ⊗ₜ[RingCompletion R] of b)) : f = g := by
  apply RingTensorCongruence.hom_ext
  intro x y
  let K := TensorProduct.mk (RingCompletion R) (RingCompletion A) (RingCompletion B)
  have hx : f.toAddMonoidHom.comp (K.flip y).toAddMonoidHom = g.toAddMonoidHom.comp (K.flip y).toAddMonoidHom := by
    apply completionAddHom_ext
    intro a
    have hy : f.toAddMonoidHom.comp (K (of a)).toAddMonoidHom = g.toAddMonoidHom.comp (K (of a)).toAddMonoidHom := by
      apply completionAddHom_ext
      intro b
      exact h a b
    exact DFunLike.congr_fun hy y
  exact DFunLike.congr_fun hx x

def completed (f : A →+* V) (g : B →+* V)
    (h : f.comp (algebraMap R A) = g.comp (algebraMap R B)) :
    CompletionTensor (R := R) (A := A) (B := B) →+* RingCompletion V :=
  (ringCompletionMap (balancedSquareMap f g h)).comp
    (ringCompletionTensorEquiv (R := R) (A := A) (B := B)).symm.toRingHom

theorem completed_of_tmul (f : A →+* V) (g : B →+* V) (h) (a : A) (b : B) :
    completed f g h (of a ⊗ₜ[RingCompletion R] of b) = of (f a) * of (g b) := by
  have he : (ringCompletionTensorEquiv (R := R) (A := A) (B := B)).symm
      (of a ⊗ₜ[RingCompletion R] of b) = of (a ⊗ₜ[R] b) :=
    (ringCompletionTensorEquiv (R := R) (A := A) (B := B)).symm_apply_eq.mpr (ringCompletionTensorEquiv_tmul a b).symm
  change ringCompletionMap (balancedSquareMap f g h) ((ringCompletionTensorEquiv (R := R) (A := A) (B := B)).symm _) = _
  rw [he, ringCompletionMap_of, balancedSquareMap_tmul]
  exact (ofRingHom : V →+* RingCompletion V).map_mul _ _

theorem completed_tmul (f : A →+* V) (g : B →+* V) (h) (x : RingCompletion A) (y : RingCompletion B) :
    completed f g h (x ⊗ₜ[RingCompletion R] y) = ringCompletionMap f x * ringCompletionMap g y := by
  have hs : (ringCompletionMap f).comp (algebraMap (RingCompletion R) (RingCompletion A)) =
      (ringCompletionMap g).comp (algebraMap (RingCompletion R) (RingCompletion B)) := by
    apply ringHom_ext
    intro r
    change ringCompletionMap f (algebraMap _ _ (of r)) = ringCompletionMap g (algebraMap _ _ (of r))
    rw [ringCompletionScalar_of, ringCompletionScalar_of, ringCompletionMap_of, ringCompletionMap_of]
    exact congrArg of (RingHom.congr_fun h r)
  have he : completed f g h = balancedSquareMap (ringCompletionMap f) (ringCompletionMap g) hs := by
    apply hom_ext
    intro a b
    rw [completed_of_tmul, balancedSquareMap_tmul, ringCompletionMap_of, ringCompletionMap_of]
  rw [he, balancedSquareMap_tmul]

end DiamondIntegral.Section4.CompletionTensorMapFormula
