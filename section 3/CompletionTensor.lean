import «section 3».BalancedSquare
import «section 3».CompletionEquivalences

/-! Ring completion commutes with the balanced tensor of commutative
semirings. Both directions are the canonical maps on actual generators. -/

noncomputable section
namespace DiamondIntegral.Section3
open Algebra.GrothendieckAddGroup
open scoped TensorProduct
universe u v w
variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B]

def ringCompletionMap {T : Type*} [CommSemiring T] (f : R →+* T) : RingCompletion R →+* RingCompletion T :=
  liftRingHom (ofRingHom.comp f)

@[simp] theorem ringCompletionMap_of {T : Type*} [CommSemiring T] (f : R →+* T) (r : R) :
    ringCompletionMap f (of r) = of (f r) := liftRingHom_apply_of _ _

instance ringCompletionAlgebra [Algebra R A] : Algebra (RingCompletion R) (RingCompletion A) :=
  (ringCompletionMap (algebraMap R A)).toAlgebra

@[simp] theorem ringCompletionScalar_of [Algebra R A] (r : R) :
    algebraMap (RingCompletion R) (RingCompletion A) (of r) = of (algebraMap R A r) :=
  ringCompletionMap_of _ _

variable [Algebra R A] [Algebra R B]
abbrev CompletionTensor := RingCompletion A ⊗[RingCompletion R] RingCompletion B

def completionTensorLeft : A →+* CompletionTensor (R := R) (A := A) (B := B) :=
  (Algebra.TensorProduct.includeLeftRingHom (R := RingCompletion R)
    (A := RingCompletion A) (B := RingCompletion B)).comp ofRingHom

def completionTensorRight : B →+* CompletionTensor (R := R) (A := A) (B := B) :=
  (Algebra.TensorProduct.includeRight (R := RingCompletion R)
    (A := RingCompletion A) (B := RingCompletion B)).toRingHom.comp ofRingHom

theorem completionTensor_square :
    (completionTensorLeft (R := R) (A := A) (B := B)).comp (algebraMap R A) =
      completionTensorRight.comp (algebraMap R B) := by
  apply RingHom.ext
  intro r
  have h := congrArg (fun f : RingCompletion R →+* CompletionTensor (R := R) (A := A) (B := B) => f (of r))
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := RingCompletion R) (A := RingCompletion A) (B := RingCompletion B))
  simpa only [RingHom.comp_apply, ringCompletionScalar_of, completionTensorLeft, completionTensorRight, ofRingHom_apply] using h

def toCompletionTensor : RingCompletion (A ⊗[R] B) →+* CompletionTensor (R := R) (A := A) (B := B) :=
  liftRingHom (balancedSquareMap completionTensorLeft completionTensorRight completionTensor_square)

theorem toCompletionTensor_tmul (a : A) (b : B) :
    toCompletionTensor (of (a ⊗ₜ[R] b)) = (of a) ⊗ₜ[RingCompletion R] (of b) := by
  change liftRingHom _ (of (a ⊗ₜ[R] b)) = _
  rw [liftRingHom_apply_of, balancedSquareMap_tmul]
  change ((of a) ⊗ₜ[RingCompletion R] (1 : RingCompletion B)) *
    ((1 : RingCompletion A) ⊗ₜ[RingCompletion R] (of b)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def fromCompletionTensorLeft : RingCompletion A →+* RingCompletion (A ⊗[R] B) :=
  ringCompletionMap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))

def fromCompletionTensorRight : RingCompletion B →+* RingCompletion (A ⊗[R] B) :=
  ringCompletionMap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom

theorem fromCompletionTensor_square :
    (fromCompletionTensorLeft (R := R) (A := A) (B := B)).comp
        (algebraMap (RingCompletion R) (RingCompletion A)) =
      fromCompletionTensorRight.comp (algebraMap (RingCompletion R) (RingCompletion B)) := by
  apply ringHom_ext
  intro r
  change fromCompletionTensorLeft (algebraMap (RingCompletion R) (RingCompletion A) (of r)) =
    fromCompletionTensorRight (algebraMap (RingCompletion R) (RingCompletion B) (of r))
  rw [ringCompletionScalar_of, ringCompletionScalar_of]
  change ringCompletionMap _ (of (algebraMap R A r)) = ringCompletionMap _ (of (algebraMap R B r))
  rw [ringCompletionMap_of, ringCompletionMap_of]
  exact congrArg of (congrArg (fun f : R →+* A ⊗[R] B => f r)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R) (A := A) (B := B)))

def fromCompletionTensor : CompletionTensor (R := R) (A := A) (B := B) →+* RingCompletion (A ⊗[R] B) :=
  balancedSquareMap (R := RingCompletion R) fromCompletionTensorLeft fromCompletionTensorRight
    fromCompletionTensor_square

theorem fromCompletionTensor_tmul (a : A) (b : B) :
    fromCompletionTensor ((of a) ⊗ₜ[RingCompletion R] (of b)) = of (a ⊗ₜ[R] b) := by
  rw [fromCompletionTensor, balancedSquareMap_tmul]
  change ringCompletionMap _ (of a) * ringCompletionMap _ (of b) = _
  rw [ringCompletionMap_of, ringCompletionMap_of]
  change (ofRingHom : (A ⊗[R] B) →+* RingCompletion (A ⊗[R] B)) (a ⊗ₜ[R] 1) *
    ofRingHom (1 ⊗ₜ[R] b) = ofRingHom (a ⊗ₜ[R] b)
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def ringCompletionTensorEquiv : RingCompletion (A ⊗[R] B) ≃+* CompletionTensor (R := R) (A := A) (B := B) := by
  let F := toCompletionTensor (R := R) (A := A) (B := B)
  let G := fromCompletionTensor (R := R) (A := A) (B := B)
  have hGF : G.comp F = RingHom.id _ := by
    apply ringHom_ext
    intro z
    change G (F (of z)) = of z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rw [toCompletionTensor_tmul, fromCompletionTensor_tmul]
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  have hFG : F.comp G = RingHom.id _ := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply ringHom_ext
      intro a
      change F (G ((of a) ⊗ₜ[RingCompletion R] (1 : RingCompletion B))) = _
      rw [show (1 : RingCompletion B) = of (1 : B) from rfl,
        fromCompletionTensor_tmul, toCompletionTensor_tmul]
      rfl
    · apply ringHom_ext
      intro b
      change F (G ((1 : RingCompletion A) ⊗ₜ[RingCompletion R] (of b))) = _
      rw [show (1 : RingCompletion A) = of (1 : A) from rfl,
        fromCompletionTensor_tmul, toCompletionTensor_tmul]
      rfl
  exact RingEquiv.ofRingHom F G hFG hGF

@[simp] theorem ringCompletionTensorEquiv_tmul (a : A) (b : B) :
    ringCompletionTensorEquiv (of (a ⊗ₜ[R] b)) = (of a) ⊗ₜ[RingCompletion R] (of b) := by
  change toCompletionTensor (of (a ⊗ₜ[R] b)) = _
  exact toCompletionTensor_tmul a b

def groupifiedTensorIso {V : Type*} [CommSemiring V] (e : A ⊗[R] B ≃+* V) :
    CompletionTensor (R := R) (A := A) (B := B) ≃+* RingCompletion V :=
  ringCompletionTensorEquiv.symm.trans (ringCompletionCongr e)

@[simp] theorem groupifiedTensorIso_tmul {V : Type*} [CommSemiring V] (e : A ⊗[R] B ≃+* V)
    (a : A) (b : B) : groupifiedTensorIso e ((of a) ⊗ₜ[RingCompletion R] (of b)) =
      of (e (a ⊗ₜ[R] b)) := by
  have h : (ringCompletionTensorEquiv (R := R) (A := A) (B := B)).symm
      ((of a) ⊗ₜ[RingCompletion R] (of b)) = of (a ⊗ₜ[R] b) :=
    (ringCompletionTensorEquiv (R := R) (A := A) (B := B)).symm_apply_eq.mpr
      (ringCompletionTensorEquiv_tmul a b).symm
  change ringCompletionCongr e (ringCompletionTensorEquiv.symm _) = _
  rw [h, ringCompletionCongr_of]

end DiamondIntegral.Section3
