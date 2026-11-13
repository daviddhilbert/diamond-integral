module

public import «section 4».StepFunctions
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-! The two Euler generator algebras, with a proved additive identification
with actual finite-jump functions. The integral-convolution identification
and the first-order definability bridge are separate obligations. -/

@[expose] public noncomputable section
open Classical

namespace DiamondIntegral.Section4

inductive EulerKind where
  | geometric
  | bounded
  deriving DecidableEq

def EulerKind.lineValue : EulerKind → ℤ
  | .geometric => -1
  | .bounded => 1

def EulerKind.rayValue : EulerKind → ℤ
  | .geometric => -1
  | .bounded => 0

theorem EulerKind.lineValue_sq (k : EulerKind) : k.lineValue * k.lineValue = 1 := by
  cases k <;> decide

theorem EulerKind.rayValue_sq (k : EulerKind) : k.rayValue * k.rayValue = -k.rayValue := by
  cases k <;> decide

def coefficientSum {Γ : Type*} : (Γ →₀ ℤ) →+ ℤ where
  toFun p := p.sum fun _ n => n
  map_zero' := by simp
  map_add' p q := Finsupp.sum_add_index (by intros; rfl) (by intros; rfl)

theorem coefficientSum_single {Γ : Type*} (a : Γ) (n : ℤ) :
    coefficientSum (Finsupp.single a n) = n := by
  change (Finsupp.single a n).sum (fun _ m => m) = n
  exact Finsupp.sum_single_index rfl

variable {Γ : Type*}

abbrev GammaGroupRing (Γ : Type*) := AddMonoidAlgebra ℤ Γ
abbrev EulerModel (Γ : Type*) := ℤ × GammaGroupRing Γ × GammaGroupRing Γ

def groupCoefficientSum : GammaGroupRing Γ →+ ℤ :=
  coefficientSum.comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem groupCoefficientSum_eq (p : GammaGroupRing Γ) :
    groupCoefficientSum p = coefficientSum p.coeff := rfl

theorem groupCoefficientSum_ofCoeff (p : Γ →₀ ℤ) :
    groupCoefficientSum (AddMonoidAlgebra.ofCoeff p) = coefficientSum p := rfl

def normalCoordinates (k : EulerKind) : StepCoefficients Γ ≃+ EulerModel Γ where
  toFun v := (k.lineValue * v.1 + coefficientSum v.2.1 +
    k.rayValue * coefficientSum v.2.2,
    AddMonoidAlgebra.ofCoeff v.2.1, AddMonoidAlgebra.ofCoeff (v.2.1 - v.2.2))
  invFun z := (k.lineValue * (z.1 - groupCoefficientSum z.2.1 -
    k.rayValue * (groupCoefficientSum z.2.1 - groupCoefficientSum z.2.2)),
    z.2.1.coeff, z.2.1.coeff - z.2.2.coeff)
  left_inv v := by
    apply Prod.ext
    · dsimp
      simp only [groupCoefficientSum_ofCoeff, map_sub]
      cases k <;> simp only [EulerKind.lineValue, EulerKind.rayValue] <;> ring
    · apply Prod.ext
      · rfl
      · dsimp; exact sub_sub_cancel _ _
  right_inv z := by
    apply Prod.ext
    · dsimp only
      simp only [groupCoefficientSum_eq, map_sub]
      cases k <;> simp only [EulerKind.lineValue, EulerKind.rayValue] <;> ring
    · apply Prod.ext
      · exact AddMonoidAlgebra.ofCoeff_coeff _
      · dsimp
        rw [sub_sub_cancel]
  map_add' u v := by
    apply Prod.ext
    · dsimp; simp only [map_add]; ring
    · apply Prod.ext
      · exact AddMonoidAlgebra.ofCoeff_add _ _
      · dsimp
        abel

theorem groupCoefficientSum_single (a : Γ) (n : ℤ) :
    groupCoefficientSum (AddMonoidAlgebra.single a n) = n := by
  change coefficientSum (Finsupp.single a n) = n
  exact coefficientSum_single a n

section Generators
variable [AddCommGroup Γ]

def modelPoint (a : Γ) : EulerModel Γ :=
  (1, AddMonoidAlgebra.single a 1, AddMonoidAlgebra.single a 1)

def modelRay (k : EulerKind) (a : Γ) : EulerModel Γ :=
  (k.rayValue, 0, -AddMonoidAlgebra.single a 1)

def modelLine (k : EulerKind) : EulerModel Γ := (k.lineValue, 0, 0)

theorem modelPoint_zero : modelPoint (0 : Γ) = 1 := by
  simp [modelPoint, AddMonoidAlgebra.one_def]

theorem modelPoint_mul (a b : Γ) : modelPoint a * modelPoint b = modelPoint (a + b) := by
  simp [modelPoint, AddMonoidAlgebra.single_mul_single]

theorem modelPoint_ray (k : EulerKind) (a b : Γ) :
    modelPoint a * modelRay k b = modelRay k (a + b) := by
  simp [modelPoint, modelRay, AddMonoidAlgebra.single_mul_single]

theorem modelRay_mul (k : EulerKind) (a b : Γ) :
    modelRay k a * modelRay k b = -modelRay k (a + b) := by
  apply Prod.ext
  · exact k.rayValue_sq
  · simp [modelRay, AddMonoidAlgebra.single_mul_single]

theorem modelLine_point (k : EulerKind) (a : Γ) :
    modelLine k * modelPoint a = modelLine k := by
  simp [modelLine, modelPoint]

theorem modelLine_ray (k : EulerKind) (a : Γ) :
    modelLine k * modelRay k a = k.rayValue • modelLine k := by
  simp [modelLine, modelRay, mul_comm]

theorem modelLine_mul (k : EulerKind) :
    modelLine (Γ := Γ) k * modelLine k = k.lineValue • modelLine k := by
  simp [modelLine]

end Generators

section ActualFunctions
variable [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [Nonempty Γ]

def modelFunctionEquiv (k : EulerKind) : EulerModel Γ ≃+ StepFunction Γ :=
  (normalCoordinates k).symm.trans stepCoefficientsEquiv

theorem modelFunctionEquiv_eval (k : EulerKind) (z : EulerModel Γ) (x : Γ) :
    (modelFunctionEquiv k z).val x = stepEval ((normalCoordinates k).symm z) x := rfl

variable [AddCommGroup Γ]

omit [AddCommGroup Γ] in
theorem modelPoint_function (k : EulerKind) (a x : Γ) :
    (modelFunctionEquiv k (modelPoint a)).val x = if x = a then 1 else 0 := by
  rw [modelFunctionEquiv_eval]
  simp [normalCoordinates, modelPoint, stepEval, groupCoefficientSum_single,
    AddMonoidAlgebra.coeff_single, jumpPrefix_zero, Finsupp.single_apply, eq_comm]

theorem modelRay_function (k : EulerKind) (a x : Γ) :
    (modelFunctionEquiv k (modelRay k a)).val x = if a < x then 1 else 0 := by
  rw [modelFunctionEquiv_eval]
  simp [normalCoordinates, modelRay, stepEval, groupCoefficientSum_single,
    AddMonoidAlgebra.coeff_single, jumpPrefix_single]

theorem modelLine_function (k : EulerKind) (x : Γ) :
    (modelFunctionEquiv k (modelLine k)).val x = 1 := by
  rw [modelFunctionEquiv_eval]
  simp [normalCoordinates, modelLine, stepEval, jumpPrefix_zero, k.lineValue_sq]

end ActualFunctions
end DiamondIntegral.Section4
