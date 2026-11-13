module

public import «section 4».EulerGenerators

/-! Commutative generator-ring structures on actual finite-jump functions.
Multiplication is transported from the checked generator algebra. Equality
with Euler integration of convolution fibres remains a separate theorem;
this file does not assume that theorem, or any result of HK. -/

@[expose] public noncomputable section
namespace DiamondIntegral.Section4

structure EulerFunction (k : EulerKind) (Γ : Type*) [LinearOrder Γ] where
  toStep : StepFunction Γ

instance eulerFunctionCoeFun {Γ : Type*} [LinearOrder Γ] {k : EulerKind} :
    CoeFun (EulerFunction k Γ) (fun _ => Γ → ℤ) := ⟨fun f => f.toStep.val⟩

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

def eulerCoordinates (k : EulerKind) : EulerFunction k Γ ≃ EulerModel Γ where
  toFun f := (modelFunctionEquiv k).symm f.toStep
  invFun z := ⟨modelFunctionEquiv k z⟩
  left_inv f := by
    cases f with
    | mk f =>
      exact congrArg (fun g : StepFunction Γ => EulerFunction.mk (k := k) g)
        ((modelFunctionEquiv (Γ := Γ) k).apply_symm_apply f)
  right_inv z := (modelFunctionEquiv (Γ := Γ) k).symm_apply_apply z

instance eulerFunctionCommRing (k : EulerKind) : CommRing (EulerFunction k Γ) :=
  (eulerCoordinates k).commRing

def eulerCoordinatesRingEquiv (k : EulerKind) : EulerFunction k Γ ≃+* EulerModel Γ :=
  Equiv.ringEquiv (eulerCoordinates k)

namespace EulerFunction

variable (k : EulerKind)

def ofModel (z : EulerModel Γ) : EulerFunction k Γ :=
  (eulerCoordinatesRingEquiv k).symm z

theorem ofModel_eval (z : EulerModel Γ) (x : Γ) :
    ofModel k z x = (modelFunctionEquiv k z).val x := rfl

theorem ofModel_add (z w : EulerModel Γ) :
    ofModel k (z + w) = ofModel k z + ofModel k w :=
  (eulerCoordinatesRingEquiv k).symm.map_add z w

theorem ofModel_mul (z w : EulerModel Γ) :
    ofModel k (z * w) = ofModel k z * ofModel k w :=
  (eulerCoordinatesRingEquiv k).symm.map_mul z w

theorem ofModel_neg (z : EulerModel Γ) : ofModel k (-z) = -ofModel k z :=
  (eulerCoordinatesRingEquiv k).symm.map_neg z

theorem ofModel_zsmul (n : ℤ) (z : EulerModel Γ) :
    ofModel k (n • z) = n • ofModel k z :=
  map_zsmul (eulerCoordinatesRingEquiv k).symm n z

theorem eval_add (f g : EulerFunction k Γ) (x : Γ) : (f + g) x = f x + g x := by
  change (modelFunctionEquiv k
    ((modelFunctionEquiv k).symm f.toStep + (modelFunctionEquiv k).symm g.toStep)).val x = _
  rw [map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

theorem eval_zero (x : Γ) : (0 : EulerFunction k Γ) x = 0 := by
  change (modelFunctionEquiv k 0).val x = 0
  rw [map_zero]
  rfl

theorem eval_neg (f : EulerFunction k Γ) (x : Γ) : (-f) x = -f x := by
  change (modelFunctionEquiv k (-((modelFunctionEquiv k).symm f.toStep))).val x = _
  rw [map_neg, AddEquiv.apply_symm_apply]
  rfl

omit [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] in
theorem eval_injective : Function.Injective (fun f : EulerFunction k Γ => (f : Γ → ℤ)) := by
  intro f g h
  cases f with | mk f =>
    cases g with | mk g =>
      congr 1
      exact Subtype.ext h

omit [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] in
theorem finite_range (f : EulerFunction k Γ) : (Set.range (f : Γ → ℤ)).Finite :=
  stepFunction_finite_range f.toStep

def point (a : Γ) : EulerFunction k Γ := ofModel k (modelPoint a)
def ray (a : Γ) : EulerFunction k Γ := ofModel k (modelRay k a)
def line : EulerFunction k Γ := ofModel k (modelLine k)

theorem point_eval (a x : Γ) : point k a x = if x = a then 1 else 0 :=
  modelPoint_function k a x

theorem ray_eval (a x : Γ) : ray k a x = if a < x then 1 else 0 :=
  modelRay_function k a x

theorem line_eval (x : Γ) : line (Γ := Γ) k x = 1 := modelLine_function k x

theorem point_zero : point k (0 : Γ) = 1 := by
  change ofModel k (modelPoint 0) = 1
  rw [modelPoint_zero]
  exact (eulerCoordinatesRingEquiv (Γ := Γ) k).symm.map_one

theorem point_mul (a b : Γ) : point k a * point k b = point k (a + b) := by
  change ofModel k (modelPoint a) * ofModel k (modelPoint b) = _
  rw [← ofModel_mul, modelPoint_mul]
  rfl

theorem point_ray (a b : Γ) : point k a * ray k b = ray k (a + b) := by
  change ofModel k (modelPoint a) * ofModel k (modelRay k b) = _
  rw [← ofModel_mul, modelPoint_ray]
  rfl

theorem ray_mul (a b : Γ) : ray k a * ray k b = -ray k (a + b) := by
  change ofModel k (modelRay k a) * ofModel k (modelRay k b) = _
  rw [← ofModel_mul, modelRay_mul, ofModel_neg]
  rfl

theorem line_point (a : Γ) : line k * point k a = line k := by
  change ofModel k (modelLine k) * ofModel k (modelPoint a) = _
  rw [← ofModel_mul, modelLine_point]
  rfl

theorem line_ray (a : Γ) : line k * ray k a = k.rayValue • line k := by
  change ofModel k (modelLine k) * ofModel k (modelRay k a) = _
  rw [← ofModel_mul, modelLine_ray, ofModel_zsmul]
  rfl

theorem line_mul : line (Γ := Γ) k * line k = k.lineValue • line k := by
  change ofModel k (modelLine k) * ofModel k (modelLine k) = _
  rw [← ofModel_mul, modelLine_mul, ofModel_zsmul]
  rfl

def totalEuler : EulerFunction k Γ →+* ℤ :=
  (RingHom.fst ℤ (GammaGroupRing Γ × GammaGroupRing Γ)).comp
    (eulerCoordinatesRingEquiv k).toRingHom

theorem totalEuler_point (a : Γ) : totalEuler k (point k a) = 1 := by
  change ((eulerCoordinatesRingEquiv k) ((eulerCoordinatesRingEquiv k).symm _)).1 = 1
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem totalEuler_ray (a : Γ) : totalEuler k (ray k a) = k.rayValue := by
  change ((eulerCoordinatesRingEquiv k) ((eulerCoordinatesRingEquiv k).symm _)).1 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem totalEuler_line : totalEuler k (line (Γ := Γ) k) = k.lineValue := by
  change ((eulerCoordinatesRingEquiv k) ((eulerCoordinatesRingEquiv k).symm _)).1 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

end EulerFunction
end DiamondIntegral.Section4
