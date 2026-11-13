module

public import «section 4».EulerDecomposition
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-! The actual convolution ring has a point-valued ring projection sending
p_a to p_a, q_a to -p_a and the whole line to zero. It is the third model
coordinate, followed by the actual point group-ring embedding. -/

@[expose] public noncomputable section
set_option autoImplicit false

namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

def fullPointMonoidHom (k : EulerKind) : Multiplicative Γ →* EulerFunction k Γ where
  toFun a := point k (Multiplicative.toAdd a)
  map_one' := point_zero k
  map_mul' a b := (point_mul k (Multiplicative.toAdd a) (Multiplicative.toAdd b)).symm

def fullPointRing (k : EulerKind) : GammaGroupRing Γ →+* EulerFunction k Γ :=
  ((AddMonoidAlgebra.lift ℤ (EulerFunction k Γ) Γ) (fullPointMonoidHom k)).toRingHom

theorem fullPointRing_single (k : EulerKind) (a : Γ) (n : ℤ) :
    fullPointRing k (AddMonoidAlgebra.single a n) = n • point k a :=
  AddMonoidAlgebra.lift_single (fullPointMonoidHom k) a n

def endpointCoordinate (k : EulerKind) : EulerFunction k Γ →+* GammaGroupRing Γ :=
  ((RingHom.snd (GammaGroupRing Γ) (GammaGroupRing Γ)).comp
    (RingHom.snd ℤ (GammaGroupRing Γ × GammaGroupRing Γ))).comp (eulerCoordinatesRingEquiv k).toRingHom

theorem endpointCoordinate_point (k : EulerKind) (a : Γ) :
    endpointCoordinate k (point k a) = AddMonoidAlgebra.single a 1 := by
  change ((eulerCoordinatesRingEquiv k) ((eulerCoordinatesRingEquiv k).symm (modelPoint a))).2.2 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem endpointCoordinate_ray (k : EulerKind) (a : Γ) :
    endpointCoordinate k (ray k a) = -AddMonoidAlgebra.single a 1 := by
  change ((eulerCoordinatesRingEquiv k) ((eulerCoordinatesRingEquiv k).symm (modelRay k a))).2.2 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem endpointCoordinate_line (k : EulerKind) : endpointCoordinate (Γ := Γ) k (line k) = 0 := by
  change ((eulerCoordinatesRingEquiv k) ((eulerCoordinatesRingEquiv k).symm (modelLine k))).2.2 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

def endpointProjection (k : EulerKind) : EulerFunction k Γ →+* EulerFunction k Γ :=
  (fullPointRing k).comp (endpointCoordinate k)

theorem endpointProjection_point (k : EulerKind) (a : Γ) : endpointProjection k (point k a) = point k a := by
  rw [endpointProjection, RingHom.comp_apply, endpointCoordinate_point, fullPointRing_single, one_zsmul]

theorem endpointProjection_ray (k : EulerKind) (a : Γ) : endpointProjection k (ray k a) = -point k a := by
  rw [endpointProjection, RingHom.comp_apply, endpointCoordinate_ray, map_neg, fullPointRing_single, one_zsmul]

theorem endpointProjection_line (k : EulerKind) : endpointProjection (Γ := Γ) k (line k) = 0 := by
  rw [endpointProjection, RingHom.comp_apply, endpointCoordinate_line, map_zero]

end DiamondIntegral.Section4.EulerFunction
