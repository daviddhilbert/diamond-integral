import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Complex.Basic

/-! Rational polynomial tuples define actual scheme morphisms from
principal affine opens. Their complex-valued points are checked against
the original rational expressions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

def principalRationalAlgebraMap {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin m) ℂ →ₐ[ℂ] Localization.Away q :=
  MvPolynomial.aeval (fun j => algebraMap _ _ (p j) * IsLocalization.Away.invSelf q)

def principalPointEvaluation {n : ℕ} (q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (hq : q.eval₂ (RingHom.id ℂ) x ≠ 0) : Localization.Away q →+* ℂ :=
  IsLocalization.Away.lift q (g := MvPolynomial.eval₂Hom (RingHom.id ℂ) x)
    (isUnit_iff_ne_zero.mpr hq)

theorem principalPointEvaluation_algebraMap {n : ℕ} (q : MvPolynomial (Fin n) ℂ)
    (x : Fin n → ℂ) (hq : q.eval₂ (RingHom.id ℂ) x ≠ 0) (p : MvPolynomial (Fin n) ℂ) :
    principalPointEvaluation q x hq (algebraMap _ _ p) = p.eval₂ (RingHom.id ℂ) x :=
  IsLocalization.Away.lift_eq q (g := MvPolynomial.eval₂Hom (RingHom.id ℂ) x) _ p

theorem principalPointEvaluation_invSelf {n : ℕ} (q : MvPolynomial (Fin n) ℂ)
    (x : Fin n → ℂ) (hq : q.eval₂ (RingHom.id ℂ) x ≠ 0) :
    principalPointEvaluation q x hq (IsLocalization.Away.invSelf q) =
      (q.eval₂ (RingHom.id ℂ) x)⁻¹ := by
  have h := congrArg (principalPointEvaluation q x hq)
    (IsLocalization.Away.mul_invSelf q (S := Localization.Away q))
  rw [map_mul, map_one, principalPointEvaluation_algebraMap] at h
  have he : principalPointEvaluation q x hq (IsLocalization.Away.invSelf q) =
      1 / q.eval₂ (RingHom.id ℂ) x := (eq_div_iff hq).mpr (by rw [mul_comm]; exact h)
  simpa only [one_div] using he

theorem principalRationalAlgebraMap_point {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (x : Fin n → ℂ) (hq : q.eval₂ (RingHom.id ℂ) x ≠ 0) :
    (principalPointEvaluation q x hq).comp (principalRationalAlgebraMap p q).toRingHom =
      MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun j => (p j).eval₂ (RingHom.id ℂ) x / q.eval₂ (RingHom.id ℂ) x) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      principalRationalAlgebraMap, MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
    rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin n) ℂ) (Localization.Away q),
      principalPointEvaluation_algebraMap]
    simp
  · intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      principalRationalAlgebraMap, MvPolynomial.aeval_X, map_mul,
      principalPointEvaluation_algebraMap, principalPointEvaluation_invSelf,
      MvPolynomial.eval₂Hom_X', div_eq_mul_inv]

def principalAffineOpenInclusion {n : ℕ} (q : MvPolynomial (Fin n) ℂ) :
    Spec (.of (Localization.Away q)) ⟶ Spec (.of (MvPolynomial (Fin n) ℂ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

theorem principalAffineOpenInclusion_isOpenImmersion {n : ℕ} (q : MvPolynomial (Fin n) ℂ) :
    IsOpenImmersion (principalAffineOpenInclusion q) := by
  unfold principalAffineOpenInclusion
  infer_instance
attribute [local instance] principalAffineOpenInclusion_isOpenImmersion

theorem principalAffineOpenInclusion_range {n : ℕ} (q : MvPolynomial (Fin n) ℂ) :
    (principalAffineOpenInclusion q).opensRange = PrimeSpectrum.basicOpen q :=
  Scheme.Hom.opensRange_localizationAway (R := .of (MvPolynomial (Fin n) ℂ)) q

def principalRationalSchemeMap {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) :
    Spec (.of (Localization.Away q)) ⟶ Spec (.of (MvPolynomial (Fin m) ℂ)) :=
  Spec.map (CommRingCat.ofHom (principalRationalAlgebraMap p q).toRingHom)

theorem principalRationalSchemeMap_point {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (x : Fin n → ℂ) (hq : q.eval₂ (RingHom.id ℂ) x ≠ 0) :
    Spec.map (CommRingCat.ofHom (principalPointEvaluation q x hq)) ≫
      principalRationalSchemeMap p q =
    Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (fun j => (p j).eval₂ (RingHom.id ℂ) x / q.eval₂ (RingHom.id ℂ) x))) := by
  rw [principalRationalSchemeMap, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (principalRationalAlgebraMap_point p q x hq)

end DiamondIntegral.Section5
