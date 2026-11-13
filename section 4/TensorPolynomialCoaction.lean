module

public import «section 4».PolynomialCoactionGrading
public import Mathlib.RingTheory.TensorProduct.Maps

/-! Compatible polynomial coactions on two algebras give a polynomial
ring map on their tensor over the coefficient ring. Its counit and the
degree of homogeneous pure tensors are proved here. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Classical
open scoped TensorProduct

namespace DiamondIntegral.Section4.TensorPolynomialCoaction
open PolynomialCoactionGrading

structure Data (C A B : Type*) [CommRing C] [CommRing A] [CommRing B] [Algebra C A] [Algebra C B] where
  base : Coaction C
  left : Coaction A
  right : Coaction B
  left_compatible : (Polynomial.mapRingHom (algebraMap C A)).comp base.map = left.map.comp (algebraMap C A)
  right_compatible : (Polynomial.mapRingHom (algebraMap C B)).comp base.map = right.map.comp (algebraMap C B)

variable {C A B : Type*} [CommRing C] [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]

def leftInclusion : A →+* A ⊗[C] B := (Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] B).toRingHom

def rightInclusion : B →+* A ⊗[C] B := (Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).toRingHom

theorem leftInclusion_base : (leftInclusion (C := C) (A := A) (B := B)).comp (algebraMap C A) = algebraMap C (A ⊗[C] B) := by
  ext c
  exact (Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] B).commutes c

theorem rightInclusion_base : (rightInclusion (C := C) (A := A) (B := B)).comp (algebraMap C B) = algebraMap C (A ⊗[C] B) := by
  ext c
  exact (Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).commutes c

variable (d : Data C A B)

def baseMap : C →+* Polynomial (A ⊗[C] B) :=
  (Polynomial.mapRingHom (algebraMap C (A ⊗[C] B))).comp d.base.map

def leftMap : A →+* Polynomial (A ⊗[C] B) :=
  (Polynomial.mapRingHom (leftInclusion (C := C) (B := B))).comp d.left.map

def rightMap : B →+* Polynomial (A ⊗[C] B) :=
  (Polynomial.mapRingHom (rightInclusion (C := C) (A := A))).comp d.right.map

theorem leftMap_base : (leftMap d).comp (algebraMap C A) = baseMap d := by
  apply RingHom.ext
  intro c
  change (d.left.map (algebraMap C A c)).map leftInclusion = (d.base.map c).map (algebraMap C (A ⊗[C] B))
  have he : d.left.map (algebraMap C A c) = (d.base.map c).map (algebraMap C A) :=
    (RingHom.congr_fun d.left_compatible c).symm
  rw [he, Polynomial.map_map, leftInclusion_base]

theorem rightMap_base : (rightMap d).comp (algebraMap C B) = baseMap d := by
  apply RingHom.ext
  intro c
  change (d.right.map (algebraMap C B c)).map rightInclusion = (d.base.map c).map (algebraMap C (A ⊗[C] B))
  have he : d.right.map (algebraMap C B c) = (d.base.map c).map (algebraMap C B) :=
    (RingHom.congr_fun d.right_compatible c).symm
  rw [he, Polynomial.map_map, rightInclusion_base]

def coactionMap : A ⊗[C] B →+* Polynomial (A ⊗[C] B) := by
  letI : Algebra C (Polynomial (A ⊗[C] B)) := (baseMap d).toAlgebra
  letI : SMul C (Polynomial (A ⊗[C] B)) := (baseMap d).toAlgebra.toSMul
  letI : Module C (Polynomial (A ⊗[C] B)) := Algebra.toModule
  letI : IsScalarTower C C (Polynomial (A ⊗[C] B)) := ⟨fun r s p => by
    change (baseMap d) (r * s) * p = (baseMap d) r * ((baseMap d) s * p)
    rw [map_mul, mul_assoc]⟩
  let f : A →ₐ[C] Polynomial (A ⊗[C] B) :=
    { toRingHom := leftMap d
      commutes' c := RingHom.congr_fun (leftMap_base d) c }
  let g : B →ₐ[C] Polynomial (A ⊗[C] B) :=
    { toRingHom := rightMap d
      commutes' c := RingHom.congr_fun (rightMap_base d) c }
  exact (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom

theorem coactionMap_tmul (a : A) (b : B) :
    coactionMap d (a ⊗ₜ[C] b) = (d.left.map a).map leftInclusion * (d.right.map b).map rightInclusion := rfl

theorem coactionMap_tmul_eigen {m n : ℕ} {a : A} {b : B}
    (ha : d.left.map a = Polynomial.monomial m a) (hb : d.right.map b = Polynomial.monomial n b) :
    coactionMap d (a ⊗ₜ[C] b) = Polynomial.monomial (m + n) (a ⊗ₜ[C] b) := by
  rw [coactionMap_tmul, ha, hb, Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.monomial_mul_monomial]
  apply congrArg (Polynomial.monomial (m + n))
  change (a ⊗ₜ[C] 1) * (1 ⊗ₜ[C] b) = a ⊗ₜ[C] b
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem coactionMap_counit : (Polynomial.evalRingHom 1).comp (coactionMap d) = RingHom.id (A ⊗[C] B) := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change Polynomial.eval 1 (coactionMap d (a ⊗ₜ[C] b)) = a ⊗ₜ[C] b
    rw [coactionMap_tmul, Polynomial.eval_mul, Polynomial.eval_map, Polynomial.eval₂_at_one,
      Polynomial.eval_map, Polynomial.eval₂_at_one]
    have ha : Polynomial.eval 1 (d.left.map a) = a := RingHom.congr_fun d.left.counit a
    have hb : Polynomial.eval 1 (d.right.map b) = b := RingHom.congr_fun d.right.counit b
    rw [ha, hb]
    change (a ⊗ₜ[C] 1) * (1 ⊗ₜ[C] b) = a ⊗ₜ[C] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end DiamondIntegral.Section4.TensorPolynomialCoaction
