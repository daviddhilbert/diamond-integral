module

public import «section 4».TensorCoactionGrading
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-! A tensor ring map is graded when it sends homogeneous pure tensors
to the corresponding degree. Finite factor decompositions prove this
criterion on the whole tensor, including coaction compatibility. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Classical
open scoped TensorProduct

namespace DiamondIntegral.Section4.TensorGradedMaps
open TensorPolynomialCoaction TensorCoactionGrading PolynomialCoactionGrading
variable {C A B R : Type*} [CommRing C] [CommRing A] [CommRing B] [CommRing R] [Algebra C A] [Algebra C B]
variable (d : Data C A B) (e : Coaction R) (f : A ⊗[C] B →+* R)

def compatibilitySubgroup : AddSubgroup (A ⊗[C] B) where
  carrier := {z | ((Polynomial.mapRingHom f).comp (coactionMap d)) z = (e.map.comp f) z}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ((Polynomial.mapRingHom f).comp (coactionMap d)) (x + y) = (e.map.comp f) (x + y)
    rw [map_add, map_add, hx, hy]
  neg_mem' := by
    intro x hx
    change ((Polynomial.mapRingHom f).comp (coactionMap d)) (-x) = (e.map.comp f) (-x)
    rw [map_neg, map_neg, hx]

theorem eigen_mem_compatibility {n : ℕ} {z : A ⊗[C] B}
    (hz : coactionMap d z = Polynomial.monomial n z) (hf : f z ∈ e.piece n) : z ∈ compatibilitySubgroup d e f := by
  change (coactionMap d z).map f = e.map (f z)
  rw [hz, Polynomial.map_monomial]
  exact hf.symm

theorem tmul_mem_compatibility
    (h : ∀ m n (a : A) (b : B), a ∈ d.left.piece m → b ∈ d.right.piece n → f (a ⊗ₜ[C] b) ∈ e.piece (m + n))
    (a : A) (b : B) : a ⊗ₜ[C] b ∈ compatibilitySubgroup d e f := by
  rw [← d.left.sum_coefficients a, TensorProduct.sum_tmul]
  apply (compatibilitySubgroup d e f).sum_mem
  intro m hm
  rw [← d.right.sum_coefficients b, TensorProduct.tmul_sum]
  apply (compatibilitySubgroup d e f).sum_mem
  intro n hn
  exact eigen_mem_compatibility d e f
    (coactionMap_tmul_eigen d (d.left.coefficient_mem a m) (d.right.coefficient_mem b n))
    (h m n _ _ (d.left.coefficient_mem a m) (d.right.coefficient_mem b n))

theorem map_coaction
    (h : ∀ m n (a : A) (b : B), a ∈ d.left.piece m → b ∈ d.right.piece n → f (a ⊗ₜ[C] b) ∈ e.piece (m + n)) :
    (Polynomial.mapRingHom f).comp (coactionMap d) = e.map.comp f := by
  apply RingHom.ext
  intro z
  change z ∈ compatibilitySubgroup d e f
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact tmul_mem_compatibility d e f h a b
  | add x y hx hy => exact (compatibilitySubgroup d e f).add_mem hx hy

theorem map_mem
    (h : ∀ m n (a : A) (b : B), a ∈ d.left.piece m → b ∈ d.right.piece n → f (a ⊗ₜ[C] b) ∈ e.piece (m + n))
    {n : ℕ} {z : A ⊗[C] B} (hz : z ∈ piece d n) : f z ∈ e.piece n := by
  change coactionMap d z = Polynomial.monomial n z at hz
  change e.map (f z) = Polynomial.monomial n (f z)
  have he : e.map (f z) = (coactionMap d z).map f := (RingHom.congr_fun (map_coaction d e f h) z).symm
  rw [he, hz, Polynomial.map_monomial]

def gradedMap
    (h : ∀ m n (a : A) (b : B), a ∈ d.left.piece m → b ∈ d.right.piece n → f (a ⊗ₜ[C] b) ∈ e.piece (m + n)) :
    GradedRingHom (piece d) e.piece where
  toRingHom := f
  map_mem := map_mem d e f h

end DiamondIntegral.Section4.TensorGradedMaps
