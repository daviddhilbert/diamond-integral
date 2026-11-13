module

public import «section 4».TensorPolynomialCoaction

/-! The tensor polynomial map is coassociative. Finite decompositions in
the two factors generate homogeneous pure tensors, yielding the complete
natural-number grading of the tensor over the graded coefficient ring. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Classical
open scoped TensorProduct

namespace DiamondIntegral.Section4.TensorCoactionGrading
open TensorPolynomialCoaction PolynomialCoactionGrading
variable {C A B : Type*} [CommRing C] [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]
variable (d : Data C A B)

def coassocSubgroup : AddSubgroup (A ⊗[C] B) where
  carrier := {z | ((Polynomial.mapRingHom (coactionMap d)).comp (coactionMap d)) z =
    (PolynomialDiagonal.diagonal.comp (coactionMap d)) z}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ((Polynomial.mapRingHom (coactionMap d)).comp (coactionMap d)) (x + y) =
      (PolynomialDiagonal.diagonal.comp (coactionMap d)) (x + y)
    rw [map_add, map_add, hx, hy]
  neg_mem' := by
    intro x hx
    change ((Polynomial.mapRingHom (coactionMap d)).comp (coactionMap d)) (-x) =
      (PolynomialDiagonal.diagonal.comp (coactionMap d)) (-x)
    rw [map_neg, map_neg, hx]

theorem eigen_mem_coassoc {n : ℕ} {z : A ⊗[C] B}
    (hz : coactionMap d z = Polynomial.monomial n z) : z ∈ coassocSubgroup d := by
  change (coactionMap d z).map (coactionMap d) = PolynomialDiagonal.diagonal (coactionMap d z)
  rw [hz, Polynomial.map_monomial, hz, PolynomialDiagonal.diagonal_monomial]

theorem coassoc_tmul_mem (a : A) (b : B) : a ⊗ₜ[C] b ∈ coassocSubgroup d := by
  rw [← d.left.sum_coefficients a, TensorProduct.sum_tmul]
  apply (coassocSubgroup d).sum_mem
  intro m hm
  rw [← d.right.sum_coefficients b, TensorProduct.tmul_sum]
  apply (coassocSubgroup d).sum_mem
  intro n hn
  exact eigen_mem_coassoc d (coactionMap_tmul_eigen d (d.left.coefficient_mem a m) (d.right.coefficient_mem b n))

theorem coactionMap_coassoc :
    (Polynomial.mapRingHom (coactionMap d)).comp (coactionMap d) = PolynomialDiagonal.diagonal.comp (coactionMap d) := by
  apply RingHom.ext
  intro z
  change z ∈ coassocSubgroup d
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact coassoc_tmul_mem d a b
  | add x y hx hy => exact (coassocSubgroup d).add_mem hx hy

def coaction : Coaction (A ⊗[C] B) where
  map := coactionMap d
  counit := coactionMap_counit d
  coassoc := coactionMap_coassoc d

def piece (n : ℕ) : AddSubgroup (A ⊗[C] B) := (coaction d).piece n

instance gradedRing : GradedRing (piece d) := (coaction d).grading

theorem tmul_mem {m n : ℕ} {a : A} {b : B} (ha : a ∈ d.left.piece m) (hb : b ∈ d.right.piece n) :
    a ⊗ₜ[C] b ∈ piece d (m + n) := coactionMap_tmul_eigen d ha hb

end DiamondIntegral.Section4.TensorCoactionGrading
