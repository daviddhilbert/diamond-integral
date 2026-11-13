import «section 4».TensorCoactionGrading
import «section 4».RVZeroDegreeEquivalences

/-! If every zero-degree element of the right factor comes from a
zero-degree coefficient, every zero-degree tensor comes from the left
zero-degree subring. This uses balanced pure tensors and additive
generation, with no injectivity assumption. -/

set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace DiamondIntegral.Section4.TensorZeroDegree
open TensorPolynomialCoaction TensorCoactionGrading
variable {C A B : Type*} [CommRing C] [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]
variable (d : Data C A B)

theorem zeroProjection_tmul (a : A) (b : B) :
    (coaction d).zeroProjection (a ⊗ₜ[C] b) = d.left.zeroProjection a ⊗ₜ[C] d.right.zeroProjection b := by
  change (coactionMap d (a ⊗ₜ[C] b)).coeff 0 = _
  rw [coactionMap_tmul, Polynomial.mul_coeff_zero, Polynomial.coeff_map, Polynomial.coeff_map]
  change (d.left.zeroProjection a ⊗ₜ[C] 1) * (1 ⊗ₜ[C] d.right.zeroProjection b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem left_base_mem {c : C} (hc : c ∈ d.base.piece 0) : algebraMap C A c ∈ d.left.piece 0 := by
  have he := RingHom.congr_fun d.left_compatible c
  change (d.base.map c).map (algebraMap C A) = d.left.map (algebraMap C A c) at he
  change d.base.map c = Polynomial.monomial 0 c at hc
  rw [hc, Polynomial.map_monomial] at he
  exact he.symm

def leftZeroInclusion : d.left.zeroSubring →+* A ⊗[C] B :=
  (leftInclusion (C := C) (A := A) (B := B)).comp d.left.zeroSubring.subtype

theorem zeroProjection_range
    (hbase : ∀ b ∈ d.right.piece 0, ∃ c : C, c ∈ d.base.piece 0 ∧ algebraMap C B c = b)
    (z : A ⊗[C] B) : (coaction d).zeroProjection z ∈ (leftZeroInclusion d).range := by
  letI := d.left.grading
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [zeroProjection_tmul]
    obtain ⟨c, hc, hcb⟩ := hbase (d.right.zeroProjection b) (d.right.zeroProjection_mem b)
    have hca : c • d.left.zeroProjection a ∈ d.left.piece 0 := by
      simpa only [Algebra.smul_def] using SetLike.mul_mem_graded (left_base_mem d hc) (d.left.zeroProjection_mem a)
    refine ⟨⟨c • d.left.zeroProjection a, hca⟩, ?_⟩
    change (c • d.left.zeroProjection a) ⊗ₜ[C] 1 = d.left.zeroProjection a ⊗ₜ[C] d.right.zeroProjection b
    rw [← hcb, Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul c (d.left.zeroProjection a) (1 : B)
  | add x y hx hy =>
    rw [map_add]
    exact (leftZeroInclusion d).range.add_mem hx hy

theorem zero_surjective
    (hbase : ∀ b ∈ d.right.piece 0, ∃ c : C, c ∈ d.base.piece 0 ∧ algebraMap C B c = b)
    {z : A ⊗[C] B} (hz : z ∈ piece d 0) :
    ∃ a : A, a ∈ d.left.piece 0 ∧ leftInclusion a = z := by
  obtain ⟨a, ha⟩ := zeroProjection_range d hbase z
  exact ⟨a.val, a.property, ha.trans ((coaction d).zeroProjection_of_mem hz)⟩

end DiamondIntegral.Section4.TensorZeroDegree
