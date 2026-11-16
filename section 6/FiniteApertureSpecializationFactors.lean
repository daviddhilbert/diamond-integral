import «section 6».DownstreamApertureIdealTest

/-! The finite geometric factor occurring in the Section 8 specialization
of a relative annular relation. Its vanishing after T is sent to the
affine-line class is pure algebra. The actual family-to-specialization
formula and rational trace closure are separate geometric obligations. -/

noncomputable section
open Classical

namespace DiamondIntegral.Section6.ApertureSpecializationTest

def annularFactor {R : Type*} [CommRing R] (L q : R) (n : ℕ) : R :=
  (L-1) * ∑ i ∈ Finset.range n, q^(i+1) + q^n - 1

theorem annularFactor_eq {R : Type*} [CommRing R] (L q : R) (n : ℕ) :
    annularFactor L q n = (L*q-1) * ∑ i ∈ Finset.range n, q^i := by
  induction n with
  | zero => simp [annularFactor]
  | succ n ih =>
    simp only [annularFactor,Finset.sum_range_succ,pow_succ] at ih ⊢
    linear_combination ih

theorem annularFactor_zero_of_inverse {R : Type*} [CommRing R] (L q : R)
    (h : L*q = 1) (n : ℕ) : annularFactor L q n = 0 := by
  rw [annularFactor_eq,h,sub_self,zero_mul]

theorem integer_aperture_test (N : ℕ) : annularFactor (1 : ℤ) (-1) (2*N) = 0 := by
  simp [annularFactor,pow_mul]

theorem ramified_two_label_test : (2 : ℤ) * annularFactor 1 (-1) 1 = -4 := by
  norm_num [annularFactor]

end DiamondIntegral.Section6.ApertureSpecializationTest
