import «section 4».CoactionGradedMaps
import «section 4».RVZeroDegreeRES

/-! Kernels of coaction-compatible ring maps are homogeneous. If the
map is injective in degree zero, every kernel element is a finite sum
of positive-degree homogeneous kernel elements. -/

set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
variable {R S : Type*} [CommRing R] [CommRing S]
variable (c : Coaction R) (e : Coaction S) (f : R →+* S)
variable (h : (Polynomial.mapRingHom f).comp c.map = e.map.comp f)
include h

theorem kernel_coefficient_mem (x : R) (hx : f x = 0) (n : ℕ) :
    f ((c.map x).coeff n) = 0 := by
  have he := congrArg (fun p : Polynomial S => p.coeff n) (RingHom.congr_fun h x)
  change ((c.map x).map f).coeff n = (e.map (f x)).coeff n at he
  rw [Polynomial.coeff_map, hx, map_zero, Polynomial.coeff_zero] at he
  exact he

theorem kernel_homogeneous : letI := c.grading
    (RingHom.ker f).IsHomogeneous c.piece := by
  letI := c.grading
  intro n x hx
  rw [c.decompose_coefficient]
  exact c.kernel_coefficient_mem e f h x hx n

theorem kernel_zeroProjection
    (hinj : Set.InjOn f (c.piece 0)) (x : R) (hx : f x = 0) : c.zeroProjection x = 0 := by
  apply hinj (c.zeroProjection_mem x) (c.piece 0).zero_mem
  exact (c.kernel_coefficient_mem e f h x hx 0).trans (map_zero f).symm

theorem kernel_positive_decomposition
    (hinj : Set.InjOn f (c.piece 0)) (x : R) (hx : f x = 0) :
    (∑ n ∈ (c.map x).support.filter (fun n => 0 < n), (c.map x).coeff n) = x := by
  have hzero : (c.map x).coeff 0 = 0 := c.kernel_zeroProjection e f h hinj x hx
  have he : (∑ n ∈ (c.map x).support.filter (fun n => 0 < n), (c.map x).coeff n) =
      ∑ n ∈ (c.map x).support, (c.map x).coeff n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnf
    have hn0 : n = 0 := by
      by_contra hne
      exact hnf (Finset.mem_filter.mpr ⟨hn, Nat.pos_of_ne_zero hne⟩)
    simpa only [hn0] using hzero
  exact he.trans (c.sum_coefficients x)

end DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
