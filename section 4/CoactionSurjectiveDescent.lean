import «section 4».CoactionGradedMaps
import Mathlib.RingTheory.Ideal.Maps

/-! Descent of graded ring maps through a graded surjection. Homogeneous
preimages are constructed by taking the required coefficient of any
preimage; no injectivity of the surjection is required. -/

set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable (c : Coaction R) (d : Coaction S) (e : Coaction T)
variable (f : R →+* S) (hf : Function.Surjective f)
variable (hfgrade : ∀ n x, x ∈ c.piece n → f x ∈ d.piece n)

include hf hfgrade in
theorem homogeneous_preimage {n : ℕ} {y : S} (hy : y ∈ d.piece n) :
    ∃ x : R, x ∈ c.piece n ∧ f x = y := by
  obtain ⟨r, hr⟩ := hf y
  refine ⟨(c.map r).coeff n, c.coefficient_mem r n, ?_⟩
  have he := congrArg (fun p : Polynomial S => p.coeff n)
    (RingHom.congr_fun (c.map_coaction_of_mem d f hfgrade) r)
  change ((c.map r).map f).coeff n = (d.map (f r)).coeff n at he
  change d.map y = Polynomial.monomial n y at hy
  rw [hr, hy, Polynomial.coeff_map, Polynomial.coeff_monomial] at he
  simpa only [ite_true] using he

def surjectiveDescent (g : R →+* T) (hker : RingHom.ker f ≤ RingHom.ker g) : S →+* T :=
  f.liftOfSurjective hf ⟨g, hker⟩

theorem surjectiveDescent_apply (g : R →+* T) (hker : RingHom.ker f ≤ RingHom.ker g) (x : R) :
    surjectiveDescent f hf g hker (f x) = g x :=
  RingHom.liftOfSurjective_comp_apply f hf ⟨g, hker⟩ x

def gradedSurjectiveDescent (g : R →+* T) (hker : RingHom.ker f ≤ RingHom.ker g)
    (hggrade : ∀ n x, x ∈ c.piece n → g x ∈ e.piece n) : GradedRingHom d.piece e.piece where
  toRingHom := surjectiveDescent f hf g hker
  map_mem := by
    intro n y hy
    obtain ⟨x, hx, rfl⟩ := homogeneous_preimage c d f hf hfgrade hy
    rw [surjectiveDescent_apply]
    exact hggrade n x hx

theorem surjectiveDescent_unique (g : R →+* T) (hker : RingHom.ker f ≤ RingHom.ker g)
    (h : S →+* T) (hh : h.comp f = g) : h = surjectiveDescent f hf g hker :=
  RingHom.eq_liftOfSurjective f hf g hker h hh

end DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
