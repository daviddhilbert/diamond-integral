import «section 4».CoactionGradedMaps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A degree-preserving ring equivalence induces a degree-preserving
quotient equivalence for matching homogeneous ideals, in both directions. -/

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section4.CoactionQuotientEquivalence
open PolynomialCoactionGrading
variable {R S : Type*} [CommRing R] [CommRing S]

variable (c : Coaction R) (d : Coaction S) (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
variable (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I)
variable (hJ : ∀ n x, x ∈ J → (d.map x).coeff n ∈ J)
variable (he : J = I.map (e : R →+* S))

theorem forward_mem (hf : ∀ n x, x ∈ c.piece n → e x ∈ d.piece n)
    {n : ℕ} {x : R ⧸ I} (hx : x ∈ (c.quotient I hI).piece n) :
    Ideal.quotientEquiv I J e he x ∈ (d.quotient J hJ).piece n := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hc : Ideal.Quotient.mk I ((c.map r).coeff n) = Ideal.Quotient.mk I r := by
    have hh := congrArg (fun p : Polynomial (R ⧸ I) => p.coeff n) hx
    change (((c.map r).map (Ideal.Quotient.mk I)).coeff n) = (Polynomial.monomial n (Ideal.Quotient.mk I r)).coeff n at hh
    simpa only [Polynomial.coeff_map, Polynomial.coeff_monomial, ite_true] using hh
  rw [← hc]
  change Ideal.Quotient.mk J (e ((c.map r).coeff n)) ∈ (d.quotient J hJ).piece n
  exact d.quotient_mem J hJ (hf n _ (c.coefficient_mem r n))

theorem inverse_mem (hf : ∀ n x, x ∈ d.piece n → e.symm x ∈ c.piece n)
    {n : ℕ} {x : S ⧸ J} (hx : x ∈ (d.quotient J hJ).piece n) :
    (Ideal.quotientEquiv I J e he).symm x ∈ (c.quotient I hI).piece n := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hd : Ideal.Quotient.mk J ((d.map r).coeff n) = Ideal.Quotient.mk J r := by
    have hh := congrArg (fun p : Polynomial (S ⧸ J) => p.coeff n) hx
    change (((d.map r).map (Ideal.Quotient.mk J)).coeff n) = (Polynomial.monomial n (Ideal.Quotient.mk J r)).coeff n at hh
    simpa only [Polynomial.coeff_map, Polynomial.coeff_monomial, ite_true] using hh
  rw [← hd]
  change Ideal.Quotient.mk I (e.symm ((d.map r).coeff n)) ∈ (c.quotient I hI).piece n
  exact c.quotient_mem I hI (hf n _ (d.coefficient_mem r n))

theorem mem_iff (hf : ∀ n x, x ∈ c.piece n → e x ∈ d.piece n)
    (hg : ∀ n x, x ∈ d.piece n → e.symm x ∈ c.piece n) (n : ℕ) (x : R ⧸ I) :
    Ideal.quotientEquiv I J e he x ∈ (d.quotient J hJ).piece n ↔ x ∈ (c.quotient I hI).piece n := by
  constructor
  · intro hx
    have h := inverse_mem c d e I J hI hJ he hg hx
    rwa [RingEquiv.symm_apply_apply] at h
  · exact forward_mem c d e I J hI hJ he hf


theorem ideal_coefficients_of_map (hMap : J = I.map (e : R →+* S))
    (hcmap : (Polynomial.mapRingHom (e : R →+* S)).comp c.map = d.map.comp (e : R →+* S))
    (hOld : ∀ n x, x ∈ J → (d.map x).coeff n ∈ J) :
    ∀ n x, x ∈ I → (c.map x).coeff n ∈ I := by
  intro n x hx
  have hxJ : e x ∈ J := by
    rw [hMap]
    exact Ideal.mem_map_of_mem _ hx
  have hec : (e : R →+* S) ((c.map x).coeff n) = (d.map (e x)).coeff n := by
    have hh := congrArg (fun p : Polynomial S => p.coeff n) (RingHom.congr_fun hcmap x)
    change (((c.map x).map (e : R →+* S)).coeff n) = (d.map (e x)).coeff n at hh
    simpa only [Polynomial.coeff_map] using hh
  have hm : (e : R →+* S) ((c.map x).coeff n) ∈ I.map (e : R →+* S) := by
    rw [← hMap, hec]
    exact hOld n _ hxJ
  obtain ⟨y, hy, hye⟩ := (Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective).mp hm
  exact e.injective hye ▸ hy

end DiamondIntegral.Section4.CoactionQuotientEquivalence
