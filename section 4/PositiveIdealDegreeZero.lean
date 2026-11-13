import «section 4».RVZeroDegreeEquivalences
import «section 4».PolynomialCoactionQuotient

/-! A homogeneous quotient whose ideal vanishes under the zero-degree
projection preserves the entire zero-degree subring. Positive-degree
homogeneous generators satisfy that vanishing condition. -/

set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
variable {R : Type*} [CommRing R]
variable (c : Coaction R) (I : Ideal R)

theorem zeroProjection_of_positive_mem {n : ℕ} {x : R} (hn : n ≠ 0) (hx : x ∈ c.piece n) :
    c.zeroProjection x = 0 := by
  change (c.map x).coeff 0 = 0
  change c.map x = Polynomial.monomial n x at hx
  rw [hx]
  simp only [Polynomial.coeff_monomial, hn, ite_false]

theorem quotient_injective_on_zero (hker : I ≤ RingHom.ker c.zeroProjection) :
    Set.InjOn (Ideal.Quotient.mk I) (c.piece 0) := by
  intro x hx y hy hxy
  let f := Ideal.Quotient.lift I c.zeroProjection (fun _ hz => hker hz)
  have he := congrArg f hxy
  change c.zeroProjection x = c.zeroProjection y at he
  rwa [c.zeroProjection_of_mem hx, c.zeroProjection_of_mem hy] at he

theorem quotient_surjective_on_zero (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I)
    (x : R ⧸ I) (hx : x ∈ (c.quotient I hI).piece 0) :
    ∃ r : R, r ∈ c.piece 0 ∧ Ideal.Quotient.mk I r = x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨c.zeroProjection r, c.zeroProjection_mem r, ?_⟩
  have he := congrArg (fun p : Polynomial (R ⧸ I) => p.coeff 0) hx
  change ((c.map r).map (Ideal.Quotient.mk I)).coeff 0 =
    (Polynomial.monomial 0 (Ideal.Quotient.mk I r)).coeff 0 at he
  rw [Polynomial.coeff_map, Polynomial.coeff_monomial_same] at he
  exact he

def quotientZeroMap (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I) :
    c.zeroSubring →+* (c.quotient I hI).zeroSubring :=
  ((Ideal.Quotient.mk I).comp c.zeroSubring.subtype).codRestrict (c.quotient I hI).zeroSubring
    (fun x => c.quotient_mem I hI x.property)

def quotientZeroEquiv (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I)
    (hker : I ≤ RingHom.ker c.zeroProjection) : c.zeroSubring ≃+* (c.quotient I hI).zeroSubring :=
  RingEquiv.ofBijective (c.quotientZeroMap I hI) ⟨(by
    intro x y h
    apply Subtype.ext
    exact c.quotient_injective_on_zero I hker x.property y.property (congrArg Subtype.val h)), (by
    intro x
    obtain ⟨r, hr, hrx⟩ := c.quotient_surjective_on_zero I hI x.val x.property
    exact ⟨⟨r, hr⟩, Subtype.ext hrx⟩)⟩

theorem quotientZeroEquiv_apply (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I)
    (hker : I ≤ RingHom.ker c.zeroProjection) (x : c.zeroSubring) :
    (c.quotientZeroEquiv I hI hker x).val = Ideal.Quotient.mk I x.val := rfl

end DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
