import «section 5».ComplexAffineRationalContinuity

/-! Actual constructible subsets of complex polynomial spectra for
original pure-field definable tuple sets. The full scheme subset is
constructed, rather than only the topology on its complex points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language Topology TopologicalSpace
open SpecialTransformations.Section7
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem complex_definable_spectrum_constructible {n : ℕ} (D : Set (Fin n → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D) :
    ∃ Z : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ)), IsConstructible Z ∧
      ∀ x, x ∈ D ↔ complexPolynomialPoint x ∈ Z := by
  obtain ⟨S, hS, he⟩ := field_definable_constructible (⊤ : Subfield ℂ) D hD
  let f : MvPolynomial (Fin n) (⊤ : Subfield ℂ) →+* MvPolynomial (Fin n) ℂ :=
    MvPolynomial.map (⊤ : Subfield ℂ).subtype
  have hZ := hS.preimage (PrimeSpectrum.continuous_comap f)
    (fun _ _ _ => fun _ _ _ => NoetherianSpace.isCompact _)
  refine ⟨PrimeSpectrum.comap f ⁻¹' S, hZ, ?_⟩
  intro x
  have hp : PrimeSpectrum.comap f (complexPolynomialPoint x) = fieldTuplePrime (⊤ : Subfield ℂ) x := by
    ext p
    simp [f, complexPolynomialPoint, fieldTuplePrime, RingHom.mem_ker]
  change x ∈ D ↔ PrimeSpectrum.comap f (complexPolynomialPoint x) ∈ S
  rw [hp]
  exact he x

def complexTupleSpectrumPoint {α : Type} (x : α → ℂ) : PrimeSpectrum (MvPolynomial α ℂ) :=
  ⟨RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℂ) x), RingHom.ker_isPrime _⟩

theorem complex_definable_finite_spectrum_constructible {α : Type} [Fintype α]
    (D : Set (α → ℂ)) (hD : (Set.univ : Set ℂ).Definable Language.ring D) :
    ∃ Z : Set (PrimeSpectrum (MvPolynomial α ℂ)), IsConstructible Z ∧
      ∀ x, x ∈ D ↔ complexTupleSpectrumPoint x ∈ Z := by
  let e := Fintype.equivFin α
  let D' : Set (Fin (Fintype.card α) → ℂ) := {x | x ∘ e ∈ D}
  have hD' : (Set.univ : Set ℂ).Definable Language.ring D' := hD.preimage_comp e
  obtain ⟨Z, hZ, he⟩ := complex_definable_spectrum_constructible D' hD'
  let r : MvPolynomial (Fin (Fintype.card α)) ℂ →+* MvPolynomial α ℂ :=
    (MvPolynomial.rename e.symm).toRingHom
  have hpre := hZ.preimage (PrimeSpectrum.continuous_comap r)
    (fun _ _ _ => fun _ _ _ => NoetherianSpace.isCompact _)
  refine ⟨PrimeSpectrum.comap r ⁻¹' Z, hpre, ?_⟩
  intro x
  have hp : PrimeSpectrum.comap r (complexTupleSpectrumPoint x) =
      complexPolynomialPoint (x ∘ e.symm) := by
    ext p
    simp [r, complexTupleSpectrumPoint, complexPolynomialPoint, RingHom.mem_ker,
      MvPolynomial.eval₂_rename]
  change x ∈ D ↔ PrimeSpectrum.comap r (complexTupleSpectrumPoint x) ∈ Z
  rw [hp, ← he]
  have hx : (x ∘ e.symm) ∘ e = x := by
    funext i
    exact congrArg x (e.symm_apply_apply i)
  change x ∈ D ↔ (x ∘ e.symm) ∘ e ∈ D
  rw [hx]

end DiamondIntegral.Section5
