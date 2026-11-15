import «section 5».DiagonalGeometricValues
import «section 5».ConstructibleFieldDefinability

/-! Actual constructible spectrum loci define pure-field complex domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language Topology
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem complex_polynomial_zero_definable {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    (Set.univ : Set ℂ).Definable Language.ring {x | p.eval₂ (RingHom.id ℂ) x = 0} := by
  let c : ℂ →+* (⊤ : Subfield ℂ) := Subfield.topEquiv.symm.toRingHom
  have hc : (⊤ : Subfield ℂ).subtype.comp c = RingHom.id ℂ := by ext z; rfl
  have h := mvPolynomial_zeroSet_definable (⊤ : Subfield ℂ) (p.map c)
  convert h using 1
  ext x
  simp only [MvPolynomial.eval₂_map, hc]

theorem complex_basic_constructible_domain_definable {n : ℕ}
    (D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n) ℂ)) :
    (Set.univ : Set ℂ).Definable Language.ring {x | complexTupleSpectrumPoint x ∈ D.toSet} := by
  have hg : (Set.univ : Set ℂ).Definable Language.ring
      {x : Fin n → ℂ | ∀ i, (D.g i).eval₂ (RingHom.id ℂ) x = 0} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i => complex_polynomial_zero_definable (D.g i))
  convert hg.inter (complex_polynomial_zero_definable D.f).compl using 1
  ext x
  simp [PrimeSpectrum.BasicConstructibleSetData.toSet, PrimeSpectrum.mem_zeroLocus,
    complexTupleSpectrumPoint, Set.range_subset_iff, RingHom.mem_ker]

theorem complex_constructible_domain_definable {n : ℕ}
    (Z : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))) (hZ : IsConstructible Z) :
    (Set.univ : Set ℂ).Definable Language.ring {x | complexTupleSpectrumPoint x ∈ Z} := by
  obtain ⟨S, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hZ
  have h := Set.definable_iUnion_of_finite (fun d : S => complex_basic_constructible_domain_definable d.val)
  convert h using 1
  ext x
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨fun ⟨d, hd, hx⟩ => ⟨⟨d, hd⟩, hx⟩, fun ⟨d, hx⟩ => ⟨d.val, d.property, hx⟩⟩

end DiamondIntegral.Section5
