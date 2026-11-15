import Section7.FieldConstructibility
import Section4.ResidueMultivariateFunctions

/-! The reverse constructibility adapter, over the displayed coefficient
field. It uses finite polynomial equations and inequations, not an added
purity or descent input. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language Topology
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {K : Type} [Field K] (E : Subfield K) {n : ℕ}

theorem basic_constructible_field_definable
    (D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n) E)) :
    (E : Set K).Definable Language.ring {x | fieldTuplePrime E x ∈ D.toSet} := by
  have hg : (E : Set K).Definable Language.ring
      {x : Fin n → K | ∀ i, (D.g i).eval₂ E.subtype x = 0} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i => mvPolynomial_zeroSet_definable E (D.g i))
  convert hg.inter (mvPolynomial_zeroSet_definable E D.f).compl using 1
  ext x
  simp [PrimeSpectrum.BasicConstructibleSetData.toSet, PrimeSpectrum.mem_zeroLocus,
    fieldTuplePrime, Set.range_subset_iff, RingHom.mem_ker]

theorem constructible_field_definable
    (C : Set (PrimeSpectrum (MvPolynomial (Fin n) E))) (hC : IsConstructible C) :
    (E : Set K).Definable Language.ring {x | fieldTuplePrime E x ∈ C} := by
  obtain ⟨S, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hC
  have h := Set.definable_iUnion_of_finite
    (fun d : S => basic_constructible_field_definable E d.val)
  convert h using 1
  ext x
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨fun ⟨d, hd, hx⟩ => ⟨⟨d, hd⟩, hx⟩, fun ⟨d, hx⟩ => ⟨d.val, d.property, hx⟩⟩

end DiamondIntegral.Section5
