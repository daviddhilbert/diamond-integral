import «section 6».GammaRowImages
import «section 2».RVIndexedGammaBounds

/-! The bound postponed until after FMT. Definable nonempty Gamma rows
over a doubly bounded RV base need only be bounded separately; their
union is then bounded. Bounds for the unfrozen VF-indexed family are
neither assumed nor inferred. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

theorem rv_indexed_bounded_gamma_rows_bounded
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (hNZ : ∀ x ∈ D, ∀ i, GammaParameters.NonzeroRV (x i))
    (hDB : RVCodeDoublyBounded D)
    (P : (Fin n → M) → Set (Gamma M))
    (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hne : ∀ x ∈ D, (P x).Nonempty)
    (hRows : ∀ x ∈ D, ∃ γ : Gamma M, ∀ a ∈ P x, γ⁻¹ ≤ a ∧ a ≤ γ) :
    ∃ γ : Gamma M, ∀ x ∈ D, ∀ a ∈ P x, γ⁻¹ ≤ a ∧ a ≤ γ := by
  apply rv_indexed_gamma_family_bounded hc h00 linear hκ hs S hsmall hΓ D hD hNZ P hP hDB
  intro x hx
  obtain ⟨γ,hγ⟩ := hRows x hx
  exact ⟨hne x hx,⟨γ⁻¹,fun a ha => (hγ a ha).1⟩,⟨γ,fun a ha => (hγ a ha).2⟩⟩

theorem gammaRows_with_unit_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P)) :
    S.Definable LRV (rawGammaFamilyGraph D (fun x => insert 1 (P x))) := by
  have hOne : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {(1 : Gamma M)}} :=
    (gamma_real_codes_iff hc S _).mp
      (GammaParameters.real_definableAtBase (⟨S,∅⟩ : ParameterBase M) .rv _ (GammaSyntax.one_definable S))
  have hOneGraph : S.Definable LRV (rawGammaFamilyGraph D (fun _ => {(1 : Gamma M)})) := by
    convert (hD.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin 1)).inter
      (hOne.preimage_comp (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)) using 1
    ext z
    change (z ∘ Sum.inl ∈ D ∧ GammaParameters.NonzeroRV (z (.inr 0)) ∧
      GammaParameters.codeValue (z (.inr 0)) ∈ {(1 : Gamma M)}) ↔
      z ∘ Sum.inl ∈ D ∧ z (.inr 0) ∈ Values.gammaPullback {(1 : Gamma M)}
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨ht,hval⟩
      exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr hval
    · intro hz
      let ht : GammaParameters.NonzeroRV (z (.inr 0)) := ⟨hz.1,hz.2.1⟩
      exact ⟨ht,(GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz⟩
  convert hP.union hOneGraph using 1
  ext z
  simp only [rawGammaFamilyGraph,Set.mem_ofPred_eq,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
  tauto

/-- The complete post-FMT row bound, including empty rows and a named
uniform bound over the original parameter base. -/
theorem rv_indexed_gamma_rows_named_bound
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (hNZ : ∀ x ∈ D, ∀ i, GammaParameters.NonzeroRV (x i)) (hDB : RVCodeDoublyBounded D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hRows : ∀ x ∈ D, ∃ γ : Gamma M, ∀ a ∈ P x, γ⁻¹ ≤ a ∧ a ≤ γ) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ x ∈ D, ∀ a ∈ P x, δ⁻¹ ≤ a ∧ a ≤ δ := by
  let Q (x : Fin n → M) := insert (1 : Gamma M) (P x)
  have hQ := gammaRows_with_unit_definable hc D hD P hP
  have hQrows (x : Fin n → M) (hx : x ∈ D) :
      ∃ γ : Gamma M, ∀ a ∈ Q x, γ⁻¹ ≤ a ∧ a ≤ γ := by
    obtain ⟨γ,hγ⟩ := hRows x hx
    refine ⟨max γ 1,fun a ha => ?_⟩
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨by simpa only [inv_one] using inv_le_inv' (le_max_right γ (1 : Gamma M)),le_max_right _ _⟩
    · exact ⟨(inv_le_inv' (le_max_left γ (1 : Gamma M))).trans (hγ a ha).1,
        (hγ a ha).2.trans (le_max_left _ _)⟩
  obtain ⟨γ,hγ⟩ := rv_indexed_bounded_gamma_rows_bounded hc h00 linear hκ hs hsmall hΓ D hD hNZ hDB Q hQ
    (fun _ _ => ⟨1,Set.mem_insert _ _⟩) hQrows
  apply bounded_gamma_rows_named_bound hc h00 D P hP
  exact ⟨γ,fun x hx a ha => hγ x hx a (Set.mem_insert_of_mem 1 ha)⟩

end DiamondIntegral.Section6
