import «section 2».RVGammaBounds
import «section 2».GammaEndpointBounds

/-! Uniform bounds for RV-indexed bounded Gamma sets. The supremum of
absolute values has a full graph over the original base, and 2.41 bounds
this function. No definable selection of fibre bounds is a premise. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem rv_indexed_gamma_family_bounded
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (hNZ : ∀ x ∈ D, ∀ i, GammaParameters.NonzeroRV (x i))
    (P : (Fin n → M) → Set (Gamma M))
    (hP : S.Definable LRV (rawGammaFamilyGraph D P)) (hbound : RVCodeDoublyBounded D)
    (hpoint : ∀ x ∈ D, (P x).Nonempty ∧ BddBelow (P x) ∧ BddAbove (P x)) :
    ∃ γ : Gamma M, ∀ x ∈ D, ∀ a ∈ P x, γ⁻¹ ≤ a ∧ a ≤ γ := by
  have hAbs := rawGammaFamilyGraph_abs_definable hc S D P hP
  have hsup (x : Fin n → M) (hx : x ∈ D) : ∃ c : Gamma M, IsLUB (gammaAbs '' P x) c := by
    obtain ⟨hne,hl,hu⟩ := hpoint x hx
    obtain ⟨c,hcBound⟩ := (gamma_symmetric_bound_iff (P x)).mpr ⟨hu,hl⟩
    have hbounded : BddAbove (gammaAbs '' P x) := by
      refine ⟨c,?_⟩
      rintro _ ⟨a,ha,rfl⟩
      exact (gammaAbs_le_iff a c).mpr (hcBound a ha)
    exact rawGammaFamilyGraph_exists_lub hc h00 S D (fun x => gammaAbs '' P x) hAbs x hx
      (hne.image _) hbounded
  obtain ⟨g,hg,hgLUB⟩ := uniform_gamma_supremum S D hD (fun x => gammaAbs '' P x) hAbs hsup
  obtain ⟨γ,hγ⟩ := lemma_2_41_gamma_raw hc h00 linear hκ hs S hsmall hΓ D hD hNZ g hg hbound
  refine ⟨γ,fun x hx a ha => ?_⟩
  exact (gammaAbs_le_iff a γ).mp (((hgLUB x hx).1 ⟨a,ha,rfl⟩).trans (hγ x hx).2)

end DiamondIntegral.Section2
