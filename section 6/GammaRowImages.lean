import «section 6».RefinedCentripetalGluing

/-! Full Gamma-code image of a row family, and descent of a bounded
union to one original-base named bound. Empty unions are included. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

def gammaRowUnion (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M)) : Set (Gamma M) :=
  {a | ∃ x ∈ D, a ∈ P x}

theorem rawGammaFamilyGraph_image_codes (D : Set (Fin n → M))
    (P : (Fin n → M) → Set (Gamma M)) :
    (fun z => z ∘ (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)) '' rawGammaFamilyGraph D P =
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback (gammaRowUnion D P)} := by
  ext z
  constructor
  · rintro ⟨w,⟨hwD,hwNZ,hwP⟩,hwz⟩
    have h0 : w (.inr 0) = z 0 := congrFun hwz 0
    change z 0 ∈ Values.gammaPullback (gammaRowUnion D P)
    rw [← h0]
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hwNZ).mpr ⟨w ∘ Sum.inl,hwD,hwP⟩
  · intro hz
    let ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    obtain ⟨x,hx,hP⟩ := (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz
    exact ⟨Sum.elim x z,⟨hx,ht,hP⟩,rfl⟩

theorem bounded_gamma_rows_named_bound
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M))
    (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hBound : ∃ γ : Gamma M, ∀ x ∈ D, ∀ a ∈ P x, γ⁻¹ ≤ a ∧ a ≤ γ) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ x ∈ D, ∀ a ∈ P x, δ⁻¹ ≤ a ∧ a ≤ δ := by
  let Q (x : Fin n → M) := gammaAbs '' P x
  let U := gammaRowUnion D Q
  have hQ := rawGammaFamilyGraph_abs_definable hc S D P hP
  have hU : GammaParameters.GammaDefinableOverBase (⟨S,∅⟩ : ParameterBase M) U := by
    apply (gamma_real_codes_iff hc S U).mpr
    rw [← rawGammaFamilyGraph_image_codes D Q]
    exact hQ.image_comp Sum.inr
  obtain ⟨γ,hγ⟩ := hBound
  have hUb : BddAbove U := by
    refine ⟨γ,?_⟩
    rintro a ⟨x,hx,b,hb,rfl⟩
    exact (gammaAbs_le_iff b γ).mpr (hγ x hx b hb)
  by_cases hne : U.Nonempty
  · obtain ⟨δ,hδ,hδdef⟩ := gamma_definable_supremum h00 _ U hU hne hUb
    refine ⟨δ,(gamma_real_codes_iff hc S _).mp hδdef,fun x hx a ha => (gammaAbs_le_iff a δ).mp ?_⟩
    exact hδ.1 ⟨x,hx,a,ha,rfl⟩
  · refine ⟨1,?_,?_⟩
    · exact (gamma_real_codes_iff hc S _).mp
        (GammaParameters.real_definableAtBase (⟨S,∅⟩ : ParameterBase M) .rv _ (GammaSyntax.one_definable S))
    · intro x hx a ha
      exact False.elim (hne ⟨gammaAbs a,x,hx,a,ha,rfl⟩)

end DiamondIntegral.Section6
