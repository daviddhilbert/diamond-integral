import «section 4».GammaDefinableMaps
import «section 4».GammaUnaryBijections
import «section 2».RVGammaBounds

/-! Connect the proved 2.41 bounded-image theorem to actual Gamma tuples.
Every RV representative remains in the raw graph. The canonical-structure
hypothesis required by the reused 2.41 theorem is explicit. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedMapImage
open GammaOrderLogic GammaDefinableMaps GammaBaseExtension

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem bounded_map_image (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {n : ℕ}
    (D : Set (Fin n → Values.Gamma (M := M))) (hD : GammaDefinable B D)
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hT : MapDefinable B T)
    (hbound : ∃ β : Values.Gamma (M := M), ∀ u ∈ D, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β) :
    ∃ γ : Values.Gamma (M := M), ∀ u ∈ D, γ⁻¹ ≤ T u ∧ T u ≤ γ := by
  let S := commonRealNames B
  let E : Set (Fin n → M) := {x | Proper x ∧ (fun i => codeValue (M := M) (x i)) ∈ D}
  let f : (Fin n → M) → Values.Gamma (M := M) := fun x => T (fun i => codeValue (M := M) (x i))
  have hE : S.Definable LRV E := DefinableOver.raw_definable (DefinableOverBase.common_names hD)
  have hDtail := GammaRelationLogic.preimage_definable_base B D hD Fin.succ
  have hfull := GammaRelationLogic.inter_definable_base B _ _ hT hDtail
  have hraw := DefinableOver.raw_definable (DefinableOverBase.common_names hfull)
  let π : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.cases (.inr 0) Sum.inl
  have hf : S.Definable LRV (Section2.rawGammaFamilyGraph E (fun x => {f x})) := by
    convert hraw.preimage_comp π using 1
    ext z
    change ((Proper (z ∘ Sum.inl) ∧ (fun i => codeValue (M := M) (z (.inl i))) ∈ D) ∧
      NonzeroRV (z (.inr 0)) ∧ codeValue (M := M) (z (.inr 0)) =
        T (fun i => codeValue (M := M) (z (.inl i)))) ↔
      Proper (z ∘ π) ∧ (codeValue (M := M) (z (.inr 0)) =
        T (fun i => codeValue (M := M) (z (.inl i))) ∧
          (fun i => codeValue (M := M) (z (.inl i))) ∈ D)
    constructor
    · rintro ⟨⟨hz, hd⟩, ho, he⟩
      exact ⟨(fun i => Fin.cases ho (fun j => hz j) i), he, hd⟩
    · rintro ⟨hz, he, hd⟩
      exact ⟨⟨(fun i => hz i.succ), hd⟩, hz 0, he⟩
  have hEb : Section2.RVCodeDoublyBounded E := by
    obtain ⟨β, hβ⟩ := hbound
    exact ⟨β, fun x hx i => hβ _ hx.2 i⟩
  obtain ⟨γ, hγout⟩ := Section2.lemma_2_41_gamma_raw hc h00 linear hκ hs S
    (commonRealNames_small hκ B hr hγ) (GammaUnaryBijections.nontrivial_commonBase B hΓ)
    E hE (fun _ hx => hx.1) f hf hEb
  refine ⟨γ, ?_⟩
  intro u hu
  choose t ht htu using (fun i : Fin n => EndpointLogic.codeValue_surjective (u i))
  have he : (fun i => codeValue (M := M) (t i)) = u := funext htu
  have hmem : t ∈ E := ⟨ht, he.symm ▸ hu⟩
  have h := hγout t hmem
  change γ⁻¹ ≤ T (fun i => codeValue (M := M) (t i)) ∧ T (fun i => codeValue (M := M) (t i)) ≤ γ at h
  rwa [he] at h

end DiamondIntegral.Section4.GammaBoundedMapImage
