import «section 6».RVIndexedUpperRays

/-! Uniform eventual Gamma properties over a bounded RV base. Taking
the full upper tail is a first-order construction, so pointwise eventual
properties give one original-base named cutoff without selecting fiber
cutoffs or enlarging the base by RV parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

def gammaUpperTail (P : Set (Gamma M)) : Set (Gamma M) :=
  {γ | ∀ δ, γ ≤ δ → δ ∈ P}

theorem gammaUpperTail_graph_definable
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P)) :
    S.Definable LRV (rawGammaFamilyGraph D (fun x => gammaUpperTail (P x))) := by
  have hNZ := (GammaParameters.nonzero_rv_definable S).preimage_comp
    (fun _ : Fin 1 => (Sum.inr 0 : Fin n ⊕ Fin 1))
  have hDom := (hD.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin 1)).inter hNZ
  have hBad : S.Definable LRV (rawGammaFamilyGraph D (fun x => (P x)ᶜ)) := by
    convert hDom.inter hP.compl using 1
    ext z
    simp only [rawGammaFamilyGraph,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,
      Set.mem_compl_iff,Function.comp_apply]
    tauto
  have hCompare : S.Definable₂ LRV {p : M × M | ¬ iLe p.2 p.1} := by
    change S.Definable LRV {z : Fin 2 → M | ¬ iLe (z 1) (z 0)}
    convert ((GammaParameters.raw_le_definable S).preimage_comp (![1,0] : Fin 2 → Fin 2)).compl using 1
    ext z
    rfl
  have hAll := rawFibreForallCompare_definable S _ hBad (fun v u => ¬ iLe u v) hCompare
  convert hDom.inter hAll using 1
  ext z
  constructor
  · rintro ⟨hzD,hzNZ,hTail⟩
    refine ⟨⟨hzD,hzNZ⟩,fun t ht hle => ?_⟩
    have hΓ := (GammaParameters.original_le_codeValue_iff _ _ hzNZ ht.2.1).mp hle
    exact ht.2.2 (hTail _ hΓ)
  · rintro ⟨⟨hzD,hzNZ⟩,hAll⟩
    refine ⟨hzD,hzNZ,fun δ hδ => ?_⟩
    by_contra hn
    obtain ⟨t,ht,htδ⟩ := GammaParameters.EndpointLogic.codeValue_surjective δ
    have hBadMem : Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => t) ∈
        rawGammaFamilyGraph D (fun x => (P x)ᶜ) := ⟨hzD,ht,htδ.symm ▸ hn⟩
    apply hAll t hBadMem
    exact (GammaParameters.original_le_codeValue_iff _ _ hzNZ ht).mpr (htδ.symm ▸ hδ)

theorem rv_indexed_eventual_gamma_named_threshold
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (hNZ : ∀ x ∈ D, ∀ i, GammaParameters.NonzeroRV (x i)) (hDB : RVCodeDoublyBounded D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hEventual : ∀ x ∈ D, ∃ γ, ∀ δ, γ ≤ δ → δ ∈ P x) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      1 ≤ δ ∧ ∀ x ∈ D, ∀ γ, δ < γ → γ ∈ P x := by
  obtain ⟨δ,hδ,hδ1,hGood⟩ := rv_indexed_nonempty_upper_rays_named_threshold hc h00 linear hκ hs hsmall hΓ
    D hD hNZ hDB (fun x => gammaUpperTail (P x)) (gammaUpperTail_graph_definable D hD P hP)
    (fun x hx => hEventual x hx)
    (fun _ _ a ha b hab c hbc => ha c (hab.trans hbc))
  exact ⟨δ,hδ,hδ1,fun x hx γ hγ => hGood x hx γ hγ γ le_rfl⟩

end DiamondIntegral.Section6
