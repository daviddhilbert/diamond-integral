import «section 6».PrescribedPairedCores

/-! A single original-base named threshold works for all definable
nonempty upper rays indexed by a doubly bounded nonzero RV base.
Apply the checked bounded-row theorem to the positive bad radii; no
choice of a radius in each RV fiber is a definability premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

theorem positiveGammaCodes_definable (hc : CanonicalStructure.IsCanonical (M := M)) :
    S.Definable LRV {z : Fin 1 → M | GammaParameters.NonzeroRV (z 0) ∧
      (1 : Gamma M) ≤ GammaParameters.codeValue (z 0)} := by
  have ho := GammaSyntax.unary_at (GammaSyntax.one_definable (M := M) S)
    (Sum.inr (0 : Fin 1) : Fin 1 ⊕ Fin 1)
  have hl := (GammaSyntax.lt_definable (M := M) S
    (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1) (.inr 0)).not
  have hpos : Values.GammaDefinable S (Set.Ici (1 : Gamma M)) := by
    apply (GammaSyntax.scalar_definable_iff _).mp
    apply ((ho.and hl).exists_block).congr
    intro z
    change (∃ u : Fin 1 → Gamma M, u 0 = 1 ∧ ¬ z 0 < u 0) ↔ 1 ≤ z 0
    constructor
    · rintro ⟨u,hu,hge⟩
      rw [hu] at hge
      exact le_of_not_gt hge
    · intro hz
      exact ⟨fun _ => 1,rfl,not_lt_of_ge hz⟩
  have hraw := (gamma_real_codes_iff hc S _).mp
    (GammaParameters.real_definableAtBase (⟨S,∅⟩ : ParameterBase M) .rv _ hpos)
  convert hraw using 1
  ext z
  constructor
  · rintro ⟨hz,hpos⟩
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hz).mpr hpos
  · intro hz
    let hnz : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    exact ⟨hnz,(GammaParameters.gammaPullback_mem_codeValue_iff _ _ hnz).mp hz⟩

theorem positive_bad_gamma_rows_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P)) :
    S.Definable LRV (rawGammaFamilyGraph D (fun x => {γ | 1 ≤ γ ∧ γ ∉ P x})) := by
  have hpos := (positiveGammaCodes_definable (S := S) hc).preimage_comp
    (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)
  convert ((hD.preimage_comp Sum.inl).inter hpos).inter hP.compl using 1
  ext z
  simp only [rawGammaFamilyGraph,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_compl_iff,
    Set.mem_preimage,Function.comp_apply]
  tauto

theorem rv_indexed_nonempty_upper_rays_named_threshold
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (hNZ : ∀ x ∈ D, ∀ i, GammaParameters.NonzeroRV (x i)) (hDB : RVCodeDoublyBounded D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hne : ∀ x ∈ D, (P x).Nonempty)
    (hup : ∀ x ∈ D, ∀ a ∈ P x, ∀ b, a ≤ b → b ∈ P x) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      1 ≤ δ ∧ ∀ x ∈ D, ∀ γ, δ < γ → γ ∈ P x := by
  let Q (x : Fin n → M) : Set (Gamma M) := {γ | 1 ≤ γ ∧ γ ∉ P x}
  have hQ := positive_bad_gamma_rows_definable hc D hD P hP
  have hRows (x) (hx : x ∈ D) : ∃ r : Gamma M, ∀ a ∈ Q x, r⁻¹ ≤ a ∧ a ≤ r := by
    obtain ⟨r,hr⟩ := hne x hx
    refine ⟨max r 1,fun a ha => ⟨?_,?_⟩⟩
    · exact (inv_le_one'.mpr (le_max_right r 1)).trans ha.1
    · have har : a < r := lt_of_not_ge (fun h => ha.2 (hup x hx r hr a h))
      exact har.le.trans (le_max_left _ _)
  obtain ⟨δ,hδ,hBound⟩ := rv_indexed_gamma_rows_named_bound hc h00 linear hκ hs hsmall hΓ
    D hD hNZ hDB Q hQ hRows
  refine ⟨max δ 1,gamma_max_named δ 1 hδ (gamma_one_named hc),le_max_right _ _,?_⟩
  intro x hx γ hγ
  by_contra hn
  have hγ1 : 1 ≤ γ := ((le_max_right δ 1).trans_lt hγ).le
  have hγδ := (hBound x hx γ ⟨hγ1,hn⟩).2
  exact (not_le_of_gt ((le_max_left δ 1).trans_lt hγ)) hγδ

end DiamondIntegral.Section6
