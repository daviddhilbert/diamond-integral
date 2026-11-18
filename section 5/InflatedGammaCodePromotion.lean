import «section 5».InflatedGammaFamilyRows

/-! Promotion of adjoined Gamma names to free Gamma parameters.

A set definable over the base with a Gamma tuple `γ` adjoined is the row at
`γ` of a family over `Γ^n` definable over the original base. The family is a
set of actual Gamma tuples; its definability is that of its complete RV code
preimage, so its rows never depend on a chosen code of the parameter. Names
already in the base are kept as names, and only the names in the range of `γ`
become variables; the base need not contain any Gamma name. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- Reindex Gamma names: the old name tuple is assembled from the new
parameter tuple and the retained names, coordinate by coordinate. -/
def inflatedGammaNameMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) {n k k' : ℕ}
    (sel : Fin k → Fin n ⊕ Fin k') (Q : Space LRV M) :
    Map (DefSet.univ (((volumeGammaSpace hc).power (Fin k')).prod ((inflatedGammaPower hc n).prod Q)) S)
      (DefSet.univ (((volumeGammaSpace hc).power (Fin k)).prod Q) S) := by
  let τ : (Fin k × (volumeGammaSpace hc).Index) ⊕ Q.Index →
      (Fin k' × (volumeGammaSpace hc).Index) ⊕ ((Fin n × (volumeGammaSpace hc).Index) ⊕ Q.Index) :=
    Sum.elim (fun io => Sum.elim (fun j => Sum.inr (Sum.inl (j, io.2))) (fun l => Sum.inl (l, io.2)) (sel io.1))
      (fun q => Sum.inr (Sum.inr q))
  have key : ∀ x y : (volumeGammaSpace hc).domain, x.val = y.val →
      (volumeGammaSpace hc).decode x = (volumeGammaSpace hc).decode y :=
    fun x y h => congrArg _ (Subtype.ext h)
  have hdom (c : (((volumeGammaSpace hc).power (Fin k')).prod ((inflatedGammaPower hc n).prod Q)).domain) :
      c.val ∘ τ ∈ (((volumeGammaSpace hc).power (Fin k)).prod Q).domain := by
    refine ⟨fun i => ?_, c.property.2.2⟩
    rcases h : sel i with j | l
    · have hc' := c.property.2.1 j
      convert hc' using 1
      funext o
      simp only [τ, Function.comp_apply, Sum.elim_inl, h]
    · have hc' := c.property.1 l
      convert hc' using 1
      funext o
      simp only [τ, Function.comp_apply, Sum.elim_inl, Sum.elim_inr, h]
  refine Map.ofCodes _ (fun w => (fun i => Sum.elim w.2.1 w.1 (sel i), w.2.2)) (fun z => z ∘ τ)
    (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply Prod.ext
  · funext i
    change (volumeGammaSpace hc).decode _ = Sum.elim _ _ (sel i)
    rcases h : sel i with j | l
    · apply key
      funext o
      simp only [τ, Function.comp_apply, Sum.elim_inl, h]
    · apply key
      funext o
      simp only [τ, Function.comp_apply, Sum.elim_inl, Sum.elim_inr, h]
  · rfl

@[simp] theorem inflatedGammaNameMap_value (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M)
    {n k k' : ℕ} (sel : Fin k → Fin n ⊕ Fin k') (Q : Space LRV M)
    (w : DefSet.univ (((volumeGammaSpace hc).power (Fin k')).prod ((inflatedGammaPower hc n).prod Q)) S) :
    (inflatedGammaNameMap hc S sel Q w).val = (fun i => Sum.elim w.val.2.1 w.val.1 (sel i), w.val.2.2) := rfl

/-- Adjoined Gamma names become free Gamma variables over the original base. -/
theorem gammaGroundDefinable_abstract_gamma_names {n : ℕ} (γ : Fin n → Values.Gamma (M := M))
    {Q : Space LRV M} {W : Set Q.Carrier}
    (hW : GammaGroundDefinable hc (adjoinGammaTuple B γ) Q W) :
    ∃ S : Set ((inflatedGammaPower hc n).prod Q).Carrier,
      GammaGroundDefinable hc B ((inflatedGammaPower hc n).prod Q) S ∧ ∀ x, (γ, x) ∈ S ↔ x ∈ W := by
  obtain ⟨k, δ, hδ, R, hR, hr⟩ := hW
  let J := {i : Fin k // δ i ∈ B.gamma}
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let ε : Fin (Fintype.card J) → Values.Gamma (M := M) := fun l => δ (e.symm l).val
  have hε : ∀ l, ε l ∈ B.gamma := fun l => (e.symm l).property
  have hrange : ∀ i, δ i ∉ B.gamma → ∃ j, γ j = δ i := fun i h => (hδ i).resolve_left h
  let sel : Fin k → Fin n ⊕ Fin (Fintype.card J) := fun i =>
    if h : δ i ∈ B.gamma then Sum.inr (e ⟨i, h⟩) else Sum.inl (Classical.choose (hrange i h))
  have hsel : (fun i => Sum.elim γ ε (sel i)) = δ := by
    funext i
    by_cases h : δ i ∈ B.gamma
    · simp only [sel, h, ↓reduceDIte, Sum.elim_inr, ε, Equiv.symm_apply_apply]
    · simp only [sel, h, ↓reduceDIte, Sum.elim_inl]
      exact Classical.choose_spec (hrange i h)
  let Φ := inflatedGammaNameMap hc B.real sel Q
  let S : Set ((inflatedGammaPower hc n).prod Q).Carrier :=
    {z | ((fun i => Sum.elim z.1 ε (sel i)), z.2) ∈ R}
  refine ⟨S, ⟨Fintype.card J, ε, hε, ?_⟩, ?_⟩
  · refine ⟨{w | (Φ ⟨w, Set.mem_univ _⟩).val ∈ R}, ?_, fun z => Iff.rfl⟩
    have h := Φ.definable_preimage hR
    convert h using 1
    ext w
    constructor
    · intro hw
      exact ⟨⟨w, Set.mem_univ _⟩, rfl, hw⟩
    · rintro ⟨a, ha, hw⟩
      have he : a = ⟨w, Set.mem_univ _⟩ := Subtype.ext ha
      rw [he] at hw
      exact hw
  · intro x
    change ((fun i => Sum.elim γ ε (sel i)), x) ∈ R ↔ x ∈ W
    rw [hsel]
    exact (hr x).symm

/-- Every set over the base with `γ` adjoined is the row at `γ` of a
Gamma family over the original base. -/
theorem _root_.DiamondIntegral.Section3.GammaGroundDefSet.exists_gamma_family {n : ℕ} (γ : Fin n → Values.Gamma (M := M))
    {Q : Space LRV M} (W : GammaGroundDefSet hc (adjoinGammaTuple B γ) Q) :
    ∃ U : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod Q),
      ∀ x, (γ, x) ∈ U.carrier ↔ x ∈ W.carrier := by
  obtain ⟨S, hS, hSW⟩ := gammaGroundDefinable_abstract_gamma_names γ W.definable
  exact ⟨⟨S, hS⟩, hSW⟩

end DiamondIntegral.Section5
