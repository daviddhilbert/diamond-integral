import «section 4».GammaUniformCuts
import «section 4».EulerCutCellValues
import «section 4».GammaEulerSets

/-! Euler values of unary fibres with arbitrarily many Gamma parameters.
Uniform cut bounds give a fixed finite range. Each cut formula has weights
independent of its endpoints, which will also give original-base level-set
definability. No higher-dimensional Fubini theorem is a premise. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFamilyEuler
open GammaOrderLogic GammaDefinableEuler GammaEulerSets EulerFunction GammaUniformCuts

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def fibreEuler (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (y : Fin n → Values.Gamma (M := M)) : ℤ :=
  eulerValue h00 (GammaBaseExtension.withGamma B (Set.range y)) k {x | Fin.cons x y ∈ R}
    (GammaFamilySlices.slice_definable_base B R hR y)

theorem fibreEuler_cutSum (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n N : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (y : Fin n → Values.Gamma (M := M)) (a : Fin N → Values.Gamma (M := M))
    (ha : Controls a {x | Fin.cons x y ∈ R}) :
    fibreEuler h00 B k R hR y =
      ∑ σ : Fin N → Fin 3,
        if ∃ x, Fin.cons x y ∈ R ∧ ∀ i, cutCode (a i) x = σ i then cutPatternValue k σ else 0 := by
  let B' := GammaBaseExtension.withGamma B (Set.range y)
  let D : Set (Values.Gamma (M := M)) := {x | Fin.cons x y ∈ R}
  have hD : GammaDefinableOverBase B' D := GammaFamilySlices.slice_definable_base B R hR y
  let f := indicator h00 B' k D hD
  let A : Set (PaperGamma (M := M)) := {x | toPaperGamma.symm x ∈ D}
  have hf (x : PaperGamma (M := M)) : f x = if x ∈ A then 1 else 0 := by
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    by_cases hγ : γ ∈ D <;> simp only [f, indicator_eval, A, Set.mem_ofPred_eq,
      Equiv.symm_apply_apply, hγ, ite_true, ite_false]
  have hc : CutDetermined (fun i => toPaperGamma (a i)) f := by
    intro x x' hcut
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    obtain ⟨δ, rfl⟩ := toPaperGamma.surjective x'
    have hmem : γ ∈ D ↔ δ ∈ D := ha γ δ
      (fun i => (cutCode_eq_iff (toPaperGamma (a i)) (toPaperGamma γ) (toPaperGamma δ)).mp (hcut i))
    change indicator h00 B' k D hD (toPaperGamma γ) = indicator h00 B' k D hD (toPaperGamma δ)
    rw [indicator_eval, indicator_eval]
    by_cases hγ : γ ∈ D
    · simp only [hγ, hmem.mp hγ, ite_true]
    · have hδ : δ ∉ D := fun h => hγ (hmem.mpr h)
      simp only [hγ, hδ, ite_false]
  have h := totalEuler_cut_indicator k (fun i => toPaperGamma (a i)) A f hf hc
  change totalEuler k f = _
  rw [h, cutEulerSum]
  apply Finset.sum_congr rfl
  intro σ _
  have he : (∃ x ∈ A, ∀ i, cutCode (toPaperGamma (a i)) x = σ i) ↔
      ∃ x, Fin.cons x y ∈ R ∧ ∀ i, cutCode (a i) x = σ i := by
    constructor
    · rintro ⟨x, hx, hcut⟩
      obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
      exact ⟨γ, hx, hcut⟩
    · rintro ⟨γ, hx, hcut⟩
      exact ⟨toPaperGamma γ, hx, hcut⟩
  simp only [he]

theorem fibreEuler_finite_range (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    (Set.range (fibreEuler h00 B k R hR)).Finite := by
  obtain ⟨N, hN⟩ := uniform_cutBound h00 hκ hs B hr hγ R hR
  apply (possibleCutEulerValues_finite k N).subset
  rintro z ⟨y, rfl⟩
  obtain ⟨a, ha⟩ := hN y
  rw [fibreEuler_cutSum h00 B k R hR y a ha]
  refine ⟨(fun σ => decide (∃ x, Fin.cons x y ∈ R ∧ ∀ i, cutCode (a i) x = σ i)), ?_⟩
  simp only [decide_eq_true_eq]

end DiamondIntegral.Section4.GammaFamilyEuler
