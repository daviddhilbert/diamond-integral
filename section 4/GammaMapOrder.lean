import «section 4».GammaDefinableMaps
import «section 4».GammaQuantifierLogic

/-! Order comparisons and piecewise choices of actual Gamma maps are
definable over the same base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaMapOrder
open GammaOrderLogic GammaDefinableMaps

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem lt_maps_definable (B : Base (M := M)) {n : ℕ}
    (f g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : MapDefinable B f) (hg : MapDefinable B g) : GammaDefinable B {z | f z < g z} := by
  let πf : Fin (n + 1) → Fin (n + 2) := Fin.cases 0 (fun i => i.succ.succ)
  let πg : Fin (n + 1) → Fin (n + 2) := Fin.cases 1 (fun i => i.succ.succ)
  have hF := GammaRelationLogic.preimage_definable_base B _ hf πf
  have hG := GammaRelationLogic.preimage_definable_base B _ hg πg
  have hlt := formula_definable_base B (fun a : Empty => nomatch a) (fun a => nomatch a)
    (.lt (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ)
  have hQ := GammaRelationLogic.exists_definable_base B _
    (GammaRelationLogic.exists_definable_base B _
      (GammaRelationLogic.inter_definable_base B _ _
        (GammaRelationLogic.inter_definable_base B _ _ hF hG) hlt))
  change GammaDefinable B {z : Fin n → Values.Gamma (M := M) |
    ∃ b a, (a = f z ∧ b = g z) ∧ a < b} at hQ
  convert hQ using 1
  ext z
  constructor
  · intro h
    exact ⟨g z, f z, ⟨rfl, rfl⟩, h⟩
  · rintro ⟨b, a, ⟨rfl, rfl⟩, h⟩
    exact h

theorem piecewise_definable (B : Base (M := M)) {n : ℕ}
    (D : Set (Fin n → Values.Gamma (M := M))) (hD : GammaDefinable B D)
    (f g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : MapDefinable B f) (hg : MapDefinable B g) :
    MapDefinable B (fun z => if z ∈ D then f z else g z) := by
  have hd := GammaRelationLogic.preimage_definable_base B D hD Fin.succ
  have hnot := GammaRelationLogic.complement_definable_base B _ hd
  have h := GammaQuantifierLogic.union_definable_base B _ _
    (GammaRelationLogic.inter_definable_base B _ _ hd hf)
    (GammaRelationLogic.inter_definable_base B _ _ hnot hg)
  unfold MapDefinable
  convert h using 1
  ext z
  change (z 0 = if (fun i => z i.succ) ∈ D then f (fun i => z i.succ) else g (fun i => z i.succ)) ↔
    (z ∘ Fin.succ ∈ D ∧ z 0 = f (fun i => z i.succ)) ∨
      (¬z ∘ Fin.succ ∈ D ∧ z 0 = g (fun i => z i.succ))
  have he : z ∘ Fin.succ = (fun i => z i.succ) := by funext i; rfl
  rw [he]
  by_cases hz : (fun i => z i.succ) ∈ D <;> simp [hz]

theorem max_definable (B : Base (M := M)) {n : ℕ}
    (f g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : MapDefinable B f) (hg : MapDefinable B g) : MapDefinable B (fun z => max (f z) (g z)) := by
  have h := piecewise_definable B {z | f z < g z} (lt_maps_definable B f g hf hg) g f hg hf
  convert h using 1
  funext z
  by_cases hz : f z < g z
  · simp [hz, max_eq_right hz.le]
  · simp [hz, max_eq_left (le_of_not_gt hz)]

end DiamondIntegral.Section4.GammaMapOrder
