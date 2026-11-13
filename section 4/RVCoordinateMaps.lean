import «section 4».RVRealProducts

/-! Actual coordinate-map graphs over the original base and measured
isomorphisms induced by coordinate maps that are bijective on the domains
and preserve the corrected weight. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVCoordinateMaps
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks FiniteTupleGraphProduct

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def graphIndices {m n : ℕ} (π : Fin n → Fin m) : Fin (n + m) → Fin m := join n m id π

theorem graphIndices_tuple {m n : ℕ} (π : Fin n → Fin m) (x : Fin m → M) :
    x ∘ graphIndices π = join n m x (x ∘ π) := by
  apply block_ext n m
  · funext i
    simp [graphIndices, Function.comp_apply]
  · funext i
    simp [graphIndices, Function.comp_apply]

theorem coordinate_graph_definable (B : Base (M := M)) {m n : ℕ} (I : Set (Fin m → M))
    (hI : DefinableOverBase B (fun _ : Fin m => .rv) I) (π : Fin n → Fin m) :
    DefinableOverBase B (fun _ : Fin (n + m) => .rv) (graphOn I (fun x => x ∘ π)) := by
  have h : DefinableOverBase B (fun _ : Fin (n + m) => .rv) ((fun x => x ∘ graphIndices π) '' I) :=
    hI.image_real (graphIndices π)
  have he : graphOn I (fun x => x ∘ π) = (fun x => x ∘ graphIndices π) '' I := by
    ext w
    rw [graphOn_exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, graphIndices_tuple π x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, graphIndices_tuple π x⟩
  rw [he]
  exact h

def coordinateIso {B : Base (M := M)} {k : ℕ} (a b : Chart B k) (π : Fin b.arity → Fin a.arity)
    (hbij : Set.BijOn (fun u => u ∘ π) a.domain b.domain)
    (hw : ∀ u ∈ a.domain, a.correctedWeight u = b.correctedWeight (u ∘ π)) : Iso a b where
  equiv := Set.BijOn.equiv (fun u => u ∘ π) hbij
  graph_definable := by
    change DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv)
      {w | ∃ u : a.domain, w = join b.arity a.arity u.val (u.val ∘ π)}
    have he : {w | ∃ u : a.domain, w = join b.arity a.arity u.val (u.val ∘ π)} =
        graphOn a.domain (fun u => u ∘ π) := by
      ext w
      rw [graphOn_exists]
      constructor
      · rintro ⟨u, hu⟩
        exact ⟨u.val, u.property, hu⟩
      · rintro ⟨u, hu, he⟩
        exact ⟨⟨u, hu⟩, he⟩
    rw [he]
    exact coordinate_graph_definable B a.domain a.domain_definable π
  weight_eq := fun u => hw u.val u.property

end DiamondIntegral.Section4.RVCoordinateMaps
