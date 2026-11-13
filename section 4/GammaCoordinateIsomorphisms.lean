import «section 4».GammaOrdinaryCharts
import «section 4».RVCoordinateMaps

/-! Coordinate permutations lift on the complete proper RV preimage over
the original base. No representative section is chosen. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCoordinateIsomorphisms
open GammaRVChartPresentation GammaOrdinaryCharts GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ordinary {B : Base (M := M)} {n : ℕ} (a b : Chart B n)
    (e : Fin n ≃ Fin n)
    (hb : Set.BijOn (fun γ => γ ∘ e) a.support b.support) : Iso a b where
  map γ := γ ∘ e
  graph_definable := GammaTupleMaps.graph_definable B a.support a.support_definable _
    (fun i => projection_definable B (e i))
  bijective := hb
  lift z := z ∘ e
  lift_definable := by
    have h := RVCoordinateMaps.coordinate_graph_definable B _ (sharp_definable _ a.support_definable) e
    convert h using 1
    ext w
    exact and_congr_right (fun _ => eq_comm)
  lift_bijective := by
    refine ⟨?_, e.surjective.injective_comp_right.injOn, ?_⟩
    · intro z hz
      exact ⟨fun i => hz.1 (e i), hb.mapsTo hz.2⟩
    · intro z hz
      have he : (z ∘ e.symm) ∘ e = z := by funext i; simp
      refine ⟨z ∘ e.symm, ⟨fun i => hz.1 (e.symm i), ?_⟩, he⟩
      obtain ⟨γ, hγ, hγz⟩ := hb.surjOn hz.2
      have ht : codeValues (z ∘ e.symm) = γ := by
        funext i
        have hi := congrFun hγz (e.symm i)
        simpa only [codeValues, Function.comp_apply, Equiv.apply_symm_apply] using hi.symm
      exact ht ▸ hγ
  contraction := fun _ _ => rfl

end DiamondIntegral.Section4.GammaCoordinateIsomorphisms
