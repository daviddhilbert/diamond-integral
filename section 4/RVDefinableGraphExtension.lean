import «section 4».RVGraphComposition
import «section 4».RVCoordinateMaps
import «section 4».RVVolumeMaps

/-! Adjoining a definable RV function as an extra raw coordinate keeps
the object degree and gives an actual measured isomorphism by projection.
The coordinate map and volume form are transported from the source; the
new raw coordinate contributes no spurious Jacobian or object degree. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVDefinableGraphExtension
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def domain {B : Base (M := M)} {k : ℕ} (r : Chart B k)
    (f : (Fin r.arity → M) → M) : Set (Fin (1 + r.arity) → M) := graphOn r.domain (fun u => ![f u])

def chart {B : Base (M := M)} {k : ℕ} (r : Chart B k) (f : (Fin r.arity → M) → M)
    (hf : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv) (domain r f)) : Chart B k where
  arity := 1 + r.arity
  domain := domain r f
  domain_definable := hf
  coordinate := fun u => r.coordinate (u ∘ headIndex 1 r.arity)
  coordinate_definable := RVGraphComposition.graph_compose_definable B (domain r f) r.domain
    (fun u => u ∘ headIndex 1 r.arity) r.coordinate
    (RVCoordinateMaps.coordinate_graph_definable B (domain r f) hf (headIndex 1 r.arity))
    r.coordinate_definable (fun _ hu => hu.1)
  coordinate_proper := fun u hu => r.coordinate_proper _ hu.1
  finite_fibres := by
    intro t
    have h := (r.finite_fibres t).image (fun x => join 1 r.arity x ![f x])
    apply h.subset
    intro u hu
    refine ⟨u ∘ headIndex 1 r.arity, ⟨hu.1.1, hu.2⟩, ?_⟩
    have he := join_reconstruct 1 r.arity u
    rw [← hu.1.2] at he
    exact he
  volume := fun u => r.volume (u ∘ headIndex 1 r.arity)
  volume_definable := RVVolumeMaps.reindex_restrict_definable B r.domain (domain r f) hf
    r.volume r.volume_definable (headIndex 1 r.arity) (fun _ hu => hu.1)

theorem projection_bijective {B : Base (M := M)} {k : ℕ} (r : Chart B k)
    (f : (Fin r.arity → M) → M) :
    Set.BijOn (fun u => u ∘ headIndex 1 r.arity) (domain r f) r.domain := by
  refine ⟨fun _ hu => hu.1, ?_, ?_⟩
  · intro u hu v hv he
    have hU := join_reconstruct 1 r.arity u
    have hV := join_reconstruct 1 r.arity v
    rw [← hu.2] at hU
    rw [← hv.2] at hV
    exact hU.symm.trans ((congrArg (fun x => join 1 r.arity x ![f x]) he).trans hV)
  · intro x hx
    refine ⟨join 1 r.arity x ![f x], (graphOn_exists r.domain (fun u => ![f u]) _).mpr ⟨x, hx, rfl⟩, ?_⟩
    exact funext (join_head 1 r.arity x ![f x])

def iso {B : Base (M := M)} {k : ℕ} (r : Chart B k) (f : (Fin r.arity → M) → M)
    (hf : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv) (domain r f)) : Iso (chart r f hf) r :=
  RVCoordinateMaps.coordinateIso (chart r f hf) r (headIndex 1 r.arity)
    (projection_bijective r f) (fun _ _ => rfl)

end DiamondIntegral.Section4.RVDefinableGraphExtension
