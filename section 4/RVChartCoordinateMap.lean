import «section 4».RVResidueChartCodes
import Section4.RVDimensionRank

/-! The coordinate map retained by an RV chart is an actual finite-to-one
map over its real names, hence bounds the domain's RV dimension. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section4.RVChartCoordinateMap
open RVMeasuredCharts RVResidueChartCodes FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def coordinateMap {B : Base (M := M)} {k : ℕ} (a : Chart B k) :
    Map (typedSet a) (DefSet.univ (rawRVSpace (M := M) k) (commonRealNames B)) where
  toFun u := ⟨fun i => ⟨a.coordinate (rvValues u.val) i,
    (a.coordinate_proper (rvValues u.val) u.property i).1⟩, Set.mem_univ _⟩
  graph_definable := by
    let π : Fin (k + a.arity) → (Fin a.arity ⊕ Fin k) := join k a.arity Sum.inl Sum.inr
    have h := a.coordinate_definable.common_names.raw_definable.preimage_comp
      π
    change (commonRealNames B).Definable LRV (α := Fin a.arity ⊕ Fin k) _
    convert h using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have hh : (z ∘ π) ∘ headIndex k a.arity = z ∘ Sum.inl := by
      funext i
      exact congrArg z (join_head k a.arity Sum.inl Sum.inr i)
    have ht : (z ∘ π) ∘ tailIndex k a.arity = z ∘ Sum.inr := by
      funext i
      exact congrArg z (join_tail k a.arity Sum.inl Sum.inr i)
    constructor
    · rintro ⟨hu, hv, u, he, hf⟩
      have hx : rvValues u.val = z ∘ Sum.inl := by
        rw [he, rvValues_decode]
      have hy : rvValues (fun i => (⟨a.coordinate (rvValues u.val) i,
        (a.coordinate_proper (rvValues u.val) u.property i).1⟩ : CanonicalRV.RVSort M)) =
          z ∘ Sum.inr := by
        rw [hf, rvValues_decode]
      change (z ∘ π) ∘ headIndex k a.arity ∈ a.domain ∧
        a.coordinate ((z ∘ π) ∘ headIndex k a.arity) = (z ∘ π) ∘ tailIndex k a.arity
      rw [hh, ht]
      exact ⟨hx ▸ u.property, hx ▸ hy⟩
    · intro hz
      change (z ∘ π) ∘ headIndex k a.arity ∈ a.domain ∧
        a.coordinate ((z ∘ π) ∘ headIndex k a.arity) = (z ∘ π) ∘ tailIndex k a.arity at hz
      rw [hh, ht] at hz
      have hu : z ∘ Sum.inl ∈ (rawRVSpace (M := M) a.arity).domain :=
        ⟨fun i => ⟨z (.inl i), a.domain_definable.proper _ hz.1 i⟩, rfl⟩
      have hv : z ∘ Sum.inr ∈ (rawRVSpace (M := M) k).domain := by
        refine ⟨fun i => ⟨z (.inr i), ?_⟩, rfl⟩
        exact (congrArg iRV (congrFun hz.2 i)).mp (a.coordinate_proper _ hz.1 i).1
      let u : typedSet a := ⟨(rawRVSpace a.arity).decode ⟨z ∘ Sum.inl, hu⟩, by
        change rvValues ((rawRVSpace a.arity).decode ⟨z ∘ Sum.inl, hu⟩) ∈ a.domain
        rw [rvValues_decode]
        exact hz.1⟩
      refine ⟨hu, hv, u, rfl, ?_⟩
      apply rvValues_injective
      change a.coordinate (rvValues u.val) = rvValues ((rawRVSpace k).decode ⟨z ∘ Sum.inr, hv⟩)
      simp only [u, rvValues_decode]
      exact hz.2

theorem coordinateMap_finite {B : Base (M := M)} {k : ℕ} (a : Chart B k) :
    (coordinateMap a).FiniteFibres := by
  intro t
  have hinj : Function.Injective (fun u : typedSet a => rvValues u.val) :=
    fun _ _ h => Subtype.ext (rvValues_injective h)
  apply ((a.finite_fibres (rvValues t.val)).preimage hinj.injOn).subset
  intro u hu
  refine ⟨u.property, ?_⟩
  exact congrArg (fun t : DefSet.univ (rawRVSpace (M := M) k) (commonRealNames B) =>
    rvValues t.val) hu

theorem dimension_le {B : Base (M := M)} {k : ℕ} (a : Chart B k) :
    rvDim (typedSet a) ≤ k :=
  (rvDim_le_iff (typedSet a) k).mpr ⟨k, le_rfl, coordinateMap a, coordinateMap_finite a⟩

end DiamondIntegral.Section4.RVChartCoordinateMap
