import «section 2».ProjectiveSeparation
import «section 2».FibreClosures

/-! The fibre-graph recovery step in Proposition 2.55, in the actual
projective valuation topology. Hausdorff separation is proved here rather
than imposed as an additional topological hypothesis. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuous_finiteProjectiveTuple :
    Continuous (finiteProjectiveTuple (M := M) (n := m)) :=
  (IsOpenEmbedding.piMap (fun _ => ProjectiveLine.isOpenEmbedding_finite)).continuous

theorem projectiveFibreClosure_graph_inter {I : Type*}
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (I × (Fin n → VF M))) (f : I → (Fin n → VF M) → Fin m → VF M)
    (hf : ∀ a : I, ContinuousOn (f a) {x | (a,x) ∈ A}) :
    fibreClosure (fibreGraph A (fun a x => finiteProjectiveTuple (f a x))) ∩
      {p : I × ((Fin n → VF M) × (Fin m → ProjectiveLine (VF M))) | (p.1,p.2.1) ∈ A} =
        fibreGraph A (fun a x => finiteProjectiveTuple (f a x)) := by
  letI := projectiveProduct_t2Space hv m
  apply fibreClosure_graph_inter
  intro a
  exact continuous_finiteProjectiveTuple.comp (continuousOn_iff_continuous_domRestrict.mp (hf a))

end DiamondIntegral.Section2
