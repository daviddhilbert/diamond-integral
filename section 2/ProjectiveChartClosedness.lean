import «section 2».ProjectiveTopology

/-! Closedness is local on the two open affine charts of the projective
line. This is the chart-gluing step in Proposition 2.55. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2

theorem isClosed_of_two_open_maps_cover
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Z) (g : Y → Z) (hf : IsOpenMap f) (hg : IsOpenMap g)
    (hcover : ∀ z, (∃ x, f x = z) ∨ ∃ y, g y = z)
    (A : Set Z) (hA : IsClosed (f ⁻¹' A)) (hB : IsClosed (g ⁻¹' A)) : IsClosed A := by
  have he : Aᶜ = f '' (f ⁻¹' A)ᶜ ∪ g '' (g ⁻¹' A)ᶜ := by
    ext z
    constructor
    · intro hz
      rcases hcover z with ⟨x,rfl⟩ | ⟨y,rfl⟩
      · exact Or.inl ⟨x,hz,rfl⟩
      · exact Or.inr ⟨y,hz,rfl⟩
    · rintro (⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩)
      · exact hx
      · exact hy
  apply isOpen_compl_iff.mp
  rw [he]
  exact (hf _ hA.isOpen_compl).union (hg _ hB.isOpen_compl)

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem projective_unary_chart_cover (p : Fin 1 → ProjectiveLine (VF M)) :
    (∃ x, finiteProjectiveTuple x = p) ∨
      ∃ x, projectiveTupleChart (fun _ : Fin 1 => (none : LimitPoint M)) x = p := by
  cases hp : (p 0).point with
  | some a =>
    left
    refine ⟨fun _ : Fin 1 => a,?_⟩
    funext i
    fin_cases i
    change ProjectiveLine.finite a = p 0
    calc
      _ = ProjectiveLine.mk ((p 0).point) := congrArg ProjectiveLine.mk hp.symm
      _ = p 0 := rfl
  | none =>
    right
    refine ⟨(0 : Fin 1 → VF M),?_⟩
    funext i
    fin_cases i
    change ProjectiveLine.reciprocalChart (0 : VF M) = p 0
    calc
      _ = ProjectiveLine.mk none := by simp [ProjectiveLine.reciprocalChart,ProjectiveLine.infinity]
      _ = ProjectiveLine.mk ((p 0).point) := congrArg ProjectiveLine.mk hp.symm
      _ = p 0 := rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem isClosed_projective_unary_of_charts {X : Type*} [TopologicalSpace X]
    (A : Set (X × (Fin 1 → ProjectiveLine (VF M))))
    (hA : IsClosed ((Prod.map id finiteProjectiveTuple) ⁻¹' A))
    (hB : IsClosed ((Prod.map id (projectiveTupleChart (fun _ : Fin 1 => (none : LimitPoint M)))) ⁻¹' A)) :
    IsClosed A := by
  have hf : IsOpenEmbedding (finiteProjectiveTuple (M := M) (n := 1)) :=
    IsOpenEmbedding.piMap (fun _ => ProjectiveLine.isOpenEmbedding_finite)
  apply isClosed_of_two_open_maps_cover _ _ (IsOpenMap.id.prodMap hf.isOpenMap)
    (IsOpenMap.id.prodMap (projectiveTupleChart_isOpenEmbedding (fun _ : Fin 1 => (none : LimitPoint M))).isOpenMap)
    (fun p => ?_) A hA hB
  rcases projective_unary_chart_cover p.2 with ⟨x,hx⟩ | ⟨x,hx⟩
  · exact Or.inl ⟨(p.1,x),Prod.ext rfl hx⟩
  · exact Or.inr ⟨(p.1,x),Prod.ext rfl hx⟩

end DiamondIntegral.Section2
