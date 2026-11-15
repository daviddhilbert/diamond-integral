import «section 5».ConstructibleVarietyClasses

/-! Constructible classes satisfy disjoint-union and cut relations in the
geometric ring; no additional constructible scissors are imposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory Topology

theorem Object.Invariant.union {X : Object} {D E : Set X.scheme}
    (hD : X.Invariant D) (hE : X.Invariant E) : X.Invariant (D ∪ E) :=
  fun h x => or_congr (hD h x) (hE h x)

def appendImmersedPresentation {X : Object} {D E : Set X.scheme}
    (c : ImmersedPresentation X D) (d : ImmersedPresentation X E)
    (hDE : Disjoint D E) : ImmersedPresentation X (D ∪ E) := by
  letI := c.finite
  letI := d.finite
  refine {
    index := c.index ⊕ d.index
    finite := inferInstance
    piece := Sum.elim c.piece d.piece
    inclusion := fun j => ?_
    immersion := fun j => ?_
    contained := fun j => ?_
    partition := ?_ }
  · exact Sum.casesOn j c.inclusion d.inclusion
  · cases j with
    | inl i => exact c.immersion i
    | inr i => exact d.immersion i
  · cases j with
    | inl i => exact (c.contained i).trans Set.subset_union_left
    | inr i => exact (d.contained i).trans Set.subset_union_right
  · intro x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i, hi, huniq⟩ := (c.partition x).mp hx
        refine ⟨Sum.inl i, hi, ?_⟩
        intro j hj
        cases j with
        | inl j => exact congrArg Sum.inl (huniq j hj)
        | inr j => exact False.elim (Set.disjoint_left.mp hDE hx (d.contained j hj))
      · obtain ⟨i, hi, huniq⟩ := (d.partition x).mp hx
        refine ⟨Sum.inr i, hi, ?_⟩
        intro j hj
        cases j with
        | inl j => exact False.elim (Set.disjoint_left.mp hDE (c.contained j hj) hx)
        | inr j => exact congrArg Sum.inr (huniq j hj)
    · rintro ⟨j, hj, _⟩
      cases j with
      | inl i => exact Or.inl (c.contained i hj)
      | inr i => exact Or.inr (d.contained i hj)

theorem appendImmersedPresentation_value {X : Object} {D E : Set X.scheme}
    (c : ImmersedPresentation X D) (d : ImmersedPresentation X E) (hDE : Disjoint D E) :
    (appendImmersedPresentation c d hDE).value = c.value + d.value := by
  letI := c.finite
  letI := d.finite
  change (∑ j : c.index ⊕ d.index, objectClass (Sum.elim c.piece d.piece j)) = _
  exact Fintype.sum_sum_type _

theorem constructibleClass_disjoint_union (X : Object) (D E : Set X.scheme)
    (hD : IsConstructible D) (hE : IsConstructible E)
    (hiD : X.Invariant D) (hiE : X.Invariant E) (hDE : Disjoint D E) :
    constructibleClass X (D ∪ E) (hD.union hE) (hiD.union hiE) =
      constructibleClass X D hD hiD + constructibleClass X E hE hiE := by
  let c := Classical.choice (invariant_constructible_immersed_presentation X D hD hiD)
  let d := Classical.choice (invariant_constructible_immersed_presentation X E hE hiE)
  rw [constructibleClass_eq_presentation _ _ _ _ (appendImmersedPresentation c d hDE),
    appendImmersedPresentation_value]
  rfl

theorem constructibleClass_scissor (X : Object) (D E : Set X.scheme)
    (hD : IsConstructible D) (hE : IsConstructible E)
    (hiD : X.Invariant D) (hiE : X.Invariant E) :
    constructibleClass X D hD hiD =
      constructibleClass X (D ∩ E) (hD.inter hE) (hiD.inter hiE) +
        constructibleClass X (D \ E) (hD.sdiff hE) (hiD.sdiff hiE) := by
  have hDE : Disjoint (D ∩ E) (D \ E) := Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx.2)
  have hh := constructibleClass_disjoint_union X (D ∩ E) (D \ E) (hD.inter hE) (hD.sdiff hE)
    (hiD.inter hiE) (hiD.sdiff hiE) hDE
  simpa only [Set.inter_union_sdiff] using hh

def emptyImmersedPresentation (X : Object) : ImmersedPresentation X ∅ where
  index := Fin 0
  finite := inferInstance
  piece := Fin.elim0
  inclusion := fun i => Fin.elim0 i
  immersion := fun i => Fin.elim0 i
  contained := fun i => Fin.elim0 i
  partition := fun _ => by simp

theorem constructibleClass_empty (X : Object) :
    constructibleClass X ∅ IsConstructible.empty (Object.Invariant.empty X) = 0 := by
  rw [constructibleClass_eq_presentation _ _ _ _ (emptyImmersedPresentation X)]
  simp [ImmersedPresentation.value, emptyImmersedPresentation]

end DiamondIntegral.Section5.EquivariantVariety
