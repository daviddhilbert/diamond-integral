import «section 5».ConstructibleVarietyClasses

/-! The locus of a finite immersed presentation is intrinsically
constructible and invariant, including all scheme points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory Topology
variable {X : Object} {D E : Set X.scheme}

theorem ImmersedPresentation.locus_eq (c : ImmersedPresentation X D) :
    D = ⋃ i, Set.range (c.inclusion i).hom := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, _⟩ := (c.partition x).mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact c.contained i hi

theorem ImmersedPresentation.constructible (c : ImmersedPresentation X D) : IsConstructible D := by
  letI := c.finite
  letI := X.noetherian
  letI (i : c.index) := c.immersion i
  rw [c.locus_eq]
  exact IsConstructible.iUnion (fun i =>
    locallyClosed_constructible_of_noetherian (c.inclusion i).hom.isLocallyClosed_range)

theorem ImmersedPresentation.invariant (c : ImmersedPresentation X D) : X.Invariant D := by
  intro h x
  rw [c.locus_eq]
  simp only [Set.mem_iUnion]
  exact exists_congr (fun i => (c.inclusion i).range_invariant h x)

def ImmersedPresentation.changeLocus (c : ImmersedPresentation X D) (he : D = E) :
    ImmersedPresentation X E := he ▸ c

theorem ImmersedPresentation.changeLocus_value (c : ImmersedPresentation X D) (he : D = E) :
    (c.changeLocus he).value = c.value := by subst E; rfl

end DiamondIntegral.Section5.EquivariantVariety
