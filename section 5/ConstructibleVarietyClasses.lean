import «section 5».VarietyCommonRefinements
import «section 5».InvariantConstructibleSubstrata

/-! Every invariant constructible subset of a good finite-action variety
has a finite actual immersed presentation. Its geometric class is independent
of that presentation, by the reduced common refinement theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory Topology

theorem invariant_constructible_immersed_presentation (X : Object) (D : Set X.scheme)
    (hD : IsConstructible D) (hiD : X.Invariant D) : Nonempty (ImmersedPresentation X D) := by
  obtain ⟨N, ρ, hρ⟩ := X.finite_level
  letI : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  letI : Fintype (rootsOfUnity (N : ℕ) ℂ) := Fintype.ofFinite _
  have hiρ : ∀ h x, schemePointAction ρ h x ∈ D ↔ x ∈ D := by
    intro h x
    obtain ⟨η, hη⟩ := finiteRootProjection_surjective N h
    have hh := hiD η x
    rw [hρ] at hh
    change schemePointAction ρ (finiteRootProjection N η) x ∈ D ↔ x ∈ D at hh
    simpa only [hη] using hh
  obtain ⟨n, S, hS, hSD, hSi, hpart, _⟩ := finite_invariant_constructible_substrata
    (schemeActionHomeomorph ρ) D hD hiρ
    (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
  have hiS (i : Fin n) : X.Invariant (S i) := by
    intro η x
    change schemePointAction X.action η x ∈ S i ↔ x ∈ S i
    rw [hρ]
    exact hSi i (finiteRootProjection N η) x
  refine ⟨?_⟩
  exact {
    index := Fin n
    finite := inferInstance
    piece := fun i => subsetObject X (S i) (hS i) (hiS i)
    inclusion := fun i => subsetInclusion X (S i) (hS i) (hiS i)
    immersion := fun i => subsetInclusion_immersion X (S i) (hS i) (hiS i)
    contained := fun i => (subsetInclusion_range X (S i) (hS i) (hiS i)).subset.trans (hSD i)
    partition := fun x => by
      simp only [subsetInclusion_range]
      exact hpart x }

def constructibleClass (X : Object) (D : Set X.scheme)
    (hD : IsConstructible D) (hiD : X.Invariant D) : Ring :=
  (Classical.choice (invariant_constructible_immersed_presentation X D hD hiD)).value

theorem constructibleClass_eq_presentation (X : Object) (D : Set X.scheme)
    (hD : IsConstructible D) (hiD : X.Invariant D) (c : ImmersedPresentation X D) :
    constructibleClass X D hD hiD = c.value :=
  immersed_presentation_independent _ c

def singletonImmersedPresentation {X Y : Object} (f : Morphism Y X) [IsImmersion f.hom] :
    ImmersedPresentation X (Set.range f.hom) where
  index := PUnit
  finite := inferInstance
  piece := fun _ => Y
  inclusion := fun _ => f
  immersion := fun _ => inferInstance
  contained := fun _ => Set.Subset.refl _
  partition := fun _ => by
    constructor
    · intro hx
      exact ⟨PUnit.unit, hx, fun _ _ => Subsingleton.elim _ _⟩
    · rintro ⟨_, hx, _⟩
      exact hx

theorem constructibleClass_of_immersion {X Y : Object} (f : Morphism Y X)
    [IsImmersion f.hom] :
    constructibleClass X (Set.range f.hom)
      (by letI := X.noetherian; exact locallyClosed_constructible_of_noetherian f.hom.isLocallyClosed_range)
      f.range_invariant = objectClass Y := by
  rw [constructibleClass_eq_presentation _ _ _ _ (singletonImmersedPresentation f)]
  simp [ImmersedPresentation.value, singletonImmersedPresentation]

end DiamondIntegral.Section5.EquivariantVariety
