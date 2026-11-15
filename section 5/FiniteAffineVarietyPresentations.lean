import «section 5».ImmersedPresentationLoci
import «section 5».InvariantAffineStratification

/-! Every good finite-action variety has a finite partition by actual
invariant affine reduced varieties. The affine schemes are the reduced
closed strata inside the invariant affine open cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] reducedClosedScheme_isReduced reducedClosedInclusion_isClosedImmersion

theorem invariant_affine_closed_piece (X : Object) (U : X.scheme.Opens) (hU : IsAffineOpen U)
    (S : Set X.scheme) (hSU : S ⊆ U) (hS : IsClosed {x : U | x.val ∈ S}) (hiS : X.Invariant S) :
    ∃ Y : Object, ∃ i : Morphism Y X, IsImmersion i.hom ∧ IsAffine Y.scheme ∧ Set.range i.hom = S := by
  letI : IsAffine U.toScheme := hU
  let C : Closeds U.toScheme := ⟨{x : U | x.val ∈ S}, hS⟩
  let j := reducedClosedInclusion C ≫ U.ι
  letI : IsImmersion j := by dsimp only [j]; infer_instance
  letI : IsAffine (reducedClosedScheme C) := isAffine_of_isAffineHom (reducedClosedInclusion C)
  have hR : Set.range j = S := by
    change Set.range (U.ι ∘ reducedClosedInclusion C) = S
    rw [Set.range_comp, reducedClosedInclusion_range]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      exact ⟨⟨x, hSU hx⟩, hx, rfl⟩
  have hiR : X.Invariant (Set.range j) := by simpa only [hR] using hiS
  let Y := invariantImmersedObject X j hiR
  let i := invariantImmersedInclusion X j hiR
  exact ⟨Y, i, (inferInstance : IsImmersion j),
    (inferInstance : IsAffine (reducedClosedScheme C)), hR⟩

structure AffineVarietyPresentation (X : Object) where
  presentation : ImmersedPresentation X Set.univ
  affine : ∀ i, IsAffine (presentation.piece i).scheme

theorem finite_affine_variety_presentation (X : Object) : Nonempty (AffineVarietyPresentation X) := by
  obtain ⟨N, ρ, hρ⟩ := X.finite_level
  letI : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  letI : Finite (rootsOfUnity (N : ℕ) ℂ) := inferInstance
  letI : CompactSpace X.scheme := X.compact
  letI := X.schemeSeparated
  have hgood : ∀ x : X.scheme, ∃ U : X.scheme.Opens, IsAffineOpen U ∧
      ∀ h : rootsOfUnity (N : ℕ) ℂ, schemePointAction ρ h x ∈ U := by
    intro x
    obtain ⟨U, hU, hgood⟩ := X.good x
    refine ⟨U, hU, ?_⟩
    intro h
    obtain ⟨η, hη⟩ := finiteRootProjection_surjective N h
    have hh := hgood η
    change schemePointAction X.action η x ∈ U at hh
    rw [hρ] at hh
    change schemePointAction ρ (finiteRootProjection N η) x ∈ U at hh
    simpa only [hη] using hh
  obtain ⟨n, U, S, hU, hSU, hS, hpart, hSi⟩ := finite_invariant_affine_stratification ρ hgood
  have hiS (i : Fin n) : X.Invariant (S i) := by
    intro η x
    change schemePointAction X.action η x ∈ S i ↔ x ∈ S i
    rw [hρ]
    exact hSi i (finiteRootProjection N η) x
  choose Y f hf hAff hR using (fun i => invariant_affine_closed_piece X (U i) (hU i) (S i) (hSU i) (hS i) (hiS i))
  refine ⟨?_⟩
  exact {
    presentation := {
      index := Fin n
      finite := inferInstance
      piece := Y
      inclusion := f
      immersion := hf
      contained := fun _ => Set.subset_univ _
      partition := fun x => by
        simpa only [hR, Set.mem_univ, true_iff] using hpart x }
    affine := hAff }

end DiamondIntegral.Section5.EquivariantVariety
