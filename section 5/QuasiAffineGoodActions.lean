import «section 5».FinitePointAffineNeighborhoods
import «section 5».LocallyClosedAffineSchemes
import «section 5».ReducedImmersionIsomorphisms
import «section 5».InvariantAffineCover
import «section 5».ReducedInducedSchemes

/-! Finite group actions on reduced schemes immersed in a complex
affine scheme are good: every orbit has an actual affine open neighborhood.
Prime avoidance supplies the finite-point neighborhood. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] locallyClosedAffineScheme_isReduced locallyClosedAffineInclusion_isImmersion

theorem finite_points_affine_neighborhood_of_openImmersion {A : Type} [CommRing A]
    {X : Scheme} (i : X ⟶ Spec (.of A)) [IsOpenImmersion i]
    (T : Set X) (hT : T.Finite) : ∃ V : X.Opens, IsAffineOpen V ∧ T ⊆ V := by
  obtain ⟨f, hTf, hf⟩ := finite_points_principal_neighborhood
    (i.opensRange : Set (Spec (.of A))) i.opensRange.isOpen (i '' T) (hT.image i) (by
      rintro _ ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩)
  refine ⟨i ⁻¹ᵁ PrimeSpectrum.basicOpen f,
    (IsAffineOpen.Spec_basicOpen f).preimage_of_isOpenImmersion i hf, ?_⟩
  intro x hx
  exact hTf ⟨x, hx, rfl⟩

theorem finite_points_affine_neighborhood_of_reduced_immersion
    {A : Type} [CommRing A]
    {X : Scheme} [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of A)) [IsImmersion f] (T : Set X) (hT : T.Finite) :
    ∃ V : X.Opens, IsAffineOpen V ∧ T ⊆ V := by
  let S := Set.range f
  have hS : IsLocallyClosed S := f.isLocallyClosed_range
  letI := reducedLocallyClosedScheme_isReduced S hS
  letI := reducedLocallyClosedInclusion_isImmersion S hS
  letI := reducedClosedInclusion_isClosedImmersion (TopologicalSpace.Closeds.closure S)
  let Z := reducedClosedScheme (TopologicalSpace.Closeds.closure S)
  letI : IsAffine Z := isAffine_of_isAffineHom
    (reducedClosedInclusion (TopologicalSpace.Closeds.closure S))
  let e := reducedImmersionIso f (reducedLocallyClosedInclusion S hS)
    (reducedLocallyClosedInclusion_range S hS).symm
  let j := e.hom ≫ (reducedLocallyClosedOpen S hS).ι ≫ Z.isoSpec.hom
  letI : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  exact finite_points_affine_neighborhood_of_openImmersion j T hT

theorem finite_action_on_reduced_affine_immersion_isGood
    {A : Type} [CommRing A]
    {X : Scheme} [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of A)) [IsImmersion f]
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut X) :
    ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ ∀ h, schemePointAction ρ h x ∈ V := by
  intro x
  obtain ⟨V, hV, hTV⟩ := finite_points_affine_neighborhood_of_reduced_immersion f
    (Set.range (fun h => schemePointAction ρ h x)) (Set.finite_range _)
  exact ⟨V, hV, fun h => hTV ⟨h, rfl⟩⟩

end DiamondIntegral.Section5
