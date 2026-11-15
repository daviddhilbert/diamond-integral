import «section 5».VarietyImmersionGoodness
import «section 5».ReducedImmersionSchemeActions
import Mathlib.AlgebraicGeometry.Noetherian

/-! Invariant reduced immersed subschemes are genuine geometric variety
objects. The finite action, finite type, separation and goodness are derived
from the ambient object and the actual immersion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] Object.locally_finite_type Object.compact Object.separated Object.reduced

theorem Object.noetherian (X : Object) : NoetherianSpace X.scheme := by
  letI : IsLocallyNoetherian X.scheme := LocallyOfFiniteType.isLocallyNoetherian X.toC
  letI : IsNoetherian X.scheme := ⟨⟩
  infer_instance

theorem Object.schemeSeparated (X : Object) : X.scheme.IsSeparated := by
  constructor
  have he : Limits.terminal.from X.scheme =
      X.toC ≫ Limits.terminal.from (Spec (.of ℂ)) := Limits.terminal.hom_ext _ _
  rw [he]
  infer_instance

def immersedObject (X : Object) {Y : Scheme.{0}} [AlgebraicGeometry.IsReduced Y]
    (f : Y ⟶ X.scheme) [IsImmersion f]
    (τ : CompatibleRoots ℂ →* Aut Y)
    (hτ : ∃ N : ℕ+, ∃ σ : rootsOfUnity (N : ℕ) ℂ →* Aut Y,
      τ = σ.comp (finiteRootProjection N))
    (hf : ∀ h, (τ h).asIso.hom ≫ f = f ≫ (X.action h).asIso.hom) : Object := by
  letI := X.noetherian
  letI : NoetherianSpace Y := f.isEmbedding.isInducing.noetherianSpace
  exact {
    scheme := Y
    toC := f ≫ X.toC
    locally_finite_type := inferInstance
    compact := inferInstance
    separated := inferInstance
    reduced := inferInstance
    action := τ
    overC := fun h => by rw [← Category.assoc, hf, Category.assoc, X.overC]
    finite_level := hτ
    good := equivariant_reduced_immersion_isGood X f τ hτ hf }

theorem restrictedAction_finite_level (X : Object) {Y : Scheme.{0}}
    [AlgebraicGeometry.IsReduced Y] (f : Y ⟶ X.scheme) [IsImmersion f]
    (hInv : ∀ h z, schemePointAction X.action h z ∈ Set.range f ↔ z ∈ Set.range f) :
    ∃ N : ℕ+, ∃ σ : rootsOfUnity (N : ℕ) ℂ →* Aut Y,
      reducedImmersionSchemeAction f X.action hInv = σ.comp (finiteRootProjection N) := by
  obtain ⟨N, ρ, hρ⟩ := X.finite_level
  have hInvρ : ∀ h z, schemePointAction ρ h z ∈ Set.range f ↔ z ∈ Set.range f := by
    intro h z
    obtain ⟨g, hg⟩ := finiteRootProjection_surjective N h
    have hh := hInv g z
    rw [hρ] at hh
    change schemePointAction ρ (finiteRootProjection N g) z ∈ Set.range f ↔ z ∈ Set.range f at hh
    simpa only [hg] using hh
  refine ⟨N, reducedImmersionSchemeAction f ρ hInvρ, ?_⟩
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  apply CategoryTheory.Iso.ext
  apply (cancel_mono f).mp
  change (reducedImmersionSchemeAction f X.action hInv g).asIso.hom ≫ f =
    (reducedImmersionSchemeAction f ρ hInvρ (finiteRootProjection N g)).asIso.hom ≫ f
  rw [reducedImmersionSchemeAction_fac, reducedImmersionSchemeAction_fac, hρ]
  rfl

def invariantImmersedObject (X : Object) {Y : Scheme.{0}} [AlgebraicGeometry.IsReduced Y]
    (f : Y ⟶ X.scheme) [IsImmersion f]
    (hInv : ∀ h z, schemePointAction X.action h z ∈ Set.range f ↔ z ∈ Set.range f) : Object :=
  immersedObject X f (reducedImmersionSchemeAction f X.action hInv)
    (restrictedAction_finite_level X f hInv)
    (reducedImmersionSchemeAction_fac f X.action hInv)

def invariantImmersedInclusion (X : Object) {Y : Scheme.{0}} [AlgebraicGeometry.IsReduced Y]
    (f : Y ⟶ X.scheme) [IsImmersion f]
    (hInv : ∀ h z, schemePointAction X.action h z ∈ Set.range f ↔ z ∈ Set.range f) :
    Morphism (invariantImmersedObject X f hInv) X where
  hom := f
  overC := rfl
  equivariant := reducedImmersionSchemeAction_fac f X.action hInv

end DiamondIntegral.Section5.EquivariantVariety
