import «section 5».EquivariantVarietyRing
import «section 5».QuasiAffineGoodActions

/-! The affine-orbit condition is inherited by invariant reduced immersed
subschemes. The finite orbit is first put over an affine open of the ambient
variety, then prime avoidance supplies its own affine neighborhood. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

theorem finite_points_affine_neighborhood_over_affine_open
    {X Y : Scheme.{0}} [AlgebraicGeometry.IsReduced Y]
    (f : Y ⟶ X) [IsImmersion f] (T : Set Y) (hT : T.Finite)
    (U : X.Opens) (hU : IsAffineOpen U) (hTU : f '' T ⊆ U) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ T ⊆ V := by
  let W := f ⁻¹ᵁ U
  let g := (f ∣_ U) ≫ hU.isoSpec.hom
  letI : AlgebraicGeometry.IsReduced W.toScheme := isReduced_of_isOpenImmersion W.ι
  letI : IsImmersion g := by dsimp only [g]; infer_instance
  let T' : Set W.toScheme := {y | y.val ∈ T}
  have hT' : T'.Finite := hT.preimage Subtype.val_injective.injOn
  obtain ⟨V, hV, hTV⟩ := finite_points_affine_neighborhood_of_reduced_immersion g T' hT'
  refine ⟨W.ι ''ᵁ V, hV.image_of_isOpenImmersion W.ι, ?_⟩
  intro y hy
  exact ⟨⟨y, hTU ⟨y, hy, rfl⟩⟩, hTV hy, rfl⟩

theorem finite_factored_orbit {Y : Scheme.{0}}
    (τ : CompatibleRoots ℂ →* Aut Y)
    (hτ : ∃ N : ℕ+, ∃ σ : rootsOfUnity (N : ℕ) ℂ →* Aut Y,
      τ = σ.comp (finiteRootProjection N)) (y : Y) :
    (Set.range (fun h => schemePointAction τ h y)).Finite := by
  obtain ⟨N, σ, rfl⟩ := hτ
  letI : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  exact (Set.finite_range (fun h => schemePointAction σ h y)).subset
    (by rintro _ ⟨h, rfl⟩; exact ⟨finiteRootProjection N h, rfl⟩)

theorem equivariant_reduced_immersion_isGood
    (X : EquivariantVariety.Object) {Y : Scheme.{0}} [AlgebraicGeometry.IsReduced Y]
    (f : Y ⟶ X.scheme) [IsImmersion f]
    (τ : CompatibleRoots ℂ →* Aut Y)
    (hτ : ∃ N : ℕ+, ∃ σ : rootsOfUnity (N : ℕ) ℂ →* Aut Y,
      τ = σ.comp (finiteRootProjection N))
    (hf : ∀ h, (τ h).asIso.hom ≫ f = f ≫ (X.action h).asIso.hom) :
    ∀ y : Y, ∃ V : Y.Opens, IsAffineOpen V ∧
      ∀ h, schemePointAction τ h y ∈ V := by
  intro y
  obtain ⟨U, hU, hgood⟩ := X.good (f y)
  obtain ⟨V, hV, hTV⟩ := finite_points_affine_neighborhood_over_affine_open f
    (Set.range (fun h => schemePointAction τ h y)) (finite_factored_orbit τ hτ y) U hU (by
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      have he := congrArg (fun g : Y ⟶ X.scheme => g y) (hf h)
      change f (schemePointAction τ h y) = schemePointAction X.action h (f y) at he
      exact he.symm ▸ hgood h)
  exact ⟨V, hV, fun h => hTV ⟨h, rfl⟩⟩

end DiamondIntegral.Section5
