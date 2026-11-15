import «section 5».InvariantConstructibleStrata
import «section 5».InvariantLocallyClosedActions

/-! Invariant constructible stratification instantiated on actual
schemes. For affine spectra every stratum receives its reduced scheme,
its actual group action, and its equivariant immersion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology TopologicalSpace

def schemeActionHomeomorph {X : Scheme} {G : Type} [Group G] (ρ : G →* Aut X) :
    G →* (X ≃ₜ X) where
  toFun g := Scheme.homeoOfIso (ρ g).asIso
  map_one' := by
    apply Homeomorph.ext
    intro x
    exact schemePointAction_one ρ x
  map_mul' g h := by
    apply Homeomorph.ext
    intro x
    exact schemePointAction_mul ρ g h x

theorem finite_scheme_invariant_constructible_strata {X : Scheme} {G : Type}
    [Group G] [Fintype G] {ι : Type} [Fintype ι]
    (ρ : G →* Aut X) (D : ι → Set X) (hD : ∀ i, IsConstructible (D i)) :
    ∃ (n : ℕ) (S : Fin n → Set X),
      (∀ k, IsLocallyClosed (S k)) ∧
      (∀ k g x, schemePointAction ρ g x ∈ S k ↔ x ∈ S k) ∧
      (∀ x, ∃! k, x ∈ S k) ∧
      (∀ k i, IsClopen {x : S k | x.val ∈ D i}) :=
  finite_invariant_constructible_strata (schemeActionHomeomorph ρ) D hD

theorem finite_affine_invariant_scheme_strata {A : Type} [CommRing A] [Algebra ℂ A]
    {G : Type} [Group G] [Fintype G] {ι : Type} [Fintype ι]
    (ρ : G →* (A ≃ₐ[ℂ] A)) (D : ι → Set (PrimeSpectrum A))
    (hD : ∀ i, IsConstructible (D i)) :
    ∃ (n : ℕ) (S : Fin n → Set (PrimeSpectrum A)) (hS : ∀ k, IsLocallyClosed (S k))
      (σ : ∀ k, G →* Aut (locallyClosedAffineScheme (S k) (hS k))),
      (∀ k g, (σ k g).asIso.hom ≫ locallyClosedAffineInclusion (S k) (hS k) =
        locallyClosedAffineInclusion (S k) (hS k) ≫ (algebraSpecAction ρ g).asIso.hom) ∧
      (∀ k, AlgebraicGeometry.IsReduced (locallyClosedAffineScheme (S k) (hS k))) ∧
      (∀ k, IsImmersion (locallyClosedAffineInclusion (S k) (hS k))) ∧
      (∀ x, ∃! k, x ∈ S k) ∧
      (∀ k i, IsClopen {x : S k | x.val ∈ D i}) := by
  obtain ⟨n, S, hS, hInv, hunique, hclopen⟩ :=
    finite_scheme_invariant_constructible_strata (algebraSpecAction ρ) D hD
  choose σ hσ using (fun k => invariant_locally_closed_affine_action ρ (S k) (hS k) (hInv k))
  exact ⟨n, S, hS, σ, hσ, (fun k => locallyClosedAffineScheme_isReduced _ _),
    (fun k => locallyClosedAffineInclusion_isImmersion _ _), hunique, hclopen⟩

theorem clopen_inter_locallyClosed {X : Type*} [TopologicalSpace X] (S D : Set X)
    (hS : IsLocallyClosed S) (hD : IsClopen {x : S | x.val ∈ D}) :
    IsLocallyClosed (S ∩ D) := by
  have hrange : IsLocallyClosed (Set.range (Subtype.val : S → X)) := by
    simpa only [Subtype.range_val] using hS
  have h := hD.isClosed.isLocallyClosed.image IsInducing.subtypeVal hrange
  convert h using 1
  ext x
  constructor
  · rintro ⟨hxS, hxD⟩
    exact ⟨⟨x, hxS⟩, hxD, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

end DiamondIntegral.Section5
