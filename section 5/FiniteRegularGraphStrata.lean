import «section 5».GraphStratumMorphisms
import «section 5».InvariantConstructibleSubstrata
import «section 5».ReducedImmersionSchemeActions

/-! Finite invariant input strata carrying regular maps from a complex
definable bijection graph. All branch images and their translates are
included in the stratification construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology
attribute [local instance] locallyClosedAffineScheme_isReduced locallyClosedAffineInclusion_isImmersion
attribute [local instance] basicConstructibleCoordinate_reduced basicConstructibleCoordinate_finiteType

theorem finite_regular_graph_strata {n m : ℕ} {J H : Type}
    [Fintype J] [Group H] [Fintype H]
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))]
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hD : ∀ j v, complexTupleSpectrumPoint v ∈ (D j).toSet → v ∈ G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z)
    (ρ : H →* Aut (Spec (.of (MvPolynomial (Fin n) ℂ))))
    (hInv : ∀ h x, schemePointAction ρ h x ∈
      (⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))) ↔
      x ∈ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))) :
    ∃ (r : ℕ) (S : Fin r → Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ)))
      (hS : ∀ k, IsLocallyClosed (S k))
      (σ : ∀ k, H →* Aut (locallyClosedAffineScheme (S k) (hS k)))
      (F : ∀ k, locallyClosedAffineScheme (S k) (hS k) ⟶ Spec (.of (MvPolynomial (Fin m) ℂ))),
      (∀ k h, (σ k h).asIso.hom ≫ locallyClosedAffineInclusion (S k) (hS k) =
        locallyClosedAffineInclusion (S k) (hS k) ≫ (ρ h).asIso.hom) ∧
      (∀ x, (x ∈ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))) ↔
        ∃! k, x ∈ S k) ∧
      (∀ k, ∃ (ho : ∀ j, IsOpen {x : locallyClosedAffineScheme (S k) (hS k) |
        locallyClosedAffineInclusion (S k) (hS k) x ∈
          Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))}),
        ∀ j, (immersionBranchOpen (fun j => BasicConstructibleCoordinateRing (D j))
          (fun j => basicGraphLeft (D j)) (locallyClosedAffineInclusion (S k) (hS k)) ho j).ι ≫ F k =
          immersionBranchLift (fun j => BasicConstructibleCoordinateRing (D j))
            (fun j => basicGraphLeft (D j)) (locallyClosedAffineInclusion (S k) (hS k)) ho j ≫
              Spec.map (CommRingCat.ofHom (basicGraphRight (D j)).toRingHom)) := by
  let E := fun j => Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))
  have hE (j : J) : IsConstructible (E j) :=
    locallyClosed_constructible_of_noetherian (Scheme.Hom.isLocallyClosed_range _)
  obtain ⟨r, S, hS, hsub, hSinv, hpart, hclopen⟩ :=
    finite_invariant_constructible_substrata (schemeActionHomeomorph ρ) (⋃ j, E j)
      (IsConstructible.iUnion hE) hInv E hE
  have hreg (k : Fin r) := complex_graph_stratum_regular_map D G hD hu
    (S k) (hS k) (hclopen k) (hsub k)
  choose ho F hF huniq using hreg
  have hRInv (k : Fin r) (h : H) (x : Spec (.of (MvPolynomial (Fin n) ℂ))) :
      schemePointAction ρ h x ∈ Set.range (locallyClosedAffineInclusion (S k) (hS k)) ↔
        x ∈ Set.range (locallyClosedAffineInclusion (S k) (hS k)) := by
    rw [locallyClosedAffineInclusion_range]
    have hh := hSinv k h x
    change (ρ h).asIso.hom x ∈ S k ↔ x ∈ S k at hh
    exact hh
  refine ⟨r, S, hS, (fun k => reducedImmersionSchemeAction
    (locallyClosedAffineInclusion (S k) (hS k)) ρ (hRInv k)), F, ?_, hpart, ?_⟩
  · intro k h
    exact reducedImmersionSchemeAction_fac _ _ _ h
  · exact fun k => ⟨ho k, hF k⟩

end DiamondIntegral.Section5
