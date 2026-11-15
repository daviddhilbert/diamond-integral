import «section 5».InvariantOpenSchemeActions
import «section 5».LocallyClosedAffineSchemes
import «section 5».AffineSchemeActions

/-! Invariant locally closed affine-spectrum subsets inherit actual
scheme actions on their reduced induced structures. Equivariance of the
locally closed immersion is proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology TopologicalSpace

theorem schemeAction_closure_invariant {X : Scheme} {G : Type} [Group G]
    (ρ : G →* Aut X) (S : Set X)
    (hS : ∀ g x, schemePointAction ρ g x ∈ S ↔ x ∈ S) :
    ∀ g x, schemePointAction ρ g x ∈ closure S ↔ x ∈ closure S := by
  have hp (g : G) : closure S ⊆ (schemePointAction ρ g) ⁻¹' closure S :=
    closure_minimal (fun x hx => subset_closure ((hS g x).mpr hx))
      (isClosed_closure.preimage (ρ g).asIso.hom.continuous)
  intro g x
  constructor
  · intro hx
    have h := hp g⁻¹ hx
    have he : schemePointAction ρ g⁻¹ (schemePointAction ρ g x) = x := by
      rw [← schemePointAction_mul, inv_mul_cancel, schemePointAction_one]
    exact he ▸ h
  · intro hx
    exact hp g hx

theorem schemeAction_coborder_invariant {X : Scheme} {G : Type} [Group G]
    (ρ : G →* Aut X) (S : Set X)
    (hS : ∀ g x, schemePointAction ρ g x ∈ S ↔ x ∈ S) :
    ∀ g x, schemePointAction ρ g x ∈ coborder S ↔ x ∈ coborder S := by
  intro g x
  simp only [coborder, Set.mem_compl_iff, Set.mem_sdiff,
    schemeAction_closure_invariant ρ S hS g x, hS g x]

theorem invariant_locally_closed_affine_action {A : Type} [CommRing A] [Algebra ℂ A]
    {G : Type} [Group G] (ρ : G →* (A ≃ₐ[ℂ] A))
    (S : Set (PrimeSpectrum A)) (hS : IsLocallyClosed S)
    (hInv : ∀ g x, schemePointAction (algebraSpecAction ρ) g x ∈ S ↔ x ∈ S) :
    ∃ σ : G →* Aut (locallyClosedAffineScheme S hS), ∀ g,
      (σ g).asIso.hom ≫ locallyClosedAffineInclusion S hS =
        locallyClosedAffineInclusion S hS ≫ (algebraSpecAction ρ g).asIso.hom := by
  have hcl := schemeAction_closure_invariant (algebraSpecAction ρ) S hInv
  have hcb := schemeAction_coborder_invariant (algebraSpecAction ρ) S hInv
  have hZ (g : G) (x : PrimeSpectrum A) :
      PrimeSpectrum.comap (ρ g).toRingHom x ∈ closure S ↔ x ∈ closure S := by
    have h := hcl g⁻¹ x
    change PrimeSpectrum.comap (ρ ((g⁻¹)⁻¹)).toRingHom x ∈ closure S ↔ x ∈ closure S at h
    simpa only [inv_inv] using h
  let I := PrimeSpectrum.vanishingIdeal (closure S)
  let τ := algebraSpecAction (invariantIdealQuotientAction ρ I (invariantClosedIdeal_stable ρ (closure S) hZ))
  let U := locallyClosedAffineOpen S hS
  have hU (g : G) (x : closedAffineScheme (closure S)) :
      schemePointAction τ g x ∈ U ↔ x ∈ U := by
    change closedAffineInclusion (closure S) (schemePointAction τ g x) ∈ coborder S ↔
      closedAffineInclusion (closure S) x ∈ coborder S
    have he := congrArg (fun f : closedAffineScheme (closure S) ⟶ Spec (.of A) => f x)
      (invariantClosedAffineInclusion_equivariant ρ (closure S) hZ g)
    change schemePointAction (algebraSpecAction ρ) g (closedAffineInclusion (closure S) x) =
      closedAffineInclusion (closure S) (schemePointAction τ g x) at he
    rw [← he]
    exact hcb g _
  refine ⟨invariantOpenSchemeAction τ U hU, ?_⟩
  intro g
  change (invariantOpenSchemeAction τ U hU g).asIso.hom ≫
    (U.ι ≫ closedAffineInclusion (closure S)) =
      (U.ι ≫ closedAffineInclusion (closure S)) ≫ (algebraSpecAction ρ g).asIso.hom
  rw [← Category.assoc, invariantOpenSchemeAction_equivariant, Category.assoc]
  have he : (τ g).asIso.hom ≫ closedAffineInclusion (closure S) =
      closedAffineInclusion (closure S) ≫ (algebraSpecAction ρ g).asIso.hom :=
    (invariantClosedAffineInclusion_equivariant ρ (closure S) hZ g).symm
  exact (congrArg (fun f : closedAffineScheme (closure S) ⟶ Spec (.of A) => U.ι ≫ f) he).trans
    (Category.assoc _ _ _).symm

end DiamondIntegral.Section5
