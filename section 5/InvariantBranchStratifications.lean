import «section 5».FiniteCertifiedBranchPieces
import «section 5».InvariantConstructibleSubstrata
import «section 5».ReducedImmersionSchemeActions
import «section 5».EquivariantBranchGluing
import «section 5».GraphStratumMorphisms

/-! Every finite reduced affine branch presentation has certified
regular strata adapted to a finite action on its input. The certificates
also prove equivariance whenever the complex graph is equivariant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology
attribute [local instance] locallyClosedAffineScheme_isReduced locallyClosedAffineInclusion_isImmersion
variable {S T J : Type} [CommRing S] [CommRing T] [Algebra ℂ S] [Algebra ℂ T]
variable {A : J → Type} [∀ j, CommRing (A j)] [∀ j, Algebra ℂ (A j)]
variable {f : ∀ j, S →ₐ[ℂ] A j} {a : ∀ j, T →ₐ[ℂ] A j}

theorem AffineBranchCertificate.equivariant [∀ j, Algebra.FiniteType ℂ (A j)]
    {X : Scheme} [AlgebraicGeometry.IsReduced X]
    {base : X ⟶ Spec (.of S)} {F : X ⟶ Spec (.of T)}
    (c : AffineBranchCertificate A f a base F)
    (s : X ⟶ X) (k : S →ₐ[ℂ] S) (l : T →ₐ[ℂ] T)
    (hs : s ≫ base = base ≫ Spec.map (CommRingCat.ofHom k.toRingHom))
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp ((f i).comp k) = ψ.comp (f j) → φ.comp ((a i).comp l) = ψ.comp (a j)) :
    s ≫ F = F ≫ Spec.map (CommRingCat.ofHom l.toRingHom) :=
  glued_branches_equivariant c.cover (fun i => A (c.index i))
    (fun i => f (c.index i)) (fun i => a (c.index i)) c.lift base c.input_fac F
      (fun i => (c.output_fac i).symm) s k l hs (fun i j => hc (c.index i) (c.index j))

theorem finite_invariant_branch_stratification [Algebra.FiniteType ℂ S]
    [Fintype J] [∀ j, Algebra.FiniteType ℂ (A j)] [∀ j, _root_.IsReduced (A j)]
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (f j).toRingHom))]
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (f i) = ψ.comp (f j) → φ.comp (a i) = ψ.comp (a j))
    {H : Type} [Group H] [Fintype H] (ρ : H →* Aut (Spec (.of S)))
    (hInv : ∀ h x, schemePointAction ρ h x ∈
      (⋃ j, Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))) ↔
      x ∈ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))) :
    ∃ c : AffineBranchStratification A f a, ∃ σ : ∀ i, H →* Aut (c.scheme i),
      ∀ i h, (σ i h).asIso.hom ≫ c.base i = c.base i ≫ (ρ h).asIso.hom := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  let E := fun j => Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))
  have hE (j : J) : IsConstructible (E j) :=
    locallyClosed_constructible_of_noetherian (Scheme.Hom.isLocallyClosed_range _)
  obtain ⟨r, S', hS, hsub, hSinv, hpart, hclopen⟩ :=
    finite_invariant_constructible_substrata (schemeActionHomeomorph ρ) (⋃ j, E j)
      (IsConstructible.iUnion hE) hInv E hE
  let base := fun k => locallyClosedAffineInclusion (S' k) (hS k)
  have ho (k : Fin r) (j : J) : IsOpen {x : locallyClosedAffineScheme (S' k) (hS k) |
      base k x ∈ E j} :=
    (immersion_preimage_isClopen (base k) (S' k) (E j)
      (locallyClosedAffineInclusion_range _ _).subset (hclopen k j)).isOpen
  have hcover (k : Fin r) (x : locallyClosedAffineScheme (S' k) (hS k)) :
      ∃ j, base k x ∈ E j :=
    Set.mem_iUnion.mp (hsub k ((locallyClosedAffineInclusion_range _ _).subset ⟨x, rfl⟩))
  have hglue (k : Fin r) := glue_immersion_branches_certificate (A := A) (f := f) (a := a)
    hc (base k) (ho k) (hcover k)
  choose F hF using hglue
  let c : AffineBranchStratification A f a := {
    index := Fin r
    finite := inferInstance
    scheme := fun k => locallyClosedAffineScheme (S' k) (hS k)
    base := base
    immersion := fun k => locallyClosedAffineInclusion_isImmersion _ _
    reduced := fun k => locallyClosedAffineScheme_isReduced _ _
    output := F
    certificate := fun k => Classical.choice (hF k)
    partition := by simpa only [base, locallyClosedAffineInclusion_range] using hpart }
  have hi (k : Fin r) (h : H) (x : Spec (.of S)) :
      schemePointAction ρ h x ∈ Set.range (base k) ↔ x ∈ Set.range (base k) := by
    change schemePointAction ρ h x ∈ Set.range (locallyClosedAffineInclusion (S' k) (hS k)) ↔ _
    rw [locallyClosedAffineInclusion_range]
    have hh := hSinv k h x
    change (ρ h).asIso.hom x ∈ S' k ↔ x ∈ S' k at hh
    exact hh
  refine ⟨c, (fun k => reducedImmersionSchemeAction (base k) ρ (hi k)), ?_⟩
  intro k h
  exact reducedImmersionSchemeAction_fac _ _ _ h

theorem finite_equivariant_branch_stratification [Algebra.FiniteType ℂ S]
    [Fintype J] [∀ j, Algebra.FiniteType ℂ (A j)] [∀ j, _root_.IsReduced (A j)]
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (f j).toRingHom))]
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (f i) = ψ.comp (f j) → φ.comp (a i) = ψ.comp (a j))
    {H : Type} [Group H] [Fintype H]
    (ρS : H →* (S ≃ₐ[ℂ] S)) (ρT : H →* (T ≃ₐ[ℂ] T))
    (hInv : ∀ h x, schemePointAction (algebraSpecAction ρS) h x ∈
      (⋃ j, Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))) ↔
      x ∈ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom)))
    (htrans : ∀ h i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp ((f i).comp (ρS h⁻¹).toAlgHom) = ψ.comp (f j) →
        φ.comp ((a i).comp (ρT h⁻¹).toAlgHom) = ψ.comp (a j)) :
    ∃ c : AffineBranchStratification A f a, ∃ σ : ∀ i, H →* Aut (c.scheme i),
      (∀ i h, (σ i h).asIso.hom ≫ c.base i = c.base i ≫ (algebraSpecAction ρS h).asIso.hom) ∧
      (∀ i h, (σ i h).asIso.hom ≫ c.output i = c.output i ≫ (algebraSpecAction ρT h).asIso.hom) := by
  obtain ⟨c, σ, hσ⟩ := finite_invariant_branch_stratification hc (algebraSpecAction ρS) hInv
  refine ⟨c, σ, hσ, ?_⟩
  intro i h
  letI := c.reduced i
  exact (c.certificate i).equivariant (σ i h).asIso.hom
    (ρS h⁻¹).toAlgHom (ρT h⁻¹).toAlgHom (hσ i h) (htrans h)

end DiamondIntegral.Section5
