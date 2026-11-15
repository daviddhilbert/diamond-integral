import «section 5».FiniteCertifiedBranchPieces
import «section 5».ReducedPullbackActions

/-! The common reduced pieces of equivariant certified regular strata
inherit actual group actions and equivariant immersion projections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

theorem equivariant_certified_common_pieces {S T J H : Type}
    [CommRing S] [CommRing T] [Algebra ℂ S] [Algebra ℂ T] [Group H]
    (A : J → Type) [∀ j, CommRing (A j)] [∀ j, Algebra ℂ (A j)]
    [∀ j, Algebra.FiniteType ℂ (A j)]
    (f : ∀ j, S →ₐ[ℂ] A j) (a : ∀ j, T →ₐ[ℂ] A j)
    (hv : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (a i) = ψ.comp (a j) → φ.comp (f i) = ψ.comp (f j))
    (c : AffineBranchStratification A f a) (d : AffineBranchStratification A a f)
    (σ : ∀ i, H →* Aut (c.scheme i)) (τ : ∀ j, H →* Aut (d.scheme j))
    (ρ : H →* Aut (Spec (.of T)))
    (hF : ∀ i h, (σ i h).asIso.hom ≫ c.output i = c.output i ≫ (ρ h).asIso.hom)
    (hd : ∀ j h, (τ j h).asIso.hom ≫ d.base j = d.base j ≫ (ρ h).asIso.hom) :
    ∃ κ : ∀ i j, H →* Aut (certifiedCommonPiece c d i j),
      (∀ i j h, (κ i j h).asIso.hom ≫ certifiedCommonLeft c d i j =
        certifiedCommonLeft c d i j ≫ (σ i h).asIso.hom) ∧
      (∀ i j h, (κ i j h).asIso.hom ≫ certifiedCommonRight c d i j =
        certifiedCommonRight c d i j ≫ (τ j h).asIso.hom) ∧
      (∀ i j, IsImmersion (certifiedCommonLeft c d i j) ∧ IsImmersion (certifiedCommonRight c d i j)) := by
  refine ⟨(fun i j => reducedPullbackSchemeAction (c.output i) (d.base j)
    (σ i) (τ j) ρ (hF i) (hd j)), ?_, ?_, ?_⟩
  · intro i j h
    exact reducedPullbackSchemeAction_fst _ _ _ _ _ _ _ h
  · intro i j h
    exact reducedPullbackSchemeAction_snd _ _ _ _ _ _ _ h
  · intro i j
    have hi := certifiedCommon_immersions hv c d i j
    exact ⟨hi.1, hi.2.1⟩

end DiamondIntegral.Section5
