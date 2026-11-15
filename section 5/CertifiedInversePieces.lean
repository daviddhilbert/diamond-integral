import «section 5».AffineBranchCertificates
import «section 5».ReducedSchemeProducts

/-! Forward and inverse affine-branch certificates turn the reduced
intersection of two regular strata into a common immersed scheme.
Both projections are actual immersions; no inverse morphism is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] reducedPullback_isReduced schemeReductionMap_isClosedImmersion

theorem certified_inverse_pieces {S T J : Type} [CommRing S] [CommRing T]
    [Algebra ℂ S] [Algebra ℂ T] (A : J → Type)
    [∀ j, CommRing (A j)] [∀ j, Algebra ℂ (A j)] [∀ j, Algebra.FiniteType ℂ (A j)]
    (f : ∀ j, S →ₐ[ℂ] A j) (a : ∀ j, T →ₐ[ℂ] A j)
    (hv : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (a i) = ψ.comp (a j) → φ.comp (f i) = ψ.comp (f j))
    {X Y : Scheme} (cx : X ⟶ Spec (.of S)) [IsImmersion cx]
    (cy : Y ⟶ Spec (.of T)) [IsImmersion cy]
    (F : X ⟶ Spec (.of T)) (H : Y ⟶ Spec (.of S))
    (c : AffineBranchCertificate A f a cx F) (d : AffineBranchCertificate A a f cy H) :
    IsImmersion (reducedPullbackFst F cy) ∧ IsImmersion (reducedPullbackSnd F cy) ∧
      reducedPullbackFst F cy ≫ cx = reducedPullbackSnd F cy ≫ H := by
  let r := reducedPullbackFst F cy
  let s := reducedPullbackSnd F cy
  have he : r ≫ F = s ≫ cy := reducedPullback_condition F cy
  have c' : AffineBranchCertificate A a f (s ≫ cy) (r ≫ cx) := by
    simpa only [he] using (c.pullback r).symm
  have hInv : r ≫ cx = s ≫ H := c'.functional A a f hv (d.pullback s)
  have hr : IsImmersion r := by
    change IsImmersion (schemeReductionMap _ ≫ CategoryTheory.Limits.pullback.fst F cy)
    infer_instance
  letI := hr
  have hsH : IsImmersion (s ≫ H) := by
    rw [← hInv]
    infer_instance
  letI := hsH
  exact ⟨hr, IsImmersion.of_comp s H, hInv⟩

end DiamondIntegral.Section5
