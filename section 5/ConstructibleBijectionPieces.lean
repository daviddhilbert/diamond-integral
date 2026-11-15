import «section 5».BasicRationalGraphPartitions
import «section 5».BasicGraphInverseProjectionImmersions

/-! A constructible complex bijection is represented by finitely many
actual reduced affine graph schemes, with both projections immersions.
Their complex points partition the original graph. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry CategoryTheory
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem complex_constructible_bijection_algebraic_pieces {n m : ℕ}
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : (Set.univ : Set ℂ).Definable Language.ring G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z)
    (hv : ∀ (y : Fin m → ℂ) (x z : Fin n → ℂ),
      Sum.elim x y ∈ G → Sum.elim z y ∈ G → x = z) :
    ∃ (J : Type) (_ : Fintype J)
      (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ)),
      (∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom)) ∧
        IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphRight (D j)).toRingHom))) ∧
      (∀ j, AlgebraicGeometry.IsReduced (basicConstructibleScheme (D j))) ∧
      (∀ j v, complexTupleSpectrumPoint v ∈ (D j).toSet → v ∈ G) ∧
      ∀ v, v ∈ G ↔ ∃! j, complexTupleSpectrumPoint v ∈ (D j).toSet := by
  obtain ⟨Z, hZ, heZ, J, hJ, D, r, s, hsub, hpartition⟩ :=
    complex_bijection_basic_rational_graph_partition G hG hu hv
  refine ⟨J, hJ, D, ?_, (fun j => basicConstructibleScheme_isReduced (D j)), ?_, ?_⟩
  · intro j
    exact ⟨basicGraphLeft_isImmersion (D j) (r j).1 (r j).2 (fun x hx => (hsub j hx).2.1),
      basicGraphRight_isImmersion (D j) (s j).1 (s j).2 (fun x hx => (hsub j hx).2.2)⟩
  · intro j v hv
    exact (heZ v).mpr (hsub j hv).1
  · intro v
    exact (heZ v).trans (hpartition (complexTupleSpectrumPoint v))

end DiamondIntegral.Section5
