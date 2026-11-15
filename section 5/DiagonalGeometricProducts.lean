import «section 5».AffineProductPartitions
import «section 5».DiagonalGeometricValues

/-! Multiplicativity of the geometric value follows from actual reduced
products of the immersed pieces. All point sets and their projections are
identified before passing to the ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology PuiseuxOriginal EquivariantVariety
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem complexTupleSpectrumPoint_coordinate {n m : ℕ} (f : Fin n → Fin m) (x : Fin m → ℂ) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := ℂ) f).toRingHom) (complexTupleSpectrumPoint x) =
      complexTupleSpectrumPoint (x ∘ f) := by
  apply PrimeSpectrum.ext
  ext p
  change (MvPolynomial.eval₂Hom (RingHom.id ℂ) x) (MvPolynomial.rename f p) = 0 ↔
    (MvPolynomial.eval₂Hom (RingHom.id ℂ) (x ∘ f)) p = 0
  simp [MvPolynomial.eval₂_rename]

theorem complexSpectrumExtension_product (X Y : DiagonalConstructible.Object) :
    complexSpectrumExtension (tupleProductSet X.domain Y.domain) (DiagonalConstructible.product X Y).definable =
      affineProductLocus X.weights Y.weights (complexSpectrumExtension X.domain X.definable)
        (complexSpectrumExtension Y.domain Y.definable) := by
  apply constructible_eq_of_complex_points _ _ (complexSpectrumExtension_constructible _ _)
    (affineProductLocus_constructible _ _ (complexSpectrumExtension_constructible _ _)
      (complexSpectrumExtension_constructible _ _))
  intro φ
  rw [← complexTupleSpectrumPoint_algHom φ, complexSpectrumExtension_point]
  change _ ↔
    Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := ℂ) (Fin.castAdd Y.arity)).toRingHom)
        (complexTupleSpectrumPoint (fun i => φ (MvPolynomial.X i))) ∈ complexSpectrumExtension X.domain X.definable ∧
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := ℂ) (Fin.natAdd X.arity)).toRingHom)
        (complexTupleSpectrumPoint (fun i => φ (MvPolynomial.X i))) ∈ complexSpectrumExtension Y.domain Y.definable
  rw [complexTupleSpectrumPoint_coordinate, complexTupleSpectrumPoint_coordinate,
    complexSpectrumExtension_point, complexSpectrumExtension_point]
  rfl

theorem PuiseuxOriginal.DiagonalConstructible.geometricValue_product (X Y : DiagonalConstructible.Object) :
    geometricValue (product X Y) = geometricValue X * geometricValue Y := by
  have hh := constructibleClass_affine_product X.weights Y.weights
    (complexSpectrumExtension X.domain X.definable) (complexSpectrumExtension Y.domain Y.definable)
    (complexSpectrumExtension_constructible _ _) (complexSpectrumExtension_constructible _ _)
    (complexSpectrumExtension_invariant _ _ _ X.invariant) (complexSpectrumExtension_invariant _ _ _ Y.invariant)
  have he : geometricValue (product X Y) =
      constructibleClass (rationalAffineObject (Fin.append X.weights Y.weights))
        (affineProductLocus X.weights Y.weights (complexSpectrumExtension X.domain X.definable)
          (complexSpectrumExtension Y.domain Y.definable))
        (affineProductLocus_constructible _ _ (complexSpectrumExtension_constructible _ _)
          (complexSpectrumExtension_constructible _ _))
        (affineProductLocus_invariant _ _ (complexSpectrumExtension_invariant _ _ _ X.invariant)
          (complexSpectrumExtension_invariant _ _ _ Y.invariant)) :=
    constructibleClass_set_congr _ _ _ _ _ _ _ (complexSpectrumExtension_product X Y)
  exact he.trans hh

end DiamondIntegral.Section5
