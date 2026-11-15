import «section 5».GraphProjectionImages
import «section 5».DiagonalPolynomialActions

/-! Invariance of a complex graph makes the actual union of its affine
projection images invariant on all scheme points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology PuiseuxOriginal

theorem basicGraphLeft_image_invariant {n m : ℕ} {J : Type} [Fintype J]
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))]
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : ∀ v, v ∈ G ↔ ∃ j, complexTupleSpectrumPoint v ∈ (D j).toSet)
    (N : ℕ+) (w : Fin n → ℤ) (v : Fin m → ℤ)
    (hInv : ∀ (ζ : rootsOfUnity (N : ℕ) ℂ) x y,
      Sum.elim (weightedAction w ζ.val x) (weightedAction v ζ.val y) ∈ G ↔ Sum.elim x y ∈ G) :
    ∀ ζ x, schemePointAction (algebraSpecAction (finiteDiagonalAlgebraAction N w)) ζ x ∈
      (⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))) ↔
      x ∈ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom)) := by
  let U := ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))
  have hU : IsConstructible U := IsConstructible.iUnion (fun j =>
    locallyClosed_constructible_of_noetherian (Scheme.Hom.isLocallyClosed_range _))
  intro ζ
  apply constructible_invariant_of_complex_points U hU (polynomialDiagonalAction w (ζ⁻¹).val)
  intro φ
  rw [basicGraphLeft_complex_image_iff D G hG, basicGraphLeft_complex_image_iff D G hG,
    polynomialDiagonalAction_point]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨weightedAction v ζ.val y, ?_⟩
    have hh := (hInv ζ _ y).mpr hy
    simpa only [← weightedAction_mul, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
      weightedAction_one] using hh
  · rintro ⟨y, hy⟩
    exact ⟨weightedAction v (ζ⁻¹).val y, (hInv ζ⁻¹ _ y).mpr hy⟩

theorem basicGraphRight_image_invariant {n m : ℕ} {J : Type} [Fintype J]
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (basicGraphRight (D j)).toRingHom))]
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : ∀ v, v ∈ G ↔ ∃ j, complexTupleSpectrumPoint v ∈ (D j).toSet)
    (N : ℕ+) (w : Fin n → ℤ) (v : Fin m → ℤ)
    (hInv : ∀ (ζ : rootsOfUnity (N : ℕ) ℂ) x y,
      Sum.elim (weightedAction w ζ.val x) (weightedAction v ζ.val y) ∈ G ↔ Sum.elim x y ∈ G) :
    ∀ ζ x, schemePointAction (algebraSpecAction (finiteDiagonalAlgebraAction N v)) ζ x ∈
      (⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphRight (D j)).toRingHom))) ↔
      x ∈ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphRight (D j)).toRingHom)) := by
  let U := ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphRight (D j)).toRingHom))
  have hU : IsConstructible U := IsConstructible.iUnion (fun j =>
    locallyClosed_constructible_of_noetherian (Scheme.Hom.isLocallyClosed_range _))
  intro ζ
  apply constructible_invariant_of_complex_points U hU (polynomialDiagonalAction v (ζ⁻¹).val)
  intro φ
  rw [basicGraphRight_complex_image_iff D G hG, basicGraphRight_complex_image_iff D G hG,
    polynomialDiagonalAction_point]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨weightedAction w ζ.val x, ?_⟩
    have hh := (hInv ζ x _).mpr hx
    simpa only [← weightedAction_mul, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
      weightedAction_one] using hh
  · rintro ⟨x, hx⟩
    exact ⟨weightedAction w (ζ⁻¹).val x, (hInv ζ⁻¹ x _).mpr hx⟩

end DiamondIntegral.Section5
