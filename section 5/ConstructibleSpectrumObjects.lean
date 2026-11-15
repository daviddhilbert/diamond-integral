import «section 5».ComplexConstructibleDomains
import «section 5».DiagonalGeometricRingMap

/-! Invariant constructible spectrum loci have actual diagonal
constructible objects, whose geometric values recover the original locus.
In particular every equivariantly immersed variety has such a representative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology PuiseuxOriginal EquivariantVariety
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem rationalAffineObject_point_action {n : ℕ} (q : Fin n → ℚ) (η : CompatibleRoots ℂ) (x : Fin n → ℂ) :
    schemePointAction (rationalAffineObject q).action η (complexTupleSpectrumPoint x) =
      complexTupleSpectrumPoint (rationalAction q η x) := by
  let φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval x
  have hx : complexTupleSpectrumPoint x = complexAlgebraPoint φ := by
    simpa only [φ, MvPolynomial.aeval_X] using complexTupleSpectrumPoint_algHom φ
  rw [hx]
  change Spec.map (CommRingCat.ofHom (rationalPolynomialAction (fun i => -q i) η⁻¹).toRingHom)
    (complexAlgebraPoint φ) = _
  calc
    _ = complexAlgebraPoint (φ.comp (rationalPolynomialAction (fun i => -q i) η⁻¹).toAlgHom) :=
      complexAlgebraPoint_comp _ φ
    _ = complexTupleSpectrumPoint (rationalAction q η (fun i => φ (MvPolynomial.X i))) := by
      have he := complexTupleSpectrumPoint_algHom
        (φ.comp (rationalPolynomialAction (fun i => -q i) η⁻¹).toAlgHom)
      rw [rationalAffineObject_complex_action] at he
      exact he.symm
    _ = _ := by congr 1; funext i; simp [φ]

def PuiseuxOriginal.DiagonalConstructible.spectrumObject {n : ℕ} (q : Fin n → ℚ)
    (D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))) (hD : IsConstructible D)
    (hiD : (rationalAffineObject q).Invariant D) : DiagonalConstructible.Object where
  arity := n
  weights := q
  domain := {x | complexTupleSpectrumPoint x ∈ D}
  definable := complex_constructible_domain_definable D hD
  invariant η x := by
    change complexTupleSpectrumPoint (rationalAction q η x) ∈ D ↔ complexTupleSpectrumPoint x ∈ D
    rw [← rationalAffineObject_point_action]
    exact hiD η _

theorem spectrumObject_extension {n : ℕ} (q : Fin n → ℚ)
    (D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))) (hD : IsConstructible D)
    (hiD : (rationalAffineObject q).Invariant D) :
    complexSpectrumExtension (DiagonalConstructible.spectrumObject q D hD hiD).domain
      (DiagonalConstructible.spectrumObject q D hD hiD).definable = D := by
  apply constructible_eq_of_complex_points _ _ (complexSpectrumExtension_constructible _ _) hD
  intro φ
  rw [← complexTupleSpectrumPoint_algHom φ, complexSpectrumExtension_point]
  rfl

theorem spectrumObject_geometricValue {n : ℕ} (q : Fin n → ℚ)
    (D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))) (hD : IsConstructible D)
    (hiD : (rationalAffineObject q).Invariant D) :
    DiagonalConstructible.geometricValue (DiagonalConstructible.spectrumObject q D hD hiD) =
      constructibleClass (rationalAffineObject q) D hD hiD :=
  constructibleClass_set_congr _ _ _ _ _ _ _ (spectrumObject_extension q D hD hiD)

def PuiseuxOriginal.DiagonalConstructible.immersedObject {n : ℕ} (q : Fin n → ℚ)
    {Y : EquivariantVariety.Object} (f : Morphism Y (rationalAffineObject q)) [IsImmersion f.hom] :
    DiagonalConstructible.Object :=
  spectrumObject q (Set.range f.hom)
    (by letI := (rationalAffineObject q).noetherian; exact locallyClosed_constructible_of_noetherian f.hom.isLocallyClosed_range)
    f.range_invariant

theorem immersedObject_geometricValue {n : ℕ} (q : Fin n → ℚ)
    {Y : EquivariantVariety.Object} (f : Morphism Y (rationalAffineObject q)) [IsImmersion f.hom] :
    DiagonalConstructible.geometricValue (DiagonalConstructible.immersedObject q f) = objectClass Y :=
  (spectrumObject_geometricValue q (Set.range f.hom) _ f.range_invariant).trans (constructibleClass_of_immersion f)

end DiamondIntegral.Section5
