import «section 5».RationalBasicMorphisms

/-! Mutually rational descriptions of a bijection between basic complex
point loci give an actual isomorphism of their reduced affine schemes.
No algebraic inverse or scheme isomorphism is supplied as an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry
attribute [local instance] basicConstructibleCoordinate_reduced basicConstructibleCoordinate_finiteType

abbrev BasicComplexPoints {n : ℕ}
    (D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n) ℂ)) :=
  {ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ | complexAlgebraPoint ψ ∈ D.toSet}

structure BasicRationalPointIso {n m : ℕ}
    (D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n) ℂ))
    (E : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin m) ℂ)) where
  equiv : BasicComplexPoints D ≃ BasicComplexPoints E
  numerator : Fin m → MvPolynomial (Fin n) ℂ
  denominator : MvPolynomial (Fin n) ℂ
  nonzero : ∀ ψ : BasicComplexPoints D, ψ.val denominator ≠ 0
  equation : ∀ (ψ : BasicComplexPoints D) j,
    (equiv ψ).val (MvPolynomial.X j) * ψ.val denominator = ψ.val (numerator j)
  inverseNumerator : Fin n → MvPolynomial (Fin m) ℂ
  inverseDenominator : MvPolynomial (Fin m) ℂ
  inverse_nonzero : ∀ ψ : BasicComplexPoints E, ψ.val inverseDenominator ≠ 0
  inverse_equation : ∀ (ψ : BasicComplexPoints E) j,
    (equiv.symm ψ).val (MvPolynomial.X j) * ψ.val inverseDenominator = ψ.val (inverseNumerator j)

variable {n m : ℕ}
variable {D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n) ℂ)}
variable {E : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin m) ℂ)}

def BasicRationalPointIso.symm (σ : BasicRationalPointIso D E) : BasicRationalPointIso E D where
  equiv := σ.equiv.symm
  numerator := σ.inverseNumerator
  denominator := σ.inverseDenominator
  nonzero := σ.inverse_nonzero
  equation := σ.inverse_equation
  inverseNumerator := σ.numerator
  inverseDenominator := σ.denominator
  inverse_nonzero := σ.nonzero
  inverse_equation := σ.equation

theorem BasicRationalPointIso.denominatorUnit (σ : BasicRationalPointIso D E) :
    IsUnit (basicConstructibleCoordinateMap D σ.denominator) :=
  (complex_points_isUnit _).mpr (fun φ => σ.nonzero (basicConstructiblePointEquiv D φ))

def BasicRationalPointIso.polynomialMap (σ : BasicRationalPointIso D E) :
    MvPolynomial (Fin m) ℂ →ₐ[ℂ] BasicConstructibleCoordinateRing D :=
  unitRationalAlgebraMap (basicConstructibleCoordinateMap D) σ.numerator σ.denominator σ.denominatorUnit

theorem BasicRationalPointIso.polynomialMap_point (σ : BasicRationalPointIso D E)
    (φ : BasicConstructibleCoordinateRing D →ₐ[ℂ] ℂ) :
    φ.comp σ.polynomialMap = (σ.equiv (basicConstructiblePointEquiv D φ)).val := by
  rw [BasicRationalPointIso.polynomialMap, unitRationalAlgebraMap_point]
  apply MvPolynomial.algHom_ext
  intro j
  simp only [MvPolynomial.aeval_X]
  exact ((eq_div_iff (σ.nonzero (basicConstructiblePointEquiv D φ))).mpr
    (σ.equation (basicConstructiblePointEquiv D φ) j)).symm

def BasicRationalPointIso.algebraMap (σ : BasicRationalPointIso D E) :
    BasicConstructibleCoordinateRing E →ₐ[ℂ] BasicConstructibleCoordinateRing D :=
  complexPointBasicFactor σ.polynomialMap E (fun φ => by
    rw [σ.polynomialMap_point φ]
    exact (σ.equiv (basicConstructiblePointEquiv D φ)).property)

theorem BasicRationalPointIso.algebraMap_coordinateMap (σ : BasicRationalPointIso D E) :
    σ.algebraMap.comp (basicConstructibleCoordinateMap E) = σ.polynomialMap :=
  complexPointBasicFactor_coordinateMap _ _ _

theorem BasicRationalPointIso.algebraMap_point (σ : BasicRationalPointIso D E)
    (φ : BasicConstructibleCoordinateRing D →ₐ[ℂ] ℂ) :
    basicConstructiblePointEquiv E (φ.comp σ.algebraMap) =
      σ.equiv (basicConstructiblePointEquiv D φ) := by
  apply Subtype.ext
  change (φ.comp σ.algebraMap).comp (basicConstructibleCoordinateMap E) = _
  rw [AlgHom.comp_assoc, σ.algebraMap_coordinateMap]
  exact σ.polynomialMap_point φ

def BasicRationalPointIso.algebraEquiv (σ : BasicRationalPointIso D E) :
    BasicConstructibleCoordinateRing D ≃ₐ[ℂ] BasicConstructibleCoordinateRing E :=
  complexPointInverseEquiv σ.symm.algebraMap σ.algebraMap
    (by
      intro φ
      apply (basicConstructiblePointEquiv E).injective
      rw [← AlgHom.comp_assoc, σ.algebraMap_point, σ.symm.algebraMap_point]
      exact σ.equiv.apply_symm_apply _)
    (by
      intro φ
      apply (basicConstructiblePointEquiv D).injective
      rw [← AlgHom.comp_assoc, σ.symm.algebraMap_point, σ.algebraMap_point]
      exact σ.equiv.symm_apply_apply _)

def BasicRationalPointIso.schemeIso (σ : BasicRationalPointIso D E) :
    basicConstructibleScheme D ≅ basicConstructibleScheme E :=
  Scheme.Spec.mapIso σ.algebraEquiv.toRingEquiv.toCommRingCatIso.symm.op

end DiamondIntegral.Section5
