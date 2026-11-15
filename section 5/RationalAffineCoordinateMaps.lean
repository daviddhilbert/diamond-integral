import «section 5».RationalAffineVarieties
import «section 5».VarietyMorphisms

/-! Coordinate maps respecting rational weights are actual equivariant
complex scheme morphisms. This includes projections and coordinate changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety

theorem rationalPolynomialAction_rename {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)
    (f : Fin n → Fin m) (hf : ∀ i, r (f i) = q i) (η : CompatibleRoots ℂ) :
    (rationalPolynomialAction r η).toAlgHom.comp (MvPolynomial.rename f) =
      (MvPolynomial.rename f).comp (rationalPolynomialAction q η).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalPolynomialAction, rationalPolynomialEquiv, rationalPolynomialHom, hf]

def rationalAffineCoordinateMap {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)
    (f : Fin n → Fin m) (hf : ∀ i, r (f i) = q i) :
    Morphism (rationalAffineObject r) (rationalAffineObject q) where
  hom := Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := ℂ) f).toRingHom)
  overC := by
    change Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := ℂ) f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))) = _
    rw [← Spec.map_comp]
    congr 1
    ext c
    simp
  equivariant η := by
    change Spec.map (CommRingCat.ofHom (rationalPolynomialAction (fun j => -r j) η⁻¹).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := ℂ) f).toRingHom) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := ℂ) f).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (rationalPolynomialAction (fun i => -q i) η⁻¹).toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      (rationalPolynomialAction_rename (fun i => -q i) (fun j => -r j) f
        (fun i => congrArg Neg.neg (hf i)) η⁻¹)

def rationalAffineLeft {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ) :
    Morphism (rationalAffineObject (Fin.append q r)) (rationalAffineObject q) :=
  rationalAffineCoordinateMap q (Fin.append q r) (Fin.castAdd m) (fun i => Fin.append_left q r i)

def rationalAffineRight {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ) :
    Morphism (rationalAffineObject (Fin.append q r)) (rationalAffineObject r) :=
  rationalAffineCoordinateMap r (Fin.append q r) (Fin.natAdd n) (fun i => Fin.append_right q r i)

end DiamondIntegral.Section5
