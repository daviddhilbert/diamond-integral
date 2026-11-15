import «section 5».DiagonalGeometricValues
import «section 5».VarietyMorphisms
import «section 5».ImmersedPresentationLoci
import Mathlib.Algebra.MvPolynomial.Equiv

/-! The geometric value of the zero-coordinate one-point object is
the actual multiplicative unit in the variety presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety Topology
open PuiseuxOriginal
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem constructibleClass_univ (X : EquivariantVariety.Object) :
    constructibleClass X Set.univ IsConstructible.univ (Object.Invariant.univ X) = objectClass X := by
  let f := Morphism.id X
  letI : IsImmersion f.hom := inferInstanceAs (IsImmersion (𝟙 X.scheme))
  let c := (singletonImmersedPresentation f).changeLocus Set.range_id
  rw [constructibleClass_eq_presentation _ _ _ _ c]
  change ((singletonImmersedPresentation f).changeLocus Set.range_id).value = _
  rw [ImmersedPresentation.changeLocus_value]
  simp [ImmersedPresentation.value, singletonImmersedPresentation]

theorem complexSpectrumExtension_univ {n : ℕ}
    (hD : (Set.univ : Set ℂ).Definable FirstOrder.Language.ring (Set.univ : Set (Fin n → ℂ))) :
    complexSpectrumExtension Set.univ hD = Set.univ := by
  apply constructible_eq_of_complex_points _ _ (complexSpectrumExtension_constructible _ _) IsConstructible.univ
  intro φ
  rw [← complexTupleSpectrumPoint_algHom φ, complexSpectrumExtension_point]
  rfl

theorem rationalAffineObject_zero_toC_isIso :
    IsIso (rationalAffineObject (Fin.elim0 : Fin 0 → ℚ)).toC := by
  let e := (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)).symm.toCommRingCatIso
  have he : e.hom = CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin 0) ℂ)) := by
    ext c
    simp [e]
  haveI : IsIso (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin 0) ℂ))) := by
    rw [← he]
    infer_instance
  exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin 0) ℂ)))))

theorem PuiseuxOriginal.DiagonalConstructible.geometricValue_unit :
    geometricValue unit = (1 : EquivariantVariety.Ring) := by
  have he := complexSpectrumExtension_univ (n := 0) unit.definable
  have hc := constructibleClass_set_congr (rationalAffineObject (Fin.elim0 : Fin 0 → ℚ))
    (complexSpectrumExtension Set.univ unit.definable) Set.univ
    (complexSpectrumExtension_constructible _ _) IsConstructible.univ
    (complexSpectrumExtension_invariant _ _ _ unit.invariant) (Object.Invariant.univ _) he
  exact hc.trans ((constructibleClass_univ _).trans
    (EquivariantVariety.objectClass_unit _ rationalAffineObject_zero_toC_isIso))

end DiamondIntegral.Section5
