import «section 5».ComplexConstructiblePoints
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.LocalProperties.Reduced

/-! The reduced affine scheme of a basic constructible set. Its
coordinate algebra is the localization of the radical equation quotient.
The actual inclusion has exactly the prescribed scheme-point image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {A : Type*} [CommRing A] [Algebra ℂ A]

def basicConstructibleIdeal (D : PrimeSpectrum.BasicConstructibleSetData A) : Ideal A :=
  (Ideal.span (Set.range D.g)).radical

abbrev BasicClosedCoordinateRing (D : PrimeSpectrum.BasicConstructibleSetData A) :=
  A ⧸ basicConstructibleIdeal D

abbrev BasicConstructibleCoordinateRing (D : PrimeSpectrum.BasicConstructibleSetData A) :=
  Localization.Away (Ideal.Quotient.mk (basicConstructibleIdeal D) D.f)

theorem basicClosedCoordinate_reduced (D : PrimeSpectrum.BasicConstructibleSetData A) :
    IsReduced (BasicClosedCoordinateRing D) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
attribute [local instance] basicClosedCoordinate_reduced

theorem basicConstructibleCoordinate_reduced (D : PrimeSpectrum.BasicConstructibleSetData A) :
    IsReduced (BasicConstructibleCoordinateRing D) := inferInstance

theorem basicConstructibleCoordinate_finiteType [Algebra.FiniteType ℂ A]
    (D : PrimeSpectrum.BasicConstructibleSetData A) :
    Algebra.FiniteType ℂ (BasicConstructibleCoordinateRing D) := inferInstance

def basicConstructibleCoordinateMap (D : PrimeSpectrum.BasicConstructibleSetData A) :
    A →ₐ[ℂ] BasicConstructibleCoordinateRing D :=
  (IsScalarTower.toAlgHom ℂ (BasicClosedCoordinateRing D) (BasicConstructibleCoordinateRing D)).comp
    (Ideal.Quotient.mkₐ ℂ (basicConstructibleIdeal D))

theorem basicConstructibleCoordinateMap_equation (D : PrimeSpectrum.BasicConstructibleSetData A)
    (i : Fin D.n) : basicConstructibleCoordinateMap D (D.g i) = 0 := by
  change algebraMap (BasicClosedCoordinateRing D) (BasicConstructibleCoordinateRing D)
    (Ideal.Quotient.mk (basicConstructibleIdeal D) (D.g i)) = 0
  have h : D.g i ∈ basicConstructibleIdeal D :=
    Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

theorem basicConstructibleCoordinateMap_denominator (D : PrimeSpectrum.BasicConstructibleSetData A) :
    IsUnit (basicConstructibleCoordinateMap D D.f) := by
  change IsUnit (algebraMap (BasicClosedCoordinateRing D) (BasicConstructibleCoordinateRing D)
    (Ideal.Quotient.mk (basicConstructibleIdeal D) D.f))
  exact IsLocalization.Away.algebraMap_isUnit _

theorem basicConstructiblePoint_mem (D : PrimeSpectrum.BasicConstructibleSetData A)
    (φ : BasicConstructibleCoordinateRing D →ₐ[ℂ] ℂ) :
    complexAlgebraPoint (φ.comp (basicConstructibleCoordinateMap D)) ∈ D.toSet := by
  constructor
  · rintro _ ⟨i, rfl⟩
    change φ (basicConstructibleCoordinateMap D (D.g i)) = 0
    rw [basicConstructibleCoordinateMap_equation, map_zero]
  · have h := (basicConstructibleCoordinateMap_denominator D).map φ.toRingHom
    simpa [PrimeSpectrum.mem_zeroLocus, complexAlgebraPoint, RingHom.mem_ker] using
      (isUnit_iff_ne_zero.mp h)

def basicConstructibleScheme (D : PrimeSpectrum.BasicConstructibleSetData A) : Scheme :=
  Spec (.of (BasicConstructibleCoordinateRing D))

theorem basicConstructibleScheme_isReduced (D : PrimeSpectrum.BasicConstructibleSetData A) :
    AlgebraicGeometry.IsReduced (basicConstructibleScheme D) := by
  letI := basicConstructibleCoordinate_reduced D
  unfold basicConstructibleScheme
  infer_instance

def basicConstructibleInclusion (D : PrimeSpectrum.BasicConstructibleSetData A) :
    basicConstructibleScheme D ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (basicConstructibleCoordinateMap D).toRingHom)

theorem basicConstructibleInclusion_isImmersion (D : PrimeSpectrum.BasicConstructibleSetData A) :
    IsImmersion (basicConstructibleInclusion D) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (basicConstructibleIdeal D)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (BasicClosedCoordinateRing D) (BasicConstructibleCoordinateRing D)))) :=
    IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk (basicConstructibleIdeal D) D.f)
  change IsImmersion (Spec.map (CommRingCat.ofHom
    ((algebraMap (BasicClosedCoordinateRing D) (BasicConstructibleCoordinateRing D)).comp
      (Ideal.Quotient.mk (basicConstructibleIdeal D)))))
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

theorem basicConstructibleInclusion_range (D : PrimeSpectrum.BasicConstructibleSetData A) :
    Set.range (basicConstructibleInclusion D) = D.toSet := by
  let I := basicConstructibleIdeal D
  let q := Ideal.Quotient.mk I D.f
  change Set.range (PrimeSpectrum.comap
    ((algebraMap (A ⧸ I) (Localization.Away q)).comp (Ideal.Quotient.mk I))) = _
  rw [PrimeSpectrum.comap_comp, Set.range_comp,
    PrimeSpectrum.localization_away_comap_range (Localization.Away q) q]
  have he : (PrimeSpectrum.basicOpen q : Set (PrimeSpectrum (A ⧸ I))) =
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' (PrimeSpectrum.basicOpen D.f : Set _) := rfl
  rw [he, Set.image_preimage_eq_inter_range, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]
  have hI : PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (Set.range D.g) := by
    dsimp only [I, basicConstructibleIdeal]
    rw [PrimeSpectrum.zeroLocus_radical, PrimeSpectrum.zeroLocus_span]
  rw [hI]
  ext x
  simp only [Set.mem_inter_iff, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.mem_zeroLocus,
    Set.mem_sdiff, PrimeSpectrum.BasicConstructibleSetData.toSet, Set.singleton_subset_iff]
  tauto

end DiamondIntegral.Section5
