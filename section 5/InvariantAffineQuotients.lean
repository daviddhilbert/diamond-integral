import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.FiniteType
import Mathlib.Basic.Complex.Basic

/-! Invariant closed subsets of an affine scheme carry their actual
reduced closed-subscheme structure. Algebra actions descend to their
coordinate rings, with the original quotient maps equivariant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {G : Type*} [Group G]

theorem invariantClosedIdeal_stable (ρ : G →* (A ≃ₐ[ℂ] A))
    (Z : Set (PrimeSpectrum A))
    (hZ : ∀ g x, PrimeSpectrum.comap (ρ g).toRingHom x ∈ Z ↔ x ∈ Z) :
    ∀ g, (PrimeSpectrum.vanishingIdeal Z).map (ρ g).toRingHom = PrimeSpectrum.vanishingIdeal Z := by
  have hmem (g : G) {a : A} (ha : a ∈ PrimeSpectrum.vanishingIdeal Z) :
      ρ g a ∈ PrimeSpectrum.vanishingIdeal Z := by
    apply (PrimeSpectrum.mem_vanishingIdeal Z _).mpr
    intro x hx
    exact (PrimeSpectrum.mem_vanishingIdeal Z a).mp ha
      (PrimeSpectrum.comap (ρ g).toRingHom x) ((hZ g x).mpr hx)
  intro g
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    exact fun a ha => hmem g ha
  · intro a ha
    have h := Ideal.mem_map_of_mem (ρ g).toRingHom (hmem g⁻¹ ha)
    change ρ g (ρ g⁻¹ a) ∈ (PrimeSpectrum.vanishingIdeal Z).map (ρ g).toRingHom at h
    rw [map_inv] at h
    exact (ρ g).apply_symm_apply a ▸ h

def invariantIdealQuotientAction (ρ : G →* (A ≃ₐ[ℂ] A)) (I : Ideal A)
    (hI : ∀ g, I.map (ρ g).toRingHom = I) : G →* ((A ⧸ I) ≃ₐ[ℂ] (A ⧸ I)) where
  toFun g := Ideal.quotientEquivAlg I I (ρ g) (hI g).symm
  map_one' := by
    ext a
    refine Quotient.inductionOn' a ?_
    intro a
    change Ideal.Quotient.mk I (ρ 1 a) = Ideal.Quotient.mk I a
    rw [map_one]
    rfl
  map_mul' g h := by
    ext a
    refine Quotient.inductionOn' a ?_
    intro a
    change Ideal.Quotient.mk I (ρ (g * h) a) = Ideal.Quotient.mk I (ρ g (ρ h a))
    rw [map_mul]
    rfl

theorem invariantIdealQuotientAction_mk (ρ : G →* (A ≃ₐ[ℂ] A)) (I : Ideal A)
    (hI : ∀ g, I.map (ρ g).toRingHom = I) (g : G) (a : A) :
    invariantIdealQuotientAction ρ I hI g (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I (ρ g a) := rfl

def closedAffineScheme (Z : Set (PrimeSpectrum A)) : Scheme :=
  Spec (.of (A ⧸ PrimeSpectrum.vanishingIdeal Z))

theorem closedAffineScheme_isReduced (Z : Set (PrimeSpectrum A)) :
    AlgebraicGeometry.IsReduced (closedAffineScheme Z) := by
  letI : _root_.IsReduced (A ⧸ PrimeSpectrum.vanishingIdeal Z) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (PrimeSpectrum.isRadical_vanishingIdeal Z)
  unfold closedAffineScheme
  infer_instance

theorem closedAffineCoordinate_finiteType [Algebra.FiniteType ℂ A] (Z : Set (PrimeSpectrum A)) :
    Algebra.FiniteType ℂ (A ⧸ PrimeSpectrum.vanishingIdeal Z) := inferInstance

def closedAffineInclusion (Z : Set (PrimeSpectrum A)) : closedAffineScheme Z ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z)))

theorem closedAffineInclusion_isClosedImmersion (Z : Set (PrimeSpectrum A)) :
    IsClosedImmersion (closedAffineInclusion Z) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem closedAffineInclusion_range (Z : Set (PrimeSpectrum A)) (hZ : IsClosed Z) :
    Set.range (closedAffineInclusion Z) = Z := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z))) = Z
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq]

end DiamondIntegral.Section5
