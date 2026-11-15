import «section 5».InvariantAffineQuotients
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! The reduced scheme of an arbitrary locally closed affine-spectrum
subset: its open locus inside the reduced scheme of its closure. The
actual immersion has precisely the original scheme-point image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology TopologicalSpace
variable {A : Type*} [CommRing A] [Algebra ℂ A]

def locallyClosedAffineOpen (S : Set (PrimeSpectrum A)) (hS : IsLocallyClosed S) :
    (closedAffineScheme (closure S)).Opens :=
  (closedAffineInclusion (closure S)) ⁻¹ᵁ ⟨coborder S, hS.isOpen_coborder⟩

def locallyClosedAffineScheme (S : Set (PrimeSpectrum A)) (hS : IsLocallyClosed S) : Scheme :=
  (locallyClosedAffineOpen S hS).toScheme

def locallyClosedAffineInclusion (S : Set (PrimeSpectrum A)) (hS : IsLocallyClosed S) :
    locallyClosedAffineScheme S hS ⟶ Spec (.of A) :=
  (locallyClosedAffineOpen S hS).ι ≫ closedAffineInclusion (closure S)

theorem locallyClosedAffineScheme_isReduced (S : Set (PrimeSpectrum A)) (hS : IsLocallyClosed S) :
    AlgebraicGeometry.IsReduced (locallyClosedAffineScheme S hS) := by
  letI := closedAffineScheme_isReduced (closure S)
  exact isReduced_of_isOpenImmersion (locallyClosedAffineOpen S hS).ι

theorem locallyClosedAffineInclusion_isImmersion (S : Set (PrimeSpectrum A)) (hS : IsLocallyClosed S) :
    IsImmersion (locallyClosedAffineInclusion S hS) := by
  letI := closedAffineInclusion_isClosedImmersion (closure S)
  unfold locallyClosedAffineInclusion
  infer_instance

theorem locallyClosedAffineInclusion_range (S : Set (PrimeSpectrum A)) (hS : IsLocallyClosed S) :
    Set.range (locallyClosedAffineInclusion S hS) = S := by
  change Set.range ((locallyClosedAffineOpen S hS).ι ≫ closedAffineInclusion (closure S)) = S
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  change closedAffineInclusion (closure S) ''
    (closedAffineInclusion (closure S) ⁻¹' coborder S) = S
  rw [Set.image_preimage_eq_inter_range, closedAffineInclusion_range _ isClosed_closure,
    coborder_inter_closure]

end DiamondIntegral.Section5
