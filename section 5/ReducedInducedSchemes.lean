import «section 5».ReducedImmersionIsomorphisms
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Reduced induced structures on arbitrary closed and locally closed
scheme subsets, including reduction of an arbitrary scheme. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X : Scheme.{u}}

def reducedClosedScheme (Z : Closeds X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal Z).subscheme

def reducedClosedInclusion (Z : Closeds X) : reducedClosedScheme Z ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

theorem reducedClosedScheme_isReduced (Z : Closeds X) :
    AlgebraicGeometry.IsReduced (reducedClosedScheme Z) := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  letI (U : X.affineOpens) : AlgebraicGeometry.IsReduced (I.subschemeCover.openCover.X U) := by
    letI : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp
        (PrimeSpectrum.isRadical_vanishingIdeal _)
    change AlgebraicGeometry.IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact AlgebraicGeometry.IsReduced.of_openCover (reducedClosedScheme Z) I.subschemeCover.openCover

theorem reducedClosedInclusion_isClosedImmersion (Z : Closeds X) :
    IsClosedImmersion (reducedClosedInclusion Z) := by
  unfold reducedClosedInclusion
  infer_instance

theorem reducedClosedInclusion_range (Z : Closeds X) :
    Set.range (reducedClosedInclusion Z) = Z := by
  exact (Scheme.IdealSheafData.range_subschemeι (Scheme.IdealSheafData.vanishingIdeal Z)).trans (by simp)

attribute [local instance] reducedClosedScheme_isReduced reducedClosedInclusion_isClosedImmersion

def reducedLocallyClosedOpen (S : Set X) (hS : IsLocallyClosed S) :
    (reducedClosedScheme (Closeds.closure S)).Opens :=
  reducedClosedInclusion (Closeds.closure S) ⁻¹ᵁ ⟨coborder S, hS.isOpen_coborder⟩

def reducedLocallyClosedScheme (S : Set X) (hS : IsLocallyClosed S) : Scheme :=
  (reducedLocallyClosedOpen S hS).toScheme

def reducedLocallyClosedInclusion (S : Set X) (hS : IsLocallyClosed S) :
    reducedLocallyClosedScheme S hS ⟶ X :=
  (reducedLocallyClosedOpen S hS).ι ≫ reducedClosedInclusion (Closeds.closure S)

theorem reducedLocallyClosedScheme_isReduced (S : Set X) (hS : IsLocallyClosed S) :
    AlgebraicGeometry.IsReduced (reducedLocallyClosedScheme S hS) :=
  isReduced_of_isOpenImmersion (reducedLocallyClosedOpen S hS).ι

theorem reducedLocallyClosedInclusion_isImmersion (S : Set X) (hS : IsLocallyClosed S) :
    IsImmersion (reducedLocallyClosedInclusion S hS) := by
  unfold reducedLocallyClosedInclusion
  infer_instance

theorem reducedLocallyClosedInclusion_range (S : Set X) (hS : IsLocallyClosed S) :
    Set.range (reducedLocallyClosedInclusion S hS) = S := by
  change Set.range ((reducedLocallyClosedOpen S hS).ι ≫
    reducedClosedInclusion (Closeds.closure S)) = S
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  change reducedClosedInclusion (Closeds.closure S) ''
    (reducedClosedInclusion (Closeds.closure S) ⁻¹' coborder S) = S
  rw [Set.image_preimage_eq_inter_range, reducedClosedInclusion_range]
  exact coborder_inter_closure

def schemeReduction (X : Scheme.{u}) : Scheme := reducedClosedScheme (⊤ : Closeds X)

def schemeReductionMap (X : Scheme.{u}) : schemeReduction X ⟶ X :=
  reducedClosedInclusion ⊤

theorem schemeReduction_isReduced (X : Scheme.{u}) : AlgebraicGeometry.IsReduced (schemeReduction X) :=
  reducedClosedScheme_isReduced ⊤

theorem schemeReductionMap_isClosedImmersion (X : Scheme.{u}) :
    IsClosedImmersion (schemeReductionMap X) := reducedClosedInclusion_isClosedImmersion ⊤

theorem schemeReductionMap_surjective (X : Scheme.{u}) : Function.Surjective (schemeReductionMap X) := by
  rw [← Set.range_eq_univ]
  exact reducedClosedInclusion_range ⊤

end DiamondIntegral.Section5
