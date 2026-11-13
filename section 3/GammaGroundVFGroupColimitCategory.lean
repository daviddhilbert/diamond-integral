import «section 3».CompletionFunctor
import «section 3».GammaGroundVFPositiveColimitCategory
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [TopologicalSpace (Section2.VF M)]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M))

def gammaGroundVFGroupDiagram : ℕ ⥤ AddCommGrpCat :=
  gammaGroundVFPositiveDiagram hc ground ⋙ additiveCompletionFunctor

def gammaGroundVFGroupCocone : Cocone (gammaGroundVFGroupDiagram hc ground) :=
  additiveCompletionFunctor.mapCocone (gammaGroundVFPositiveCocone hc ground)

def gammaGroundVFGroupIsColimit : IsColimit (gammaGroundVFGroupCocone hc ground) :=
  isColimitOfPreserves additiveCompletionFunctor (gammaGroundVFPositiveIsColimit hc ground)

theorem gammaGroundVFGroupCocone_class {k : ℕ} (U : GammaGroundVFObject hc ground k) :
    ((gammaGroundVFGroupCocone hc ground).ι.app k).hom (Algebra.GrothendieckAddGroup.of (gammaGroundVFClass U)) =
      Algebra.GrothendieckAddGroup.of (gammaGroundFiniteVFClass (.ofBound U)) := by
  change additiveCompletionMap gammaGroundVFToFiniteKPlus (Algebra.GrothendieckAddGroup.of (gammaGroundVFClass U)) = _
  rw [additiveCompletionMap_of, gammaGroundVFToFiniteKPlus_class]

end DiamondIntegral.Section3
