import «section 3».CompletionFunctor
import «section 3».VFPositiveColimitCategory
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def vfGroupDiagram : ℕ ⥤ AddCommGrpCat := vfPositiveDiagram C ⋙ additiveCompletionFunctor

def vfGroupCocone : Cocone (vfGroupDiagram C) :=
  additiveCompletionFunctor.mapCocone (vfPositiveCocone C hc hv)

def vfGroupIsColimit : IsColimit (vfGroupCocone C hc hv) :=
  isColimitOfPreserves additiveCompletionFunctor (vfPositiveIsColimit C hc hv)

theorem vfGroupCocone_class {k : ℕ} (U : VFObject (M := M) (C.base : Set M) k) :
    ((vfGroupCocone C hc hv).ι.app k).hom (Algebra.GrothendieckAddGroup.of (vfClass U)) =
      Algebra.GrothendieckAddGroup.of (vfSemiringClass C hc hv U) := by
  change additiveCompletionMap (vfKPlusToSemiring C hc hv) (Algebra.GrothendieckAddGroup.of (vfClass U)) = _
  rw [additiveCompletionMap_of, vfKPlusToSemiring_class]

end DiamondIntegral.Section3
