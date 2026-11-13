import «section 3».GammaGroundRVUnitSingletons
import «section 3».GammaGroundMapImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ} {P : Space LRV M}

/-- Definable images of an actual singleton retain original-ground
definability of every RV coordinate. -/
theorem gammaGroundRVUnitMap_subsingleton_image_point_definable
    (R : GammaGroundDefSet hc B P) [Subsingleton R]
    (S : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (f : GammaGroundMap R S) (r : R) :
    ∀ i, DefinableClosureAtBase B .rv (rvUnitValues (f r).val i) := by
  letI : Subsingleton f.image := ⟨fun y z => by
    obtain ⟨a,ha⟩ := y.property
    obtain ⟨b,hb⟩ := z.property
    exact Subtype.ext (ha.symm.trans ((congrArg (fun a : R => (f a).val) (Subsingleton.elim a b)).trans hb))⟩
  exact gammaGroundRVUnit_subsingleton_point_definable f.image (f.toImage r)
end DiamondIntegral.Section3
