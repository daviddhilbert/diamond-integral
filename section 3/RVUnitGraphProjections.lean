import «section 3».GammaGroundRVUnitGraphs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m : ℕ}
variable {A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
variable {D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)}

theorem GammaGroundMap.unitGraphMap_input (f : GammaGroundMap A D) (a : A) :
    (f.unitGraphMap a).val ∘ Fin.castAdd m = a.val := by
  funext i
  exact Fin.append_left a.val (f a).val i

theorem GammaGroundMap.unitGraphMap_output (f : GammaGroundMap A D) (a : A) :
    (f.unitGraphMap a).val ∘ Fin.natAdd n = (f a).val := by
  funext i
  exact Fin.append_right a.val (f a).val i
end DiamondIntegral.Section3
