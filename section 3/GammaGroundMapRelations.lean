import «section 3».GammaGroundRelations
import «section 3».GammaGroundRawGraphs
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M} {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}

theorem GammaGroundMap.relation_definable (f : GammaGroundMap A B) :
    GammaGroundRelationDefinable hc ground P Q f.graph := f.graph_definable

end DiamondIntegral.Section3
