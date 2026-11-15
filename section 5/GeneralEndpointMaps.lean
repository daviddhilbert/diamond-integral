import «section 5».MonomialEndpointSupports
import «section 5».FiniteGammaParameterControl
import «section 3».GammaGroundMapPreimages

/-! Literal full-RV lifts of cylindrical Gamma families given by actual
endpoint maps. Definability retains their full original-ground graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {Q : Space LRV M} {X : GammaGroundDefSet hc B Q}

def generalEndpointTupleMap (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    GammaGroundMap (X.prod (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin (shape.endpoints+1)))) :=
  GammaGroundMap.tuple (fun i => Fin.lastCases
    (GammaGroundMap.prodSnd X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (fun j => (f j).comp (GammaGroundMap.prodFst X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))) i)

theorem generalEndpointTupleMap_value (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (a : X.prod (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    (generalEndpointTupleMap shape f a).val =
      Fin.snoc (α := fun _ : Fin (shape.endpoints+1) => Values.Gamma (M := M))
        (fun j => (f j ⟨a.val.1,a.property.1⟩).val) a.val.2 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [generalEndpointTupleMap, GammaGroundMap.tuple_value, Fin.lastCases_last,
      Fin.lastCases_castSucc, Fin.snoc_last, Fin.snoc_castSucc] <;> rfl

end DiamondIntegral.Section5
