import «section 5».ScalarGammaParameterControl

/-! The full scalar value-torsor graph projects by its literal initial
RV coordinates to the original base, over the unchanged ground. -/
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
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

def groundGammaFunctionGraphLift_projection
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    GammaGroundMap (groundGammaFunctionGraphLift f) X :=
  GammaGroundMap.ofGlobal _ _ (unitTupleInitMap B.real n) (fun u => by
    obtain ⟨x, hx, _⟩ := u.property
    change Fin.init u.val ∈ X.carrier
    exact hx ▸ x.property)

theorem groundGammaFunctionGraphLift_projection_value
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (u : groundGammaFunctionGraphLift f) :
    (groundGammaFunctionGraphLift_projection f u).val = Fin.init u.val := rfl

theorem groundGammaFunctionGraphLift_value
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (u : groundGammaFunctionGraphLift f) :
    (f (groundGammaFunctionGraphLift_projection f u)).val = rvUnitValueHom (u.val (Fin.last n)) := by
  obtain ⟨x, hx, hf⟩ := u.property
  have he : x = groundGammaFunctionGraphLift_projection f u := Subtype.ext hx
  exact (congrArg (fun x : X => (f x).val) he).symm.trans hf

end DiamondIntegral.Section5
