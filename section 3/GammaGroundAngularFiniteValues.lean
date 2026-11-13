import «section 3».GammaGroundRVAngularCoordinates
import «section 3».GammaGroundFiniteValuePoints
import «section 3».RVUnitGammaMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Each value of an active angular coordinate at an actual cell point
is Gamma-definable over the original mixed ground. -/
theorem gammaGroundRVAngularCell_residue_values_definable
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (x : X) :
    ∀ j, GammaDefinableClosureAtBase B (rvUnitTupleValues (E.coordinateEquiv K x.val).1 j) := by
  let F := (rvUnitGammaMap hc B.real K.zeroArity).comp
    ((universalProductFst (rawRVUnitSpace K.zeroArity) (rawRVUnitSpace K.freeArity) B.real).comp
      (rvAngularGlobalCoordinateMap E K B.real))
  let v := GammaGroundMap.ofGlobal X
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin K.zeroArity))) F
    (fun _ => Set.mem_univ _)
  have he : v.image.carrier = (fun y => rvUnitTupleValues (E.coordinateEquiv K y).1) '' X.carrier := by
    ext γ
    exact ⟨fun ⟨y,hy⟩ => ⟨y.val,y.property,hy⟩,fun ⟨y,hy,he⟩ => ⟨⟨y,hy⟩,he⟩⟩
  have hfin : v.image.carrier.Finite := by
    rw [he]
    exact E.residue_tuple_values_finite K
  exact gammaGroundGamma_finite_tuple_point_definable v.image hfin
    (rvUnitTupleValues (E.coordinateEquiv K x.val).1) ⟨x,rfl⟩
end DiamondIntegral.Section3
