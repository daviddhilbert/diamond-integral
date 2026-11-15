import «section 5».MonomialPieceScalarGraphs

/-! The actual monomial coordinate map realizes the product rectangle,
with its literal value formula retained in the definable bijection. -/
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

def GroundMonomialPiece.coordinateMap (P : GroundMonomialPiece X) :
    GammaGroundMap P.source (P.residue.prod (gammaGroundRVUnitGammaPreimage P.gamma)) :=
  GammaGroundMap.ofGlobal _ _ (rvAngularGlobalCoordinateMap P.cell P.split B.real)
    (fun x => (P.coordinate_mem_iff x.val).mpr x.property)

theorem GroundMonomialPiece.coordinateMap_value (P : GroundMonomialPiece X) (x : P.source) :
    (P.coordinateMap x).val = P.cell.coordinateEquiv P.split x.val := rfl

def GroundMonomialPiece.coordinateBijection (P : GroundMonomialPiece X) :
    GammaGroundBijection P.source (P.residue.prod (gammaGroundRVUnitGammaPreimage P.gamma)) where
  map := P.coordinateMap
  bijective := by
    constructor
    · intro x y he
      exact Subtype.ext ((P.cell.coordinateEquiv P.split).injective (congrArg Subtype.val he))
    · intro y
      have hy : y.val ∈ P.cell.coordinateEquiv P.split '' P.source.carrier :=
        P.coordinate_image.symm ▸ y.property
      obtain ⟨x, hx, he⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩

end DiamondIntegral.Section5
