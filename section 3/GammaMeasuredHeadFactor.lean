import «section 3».GammaMeasuredNormalizedPoint
import «section 3».GammaGroundMeasuredRVProducts
import «section 3».GammaGroundRVFamilyObjects

/-! Deleting an admissible final volume coordinate retains the entire
combined Gamma weight on the head, including when that head has degree
zero. The source then factors through the genuine degree-one point. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

def gammaRVHeadMap (U : GammaGroundRVObject hc B (n+1)) :=
  (gammaGroundRVSelectCoordinates (Fin.castSucc : Fin n → Fin (n+1))
    (GammaGroundDefSet.univ hc B (rawRVSpace (n+1)))).comp U.volume

def gammaMeasuredHeadFactor (U : GammaGroundMeasuredRVObject hc B (n+1))
    (hfin : (gammaRVHeadMap U.underlying).FiniteFibres) : GammaGroundMeasuredRVObject hc B n :=
  (⟨U.underlying.arity,U.underlying.domain,gammaRVHeadMap U.underlying,hfin,
    fun u i => U.underlying.nonzero u i.castSucc⟩ : GammaGroundRVObject hc B n).withCombinedWeight U.combinedWeightForm

def gammaMeasuredHeadPointHom (U : GammaGroundMeasuredRVObject hc B (n+1))
    (hfin : (gammaRVHeadMap U.underlying).FiniteFibres) : GammaGroundMeasuredRVHom U
      ((gammaMeasuredHeadFactor U hfin).product (gammaMeasuredPointZeroArity hc B)) where
  bijection := (gammaGroundRVProductRightUnitBijection (gammaMeasuredHeadFactor U hfin).underlying).symm
  preserves u := by
    let H := gammaMeasuredHeadFactor U hfin
    let P := gammaMeasuredPointZeroArity hc B
    let e := (gammaGroundRVProductRightUnitBijection H.underlying).symm
    change U.combinedWeight u = (H.product P).combinedWeight (e.map u)
    rw [GammaGroundMeasuredRVObject.product_combined,gammaMeasuredPointZeroArity_weight,mul_one]
    have hl : gammaGroundMeasuredRVProductLeft H P (e.map u) = u :=
      (gammaGroundRVProductRightUnitBijection H.underlying).map.apply_inverse
        (gammaGroundRVProductRightUnitBijection H.underlying).bijective u
    rw [hl]
    exact ((GammaGroundRVObject.withCombinedWeight_value (gammaMeasuredHeadFactor U hfin).underlying U.combinedWeightForm u).trans
      (U.combinedWeightForm_value u)).symm

end DiamondIntegral.Section3
