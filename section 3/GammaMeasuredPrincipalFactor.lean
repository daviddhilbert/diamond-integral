import «section 3».GammaMeasuredHeadFactor
import «section 3».GammaGroundRVPackPairs

/-! The weighted head accounts for an elementary point/cone replacement
in every degree. In degree one it is a genuine weighted degree-zero
object, rather than an unweighted coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

def gammaMeasuredHeadConeHom
    (U W : GammaGroundMeasuredRVObject hc B (n+1))
    (hfin : (gammaRVHeadMap U.underlying).FiniteFibres)
    (e : GammaGroundBijection W.underlying.domain
      (U.underlying.domain.prod (gammaGroundMeasuredRVPositive hc B).underlying.domain))
    (hw : ∀ w, W.combinedWeight w =
      U.combinedWeight ⟨(e.map w).val.1,(e.map w).property.1⟩ *
        (gammaGroundMeasuredRVPositive hc B).combinedWeight ⟨(e.map w).val.2,(e.map w).property.2⟩) :
    GammaGroundMeasuredRVHom W ((gammaMeasuredHeadFactor U hfin).product (gammaGroundMeasuredRVPositive hc B)) where
  bijection := (gammaGroundRVPackBijection (gammaMeasuredHeadFactor U hfin).underlying.domain
    (gammaGroundMeasuredRVPositive hc B).underlying.domain).comp e
  preserves w := by
    let a : U.underlying.domain := ⟨(e.map w).val.1,(e.map w).property.1⟩
    let b : (gammaGroundMeasuredRVPositive hc B).underlying.domain := ⟨(e.map w).val.2,(e.map w).property.2⟩
    change W.combinedWeight w = ((gammaMeasuredHeadFactor U hfin).product (gammaGroundMeasuredRVPositive hc B)).combinedWeight
      (gammaGroundRVPackPair (gammaMeasuredHeadFactor U hfin).underlying.domain (gammaGroundMeasuredRVPositive hc B).underlying.domain a b)
    have hh : (gammaMeasuredHeadFactor U hfin).combinedWeight a = U.combinedWeight a :=
      (GammaGroundRVObject.withCombinedWeight_value (gammaMeasuredHeadFactor U hfin).underlying U.combinedWeightForm a).trans
        (U.combinedWeightForm_value a)
    exact (hw w).trans ((congrArg (fun z => z * (gammaGroundMeasuredRVPositive hc B).combinedWeight b) hh.symm).trans
      (GammaGroundMeasuredRVObject.product_combined_pair (gammaMeasuredHeadFactor U hfin) (gammaGroundMeasuredRVPositive hc B) a b).symm)

theorem gammaMeasuredPrincipalFactor
    (U W : GammaGroundMeasuredRVObject hc B (n+1))
    (hfin : (gammaRVHeadMap U.underlying).FiniteFibres)
    (e : GammaGroundBijection W.underlying.domain
      (U.underlying.domain.prod (gammaGroundMeasuredRVPositive hc B).underlying.domain))
    (hw : ∀ w, W.combinedWeight w =
      U.combinedWeight ⟨(e.map w).val.1,(e.map w).property.1⟩ *
        (gammaGroundMeasuredRVPositive hc B).combinedWeight ⟨(e.map w).val.2,(e.map w).property.2⟩) :
    ∃ H : GammaGroundMeasuredRVObject hc B n,
      Nonempty (GammaGroundMeasuredRVHom U (H.product (gammaMeasuredPointZeroArity hc B))) ∧
      Nonempty (GammaGroundMeasuredRVHom W (H.product (gammaGroundMeasuredRVPositive hc B))) :=
  ⟨gammaMeasuredHeadFactor U hfin,⟨gammaMeasuredHeadPointHom U hfin⟩,⟨gammaMeasuredHeadConeHom U W hfin e hw⟩⟩

end DiamondIntegral.Section3
