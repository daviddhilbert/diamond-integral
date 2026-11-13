import «section 3».RVProductDegreeBound
import «section 3».GammaGroundRVUnitRES
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m k : ℕ}

/-- A product with a finite RV[k] label has an actual RES[k-m] factor.
This transports label degree rather than identifying it with ambient arity. -/
theorem gammaGroundRVProduct_RES_factor
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hγ : GammaRVAlgebraicityInput (M := M) κ) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m))) (hG : G.carrier.Nonempty)
    (Y : GammaGroundDefSet hc B (rawRVSpace (M := M) k))
    (f : GammaGroundMap (R.prod (gammaGroundRVUnitGammaPreimage G)) Y) (hf : f.FiniteFibres) :
    ∃ U : GammaGroundRESObject hc B (k-m), Nonempty (GammaGroundBijection R U.obj.domain) :=
  gammaGroundRVUnit_RES_of_rank_bound hex hκ hs hsmall R hR
    (gammaGroundRVProduct_residue_rank_le_sub hex hκ hs h00 hγ hsmall R G hG Y f hf)
end DiamondIntegral.Section3
