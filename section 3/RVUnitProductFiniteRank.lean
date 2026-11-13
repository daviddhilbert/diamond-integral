import «section 3».RVUnitProductTuples
import «section 3».GammaGroundRVFiniteMapRank
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

/-- A finite label map bounds the actual algebraic rank of a product
point, after transporting through its checked RV tuple presentation. -/
theorem gammaGroundRVUnitProduct_rank_le_of_finite_map
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hγ : GammaRVAlgebraicityInput (M := M) κ) (hsmall : Cardinal.mk B.real < κ)
    (X : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m)))
    (Y : GammaGroundDefSet hc B (rawRVSpace (M := M) k))
    (f : GammaGroundMap X Y) (hf : f.FiniteFibres) (x : X) :
    rvTupleRank hc hex B.real (rvUnitProductTuple x.val) ≤ k := by
  let e := gammaGroundRVUnitProductTupleBijection X
  let g := f.comp e.symm.map
  have hg : g.FiniteFibres := hf.comp (GammaGroundMap.finiteFibres_of_injective e.symm.bijective.1)
  have hh := gammaGroundRVTupleRank_le_of_finite_map hex hκ hγ hsmall g hg (e.map x)
  exact hh.trans (rvTupleRank_le_arity hc hex B.real (g (e.map x)).val)
end DiamondIntegral.Section3
