import «section 3».GammaGroundGammaSinglePiece
import «section 3».RVUnitGammaCodeBijection
import «section 3».RVProductRESFactor
import «section 3».GammaGroundUnmeasuredTensorMap
import «section 3».GammaGroundBijectionProducts
import Section4.EarlierRVInputs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m k : ℕ}

/-- Every nonempty product chart with an actual RV[k] label has a
preimage under the concrete unmeasured tensor map, over the original base. -/
theorem gammaGroundUnmeasuredTensor_chart_preimage {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (W : GammaGroundRVObject hc B k) (hW : W.domain.carrier.Nonempty)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundGammaPiece hc B m)
    (F : GammaGroundBijection W.domain (R.prod (gammaGroundRVUnitGammaPreimage G))) :
    ∃ t : GammaGroundUnmeasuredPositiveTensor hc B,
      gammaGroundUnmeasuredTensorMap t = gammaGroundRVSemiringClass W := by
  let hex := rvExchangeInput_of_earlier hκ hs h00
  let hγ := gammaRVAlgebraicityInput_of_earlier hκ hs h00
  obtain ⟨w,hw⟩ := hW
  let q := F.map ⟨w,hw⟩
  let r : R := ⟨q.val.1,q.property.1⟩
  have hG : G.carrier.Nonempty := ⟨rvUnitTupleValues q.val.2,q.property.2⟩
  let f := W.volume.comp F.symm.map
  have hf : f.FiniteFibres := W.finite.comp (GammaGroundMap.finiteFibres_of_injective F.symm.bijective.1)
  obtain ⟨U,⟨eR⟩⟩ := gammaGroundRVProduct_RES_factor hex hκ hs h00 hγ hsmall R hR G hG _ f hf
  have hdeg := gammaGroundRVProduct_residue_rank_add_le hex hκ hs h00 hγ hsmall R G hG _ f hf r
  have hmk : m ≤ k := (Nat.le_add_left m _).trans hdeg
  let J := GammaGroundGammaObject.single G
  let eG := (gammaGroundGammaSingleLiftBijection G).comp (gammaGroundRVUnitGammaCodeBijection G)
  let pack := gammaGroundRVPack U.obj.domain J.rvLift.domain
  let epack : GammaGroundBijection (U.obj.domain.prod J.rvLift.domain) (U.obj.product J.rvLift).domain :=
    ⟨pack.toImage,pack.toImage_bijective (gammaGroundRVPack_injective _ _)⟩
  let e := epack.comp ((eR.prodMap eG).comp F)
  have he : gammaGroundRVSemiringClass W = gammaGroundRVSemiringClass (U.obj.product J.rvLift) :=
    PositiveGrothendieck.of_iso (gammaGroundRVSemiringPresentation hc B)
      ⟨(Nat.sub_add_cancel hmk).symm,⟨e⟩⟩
  refine ⟨gammaGroundRESDirectSumClass U ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B] gammaGroundGammaSemiringClass J,?_⟩
  rw [gammaGroundUnmeasuredTensorMap_objects]
  exact he.symm
end DiamondIntegral.Section3
