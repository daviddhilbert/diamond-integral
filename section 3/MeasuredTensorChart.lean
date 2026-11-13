import «section 3».GammaGroundMeasuredGammaUnitLift
import «section 3».GammaGroundPrescribedWeights
import «section 3».RVProductRESFactor
import «section 3».GammaGroundMeasuredTensorMap
import «section 3».GammaGroundBijectionProducts
import «section 3».GammaGroundRVPackPairs
import Section4.EarlierRVInputs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m k l : ℕ}

theorem gammaGroundMeasuredRVSemiringClass_of_weight_bijection
    (U : GammaGroundMeasuredRVObject hc B k) (V : GammaGroundMeasuredRVObject hc B l)
    (h : k = l) (F : GammaGroundBijection U.underlying.domain V.underlying.domain)
    (hF : ∀ a, U.combinedWeight a = V.combinedWeight (F.map a)) :
    gammaGroundMeasuredRVSemiringClass U = gammaGroundMeasuredRVSemiringClass V := by
  cases h
  let f : GammaGroundMeasuredRVHom U V := ⟨F,hF⟩
  exact gammaGroundMeasuredRVSemiringClass_iso (asIso (show U ⟶ V from f))

/-- Every nonempty weight-preserving product chart has a preimage under
the actual measured balanced tensor map over the original mixed ground. -/
theorem gammaGroundMeasuredTensor_chart_preimage {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (W : GammaGroundMeasuredRVObject hc B k) (hW : W.underlying.domain.carrier.Nonempty)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundGammaPiece hc B m)
    (f : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (F : GammaGroundBijection W.underlying.domain (R.prod (gammaGroundRVUnitGammaPreimage G)))
    (hweight : ∀ a, W.combinedWeight a = f (rvUnitTupleValues (F.map a).val.2)) :
    ∃ t : GammaGroundMeasuredPositiveTensor hc B,
      gammaGroundMeasuredTensorMap t = gammaGroundMeasuredRVSemiringClass W := by
  let hex := rvExchangeInput_of_earlier hκ hs h00
  let hγ := gammaRVAlgebraicityInput_of_earlier hκ hs h00
  obtain ⟨w,hw⟩ := hW
  let q := F.map ⟨w,hw⟩
  let r : R := ⟨q.val.1,q.property.1⟩
  have hG : G.carrier.Nonempty := ⟨rvUnitTupleValues q.val.2,q.property.2⟩
  let label := W.underlying.volume.comp F.symm.map
  have hlabel : label.FiniteFibres := W.underlying.finite.comp
    (GammaGroundMap.finiteFibres_of_injective F.symm.bijective.1)
  obtain ⟨U,⟨eR⟩⟩ := gammaGroundRVProduct_RES_factor hex hκ hs h00 hγ hsmall R hR G hG _ label hlabel
  have hdeg := gammaGroundRVProduct_residue_rank_add_le hex hκ hs h00 hγ hsmall R G hG _ label hlabel r
  have hmk : m ≤ k := (Nat.le_add_left m _).trans hdeg
  let V := U.withCombinedWeight (gammaGroundOneForm U.obj.domain)
  let J := gammaGroundMeasuredGammaSingleWeight G f hf
  let eG := gammaGroundGammaUnitLiftBijection G
  let pack := gammaGroundRVPack V.obj.underlying.domain J.rvLift.underlying.domain
  let epack : GammaGroundBijection (V.obj.underlying.domain.prod J.rvLift.underlying.domain)
      (V.obj.product J.rvLift).underlying.domain :=
    ⟨pack.toImage,pack.toImage_bijective (gammaGroundRVPack_injective _ _)⟩
  let e := epack.comp ((eR.prodMap eG).comp F)
  have heweight : ∀ a, W.combinedWeight a = (V.obj.product J.rvLift).combinedWeight (e.map a) := by
    intro a
    let p := F.map a
    let ra : R := ⟨p.val.1,p.property.1⟩
    let ga : gammaGroundRVUnitGammaPreimage G := ⟨p.val.2,p.property.2⟩
    have he : e.map a = gammaGroundRVPackPair V.obj.underlying.domain J.rvLift.underlying.domain
        (eR.map ra) (eG.map ga) := rfl
    rw [he,GammaGroundMeasuredRVObject.product_combined_pair]
    change W.combinedWeight a = (U.obj.withCombinedWeight (gammaGroundOneForm U.obj.domain)).combinedWeight
      (eR.map ra) * J.rvLift.combinedWeight (eG.map ga)
    rw [GammaGroundRVObject.withCombinedWeight_value,gammaGroundOneForm_value,one_mul,
      gammaGroundMeasuredGammaUnitLift_combined]
    exact hweight a
  have he := gammaGroundMeasuredRVSemiringClass_of_weight_bijection W (V.obj.product J.rvLift)
    (Nat.sub_add_cancel hmk).symm e heweight
  refine ⟨gammaGroundMeasuredRESDirectSumClass V ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    gammaGroundMeasuredGammaSemiringClass J,?_⟩
  rw [gammaGroundMeasuredTensorMap_objects]
  exact he.symm
end DiamondIntegral.Section3
