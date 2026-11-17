import «section 3».GammaGroundMeasuredBaseReductionOperations
import «section 3».GammaMeasuredElementaryObject

/-! Actual elementary measured objects descend through their existing
product charts. Both the old combined weight and the positive parameter
weight are retained over the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredRVReduceElementaryHom {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hrC : Cardinal.mk C.real < κ) (hrB : Cardinal.mk B.real < κ)
    (H : GammaDefinableBaseReduction C B) (U : GammaGroundMeasuredRVObject hc C (k+1))
    (i : Fin (k+1)) (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i) :
    Nonempty (GammaGroundMeasuredRVHom
      (gammaGroundMeasuredRVReduceObject H (gammaMeasuredElementaryObject hκ hs h00 hrC U i hAd))
      (gammaMeasuredElementaryObject hκ hs h00 hrB (gammaGroundMeasuredRVReduceObject H U) i
        (gammaGroundRVReduceObject_admissible H U.underlying i hAd))) := by
  let V := gammaGroundMeasuredRVReduceObject H U
  let hVB := gammaGroundRVReduceObject_admissible H U.underlying i hAd
  let EC := gammaMeasuredElementaryObject hκ hs h00 hrC U i hAd
  let EB := gammaMeasuredElementaryObject hκ hs h00 hrB V i hVB
  let CC := gammaMeasuredElementaryChart hκ hs h00 hrC U.underlying i hAd
  let CB := gammaMeasuredElementaryChart hκ hs h00 hrB V.underlying i hVB
  let eC : GammaGroundBijection (gammaGroundMeasuredRVReduceObject H EC).underlying.domain
      (V.underlying.domain.prod (gammaGroundMeasuredRVPositive hc B).underlying.domain) :=
    ⟨gammaGroundRVCodeReduceMap H (gammaRawRVSpace_codes _)
      (fun w hw j => by
        cases j with
        | inl j => exact gammaRawRVSpace_codes U.underlying.arity (w ∘ Sum.inl) hw.1 j
        | inr j => exact gammaRawRVSpace_codes 1 (w ∘ Sum.inr) hw.2 j) CC.map,CC.bijective⟩
  let f := CB.symm.comp eC
  refine ⟨⟨f,fun w => ?_⟩⟩
  have hC := gammaMeasuredElementaryObject_weight hκ hs h00 hrC U i hAd w
  have hB := gammaMeasuredElementaryObject_weight hκ hs h00 hrB V i hVB (f.map w)
  have hSquare : CB.map (f.map w) = eC.map w := CB.map.apply_inverse CB.bijective _
  change _ = V.combinedWeight ⟨(CB.map (f.map w)).val.1,(CB.map (f.map w)).property.1⟩ *
    (gammaGroundMeasuredRVPositive hc B).combinedWeight
      ⟨(CB.map (f.map w)).val.2,(CB.map (f.map w)).property.2⟩ at hB
  rw [hSquare] at hB
  exact hC.trans hB.symm

end DiamondIntegral.Section3
