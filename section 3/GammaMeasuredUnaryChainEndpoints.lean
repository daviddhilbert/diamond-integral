import «section 3».GammaMeasuredUnaryChains

/-! A unary factorization of a given full measured map can retain both
specified endpoint forms. The terminal comparison is the actual inverse
of the transported chain followed by the given map, and fixes VF. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMeasuredUnaryChain_with_endpoints
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U V : GammaGroundMeasuredVFData hc B (n+1)} (F : GammaFullMeasuredBijection U V)
    (T : GammaUnaryChain B (n+1) U.domain.carrier V.domain.carrier)
    (hT : ∀ p : U.domain, (T.toIso.equiv ⟨p.val,p.property⟩).val = (F.map.map p).val) :
    ∃ H : GammaMeasuredUnaryChain U V,
      ∀ p, ((H.fullMap hκ hs hr hv).map.map p).val = (F.map.map p).val := by
  have hU := ((gammaGroundPointIso F.map).symm (gammaLogicInput B)).target_definable (gammaLogicInput B)
  have hV := (gammaGroundPointIso F.map).target_definable (gammaLogicInput B)
  obtain ⟨hfin,η,H,hH⟩ := gammaUnaryChain_measured_transport hκ hs hr hv T hU hV U.finite U.form
  let W := gammaRawPointMeasuredData V.domain.carrier hV hfin η
  let Hf : GammaFullMeasuredBijection U W := H.fullMap hκ hs hr hv
  let K := (Hf.symm hκ hs hr hv).comp hκ hs hr hv F
  have hMaps (p : U.domain) : (Hf.map.map p).val = (F.map.map p).val := (hH p).trans (hT p)
  have hFix (q : W.domain) : (K.map.map q).val.1 = q.val.1 := by
    let p := Hf.map.symm.map q
    have he : Hf.map.map p = q := Hf.map.map.apply_inverse Hf.map.bijective q
    exact congrArg Prod.fst ((hMaps p).symm.trans (congrArg Subtype.val he))
  let R : GammaMeasuredUnaryChain W V :=
    .cons 0 K (fun q j _ => congrFun (hFix q) j) (.nil V)
  refine ⟨H.append R,?_⟩
  intro p
  rw [GammaMeasuredUnaryChain.append_fullMap_value]
  change (F.map.map (Hf.map.map.inverse Hf.map.bijective (Hf.map.map p))).val = (F.map.map p).val
  rw [GammaGroundMap.inverse_apply]

end DiamondIntegral.Section3
