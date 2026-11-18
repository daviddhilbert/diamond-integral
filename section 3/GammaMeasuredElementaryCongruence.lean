import «section 3».GammaMeasuredPrincipalFactor

/-! The full weighted point/cone factorization belongs to the originally
stated semiring congruence, including its degree-one boundary case. -/
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

theorem gammaMeasuredElementary_principal_congruence
    (U W : GammaGroundMeasuredRVObject hc B (n+1))
    (hfin : (gammaRVHeadMap U.underlying).FiniteFibres)
    (e : GammaGroundBijection W.underlying.domain
      (U.underlying.domain.prod (gammaGroundMeasuredRVPositive hc B).underlying.domain))
    (hw : ∀ w, W.combinedWeight w =
      U.combinedWeight ⟨(e.map w).val.1,(e.map w).property.1⟩ *
        (gammaGroundMeasuredRVPositive hc B).combinedWeight ⟨(e.map w).val.2,(e.map w).property.2⟩) :
    gammaGroundMeasuredRVSpecialCongruence hc B
      (gammaGroundMeasuredRVSemiringClass U) (gammaGroundMeasuredRVSemiringClass W) := by
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  have hpoint : q (gammaGroundMeasuredRVSemiringClass (gammaMeasuredPointZeroArity hc B)) =
      q (gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVPositive hc B)) := by
    have hn := gammaGroundMeasuredRVSemiringClass_iso
      (asIso (show gammaMeasuredPointZeroArity hc B ⟶ gammaGroundMeasuredRVOne hc B from gammaMeasuredPointZeroArityHom hc B))
    exact (congrArg q hn).trans ((gammaGroundMeasuredRVSpecialCongruence hc B).eq.mpr
      (RingCon.le_ringConGen _ _ ⟨rfl,rfl⟩))
  have hU := gammaGroundMeasuredRVSemiringClass_iso
    (asIso (show U ⟶ (gammaMeasuredHeadFactor U hfin).product (gammaMeasuredPointZeroArity hc B) from gammaMeasuredHeadPointHom U hfin))
  have hW := gammaGroundMeasuredRVSemiringClass_iso
    (asIso (show W ⟶ (gammaMeasuredHeadFactor U hfin).product (gammaGroundMeasuredRVPositive hc B) from gammaMeasuredHeadConeHom U W hfin e hw))
  rw [gammaGroundMeasuredRVSemiringClass_product] at hU hW
  apply (gammaGroundMeasuredRVSpecialCongruence hc B).eq.mp
  change q _ = q _
  rw [hU,hW,map_mul,map_mul,hpoint]

end DiamondIntegral.Section3
