import «section 3».GammaMeasuredElementaryCongruence

/-! The principal point/cone relation applies to every finite head on the
same RV domain. Its Gamma form retains the entire original combined
weight; the deleted coordinate need not be last. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

theorem gammaMeasuredFiniteHead_principal_congruence
    (U W : GammaGroundMeasuredRVObject hc B (n+1))
    (v : GammaGroundMap U.underlying.domain (GammaGroundDefSet.univ hc B (rawRVSpace n)))
    (hfin : v.FiniteFibres) (hNZ : ∀ u j, ((v u).val j).val ≠ iRVZero)
    (e : GammaGroundBijection W.underlying.domain
      (U.underlying.domain.prod (gammaGroundMeasuredRVPositive hc B).underlying.domain))
    (hw : ∀ w, W.combinedWeight w =
      U.combinedWeight ⟨(e.map w).val.1,(e.map w).property.1⟩ *
        (gammaGroundMeasuredRVPositive hc B).combinedWeight ⟨(e.map w).val.2,(e.map w).property.2⟩) :
    gammaGroundMeasuredRVSpecialCongruence hc B (gammaGroundMeasuredRVSemiringClass U)
      (gammaGroundMeasuredRVSemiringClass W) := by
  let H0 : GammaGroundRVObject hc B n := ⟨U.underlying.arity,U.underlying.domain,v,hfin,hNZ⟩
  let H := H0.withCombinedWeight U.combinedWeightForm
  let P := gammaMeasuredPointZeroArity hc B
  let Q := gammaGroundMeasuredRVPositive hc B
  have hH (u : U.underlying.domain) : H.combinedWeight u = U.combinedWeight u :=
    (GammaGroundRVObject.withCombinedWeight_value H0 U.combinedWeightForm u).trans (U.combinedWeightForm_value u)
  let fU : GammaGroundMeasuredRVHom U (H.product P) := {
    bijection := (gammaGroundRVProductRightUnitBijection H.underlying).symm
    preserves := by
      intro u
      rw [GammaGroundMeasuredRVObject.product_combined,gammaMeasuredPointZeroArity_weight,mul_one]
      have hl : gammaGroundMeasuredRVProductLeft H P
          ((gammaGroundRVProductRightUnitBijection H.underlying).symm.map u) = u :=
        (gammaGroundRVProductRightUnitBijection H.underlying).map.apply_inverse
          (gammaGroundRVProductRightUnitBijection H.underlying).bijective u
      rw [hl]
      exact (hH u).symm }
  let fW : GammaGroundMeasuredRVHom W (H.product Q) := {
    bijection := (gammaGroundRVPackBijection H.underlying.domain Q.underlying.domain).comp e
    preserves := by
      intro w
      let a : U.underlying.domain := ⟨(e.map w).val.1,(e.map w).property.1⟩
      let b : Q.underlying.domain := ⟨(e.map w).val.2,(e.map w).property.2⟩
      change W.combinedWeight w = (H.product Q).combinedWeight
        (gammaGroundRVPackPair H.underlying.domain Q.underlying.domain a b)
      exact (hw w).trans ((congrArg (fun z => z * Q.combinedWeight b) (hH a).symm).trans
        (GammaGroundMeasuredRVObject.product_combined_pair H Q a b).symm) }
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  have hpoint : q (gammaGroundMeasuredRVSemiringClass P) = q (gammaGroundMeasuredRVSemiringClass Q) := by
    have hn := gammaGroundMeasuredRVSemiringClass_iso (asIso
      (show P ⟶ gammaGroundMeasuredRVOne hc B from gammaMeasuredPointZeroArityHom hc B))
    exact (congrArg q hn).trans ((gammaGroundMeasuredRVSpecialCongruence hc B).eq.mpr
      (RingCon.le_ringConGen _ _ ⟨rfl,rfl⟩))
  have hU := gammaGroundMeasuredRVSemiringClass_iso (asIso (show U ⟶ H.product P from fU))
  have hW := gammaGroundMeasuredRVSemiringClass_iso (asIso (show W ⟶ H.product Q from fW))
  rw [gammaGroundMeasuredRVSemiringClass_product] at hU hW
  apply (gammaGroundMeasuredRVSpecialCongruence hc B).eq.mp
  change q _ = q _
  rw [hU,hW,map_mul,map_mul,hpoint]

end DiamondIntegral.Section3
