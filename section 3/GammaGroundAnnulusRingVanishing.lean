import «section 3».GammaGroundAnnulusAbsorption
import «section 3».CompletionTensor
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open Algebra.GrothendieckAddGroup
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem gammaGroundGammaAnnulus_ring_zero (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (hpos : 1 ≤ δ)
    (c : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace 1) {c})
    (hcval : rvUnitValueHom (c 0) = δ) :
    (of (gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaAnnulus (hc := hc) δ hδ))) :
      GammaGroundGammaGrothendieckRing hc B) = 0 := by
  let a := gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaAnnulus (hc := hc) δ hδ))
  let t := gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaPositiveTail (hc := hc) (B := B)))
  have hp : a+t=t := gammaGroundGammaAnnulus_positive_absorption δ hδ hpos c hcdef hcval
  have h : (of (a+t) : GammaGroundGammaGrothendieckRing hc B) = of t :=
    congrArg (fun x : GammaGroundGammaPositiveSemiring hc B => (of x : GammaGroundGammaGrothendieckRing hc B)) hp
  rw [map_add] at h
  exact add_right_cancel (h.trans (zero_add _).symm)

/-- The actual full RV annulus has zero class after additive completion.
The proof uses unbounded tails and retains the stipulated RV multiplier. -/
theorem gammaGroundRVAnnulus_ring_zero (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (hpos : 1 ≤ δ)
    (c : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace 1) {c})
    (hcval : rvUnitValueHom (c 0) = δ) :
    (of (gammaGroundRVSemiringClass (gammaGroundGammaRVCodeLift (gammaGroundGammaAnnulus (hc := hc) δ hδ))) :
      GammaGroundRVGrothendieckRing hc B) = 0 := by
  have h := congrArg (ringCompletionMap (gammaGroundGammaToRVSemiring (hc := hc) (ground := B)))
    (gammaGroundGammaAnnulus_ring_zero δ hδ hpos c hcdef hcval)
  simp only [ringCompletionMap_of,gammaGroundGammaToRVSemiring_class,map_zero] at h
  have he := gammaGroundRVSemiringClass_iso (asIso (show gammaGroundGammaRVCodeLift (gammaGroundGammaAnnulus (hc := hc) δ hδ) ⟶
      (GammaGroundGammaObject.single (gammaGroundGammaAnnulus (hc := hc) δ hδ)).rvLift from
        gammaGroundGammaSingleLiftBijection (gammaGroundGammaAnnulus (hc := hc) δ hδ)))
  exact (congrArg of he).trans h
end DiamondIntegral.Section3
