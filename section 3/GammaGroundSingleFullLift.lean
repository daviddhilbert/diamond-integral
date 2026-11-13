import «section 3».GammaGroundAffinePartitionLift
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- A same-ground interpreted Gamma bijection with pointwise
old-ground unimodular formulas has an actual bijective RV lift on the
full preimages. This step uses compactness and no geometric cited input. -/
theorem gammaGroundAffine_full_lift {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (G J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (h : GammaGroundBijection G J)
    (hpoint : ∀ γ : G, ∃ F : OriginalGroundAffineRVFormula hc B n,
      (h.map γ).val = rvUnitTupleValues F.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) F.matrix γ.val) :
    ∃ L : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage J),
      ∀ u, gammaGroundFullPreimageValueMap J (L.map u) = h.map (gammaGroundFullPreimageValueMap G u) := by
  obtain ⟨N,F,P,hP,hcover,hformula⟩ := gammaGroundAffine_finite_partition hκ hs hsmall hγsmall G J h.map hpoint
  exact gammaGroundAffine_partition_full_lift G J h F P hP hcover hformula

end DiamondIntegral.Section3
