import «section 3».GammaGroundGammaProductDecomposition
import «section 3».GammaCodeProjections
/-! Coordinate projections and concatenation identities on all full
Gamma codes are definable over the same original real base. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundGammaCodeLeftMap (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k l : ℕ) :
    GammaGroundMap (GammaGroundDefSet.univ hc ground (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))))
      (GammaGroundDefSet.univ hc ground (codeSpace ((volumeGammaSpace hc).power (Fin k)))) :=
  GammaGroundMap.ofGlobal _ _ (gammaCodeLeftMap hc ground.real k l) (fun _ => Set.mem_univ _)

def gammaGroundGammaCodeRightMap (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k l : ℕ) :
    GammaGroundMap (GammaGroundDefSet.univ hc ground (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))))
      (GammaGroundDefSet.univ hc ground (codeSpace ((volumeGammaSpace hc).power (Fin l)))) :=
  GammaGroundMap.ofGlobal _ _ (gammaCodeRightMap hc ground.real k l) (fun _ => Set.mem_univ _)

theorem gammaGroundGammaProductCodePieceEquiv_left_val (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l)
    (c : gammaGroundCodePreimage (gammaGroundGammaAppendMap A B).image) :
    (gammaGroundGammaProductCodePieceEquiv A B c).1.val = gammaCodeLeft c.val := by
  obtain ⟨a, b, rfl⟩ := gammaGroundGammaProductCode_surjective A B c
  rw [gammaGroundGammaProductCodePieceEquiv_code]
  exact (gammaCodeLeft_append a.val b.val).symm

theorem gammaGroundGammaProductCodePieceEquiv_right_val (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l)
    (c : gammaGroundCodePreimage (gammaGroundGammaAppendMap A B).image) :
    (gammaGroundGammaProductCodePieceEquiv A B c).2.val = gammaCodeRight c.val := by
  obtain ⟨a, b, rfl⟩ := gammaGroundGammaProductCode_surjective A B c
  rw [gammaGroundGammaProductCodePieceEquiv_code]
  exact (gammaCodeRight_append a.val b.val).symm

end DiamondIntegral.Section3
