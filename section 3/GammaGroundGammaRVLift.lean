import «section 3».GammaGroundGammaRVCodeLift
import «section 3».GammaGroundFamilyPieceMaps
import «section 3».GammaGroundRVFamilyObjects
/-! The actual Gamma-to-RV object lift for every finite tagged gammaGroundFamily.
A Gamma arrow supplies a genuine RV isomorphism of these lifts. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundGammaObject.rvPieces (A : GammaGroundGammaObject hc ground k) : GammaGroundFiniteFamily hc ground (rawRVSpace k) :=
  ⟨A.tags, fun i => (gammaGroundGammaRVCodeLift (A.piece i)).domain⟩

def GammaGroundGammaObject.rvCodeBijection (A : GammaGroundGammaObject hc ground k) :
    GammaGroundFamilyBijection A.codeLift A.rvPieces :=
  GammaGroundFamilyBijection.pieces A.codeLift _ (fun i => gammaGroundGammaRVCodeBijection (A.piece i))

theorem GammaGroundGammaObject.rvPieces_nonzero (A : GammaGroundGammaObject hc ground k)
    (i : Fin A.rvPieces.tags) (a : A.rvPieces.piece i) (j : Fin k) :
    (a.val j).val ≠ iRVZero := (gammaGroundGammaRVCodeLift (A.piece i)).nonzero a j

def GammaGroundGammaObject.rvLift (A : GammaGroundGammaObject hc ground k) : GammaGroundRVObject hc ground k :=
  A.rvPieces.rvObject A.rvPieces_nonzero

theorem gammaGroundGammaHom_lift_iso {A B : GammaGroundGammaObject hc ground k} (f : A ⟶ B) :
    Nonempty (A.rvLift ≅ B.rvLift) := by
  obtain ⟨F, _⟩ := f.contraction
  exact ⟨gammaGroundRVFamilyIso A.rvPieces_nonzero B.rvPieces_nonzero
    (B.rvCodeBijection.comp (F.comp A.rvCodeBijection.symm))⟩

end DiamondIntegral.Section3
