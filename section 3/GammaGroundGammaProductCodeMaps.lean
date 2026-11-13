import «section 3».GammaGroundGammaRVProductCodes
import «section 3».GammaGroundMeasuredGammaRVLift
import «section 3».GammaRVProductCodeMaps
/-! Product lift maps on every full Gamma code. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundGammaProductCode (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l)
    (a : gammaGroundCodePreimage A) (b : gammaGroundCodePreimage B) : gammaGroundCodePreimage (gammaGroundGammaAppendMap A B).image :=
  ⟨gammaCodeAppend a.val b.val, ⟨⟨((((volumeGammaSpace hc).power (Fin k)).decode a.val),
    (((volumeGammaSpace hc).power (Fin l)).decode b.val)), a.property, b.property⟩,
      (gammaCodeAppend_decode a.val b.val).symm⟩⟩

theorem gammaGroundGammaProductCode_surjective (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l)
    (c : gammaGroundCodePreimage (gammaGroundGammaAppendMap A B).image) :
    ∃ a b, gammaGroundGammaProductCode A B a b = c := by
  have ht := (gammaGroundGammaRVCodeLift_product A B).le
    (show gammaCodeTuple c.val ∈ (gammaGroundGammaRVCodeLift (gammaGroundGammaAppendMap A B).image).domain.carrier from ⟨c, rfl⟩)
  obtain ⟨p, hp⟩ := ht
  obtain ⟨a, ha⟩ := p.property.1
  obtain ⟨b, hb⟩ := p.property.2
  refine ⟨a, b, Subtype.ext ?_⟩
  apply gammaGroundGammaCodeTuple_injective
  change gammaCodeTuple (gammaCodeAppend a.val b.val) = _
  rw [gammaCodeAppend_tuple]
  exact (congrArg₂ rvAppend ha hb).trans hp


end DiamondIntegral.Section3
