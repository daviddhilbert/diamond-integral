import «section 3».GammaGroundGammaRVCodeLift
import «section 3».GammaGroundGammaCodeRestrictions
import «section 3».GammaGroundMeasuredRVCategories
/-! Pulling a Gamma form back to all its RV codes commutes with every
source restriction. The comparison uses actual code inclusions. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

@[simp] theorem GammaGroundBijection.symm_apply_apply
    {P Q : Space LRV M} {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}
    (f : GammaGroundBijection A B) (a : A) : f.symm.map (f.map a) = a :=
  f.map.inverse_apply f.bijective a

def gammaGroundGammaRVCodeForm (I : GammaGroundGammaPiece hc ground k) (ω : GammaGroundVolumeForm hc ground I) :
    GammaGroundVolumeForm hc ground (gammaGroundGammaRVCodeLift I).domain :=
  ω.comp ((gammaGroundCodeDecode I).comp (gammaGroundGammaRVCodeBijection I).symm.map)

def gammaGroundGammaCodeInclusion {I X : GammaGroundGammaPiece hc ground k} (hX : X.carrier ⊆ I.carrier) :
    GammaGroundMap (gammaGroundCodePreimage X) (gammaGroundCodePreimage I) := GammaGroundMap.inclusion (fun _ h => hX h)

def gammaGroundGammaRVCodeInclusion {I X : GammaGroundGammaPiece hc ground k} (hX : X.carrier ⊆ I.carrier) :
    GammaGroundMap (gammaGroundGammaRVCodeLift X).domain (gammaGroundGammaRVCodeLift I).domain := GammaGroundMap.inclusion (gammaGroundGammaRVCodeLift_mono hX)

theorem gammaGroundGammaRVCodeBijection_restrict {I X : GammaGroundGammaPiece hc ground k} (hX : X.carrier ⊆ I.carrier)
    (c : gammaGroundCodePreimage X) :
    gammaGroundGammaRVCodeInclusion hX ((gammaGroundGammaRVCodeBijection X).map c) =
      (gammaGroundGammaRVCodeBijection I).map (gammaGroundGammaCodeInclusion hX c) := Subtype.ext rfl

theorem gammaGroundGammaCodeDecode_inclusion {I X : GammaGroundGammaPiece hc ground k} (hX : X.carrier ⊆ I.carrier)
    (c : gammaGroundCodePreimage X) :
    gammaGroundCodeDecode I (gammaGroundGammaCodeInclusion hX c) = GammaGroundMap.inclusion hX (gammaGroundCodeDecode X c) := Subtype.ext rfl

theorem gammaGroundGammaRVCodeForm_restrict {I X : GammaGroundGammaPiece hc ground k} (hX : X.carrier ⊆ I.carrier)
    (ω : GammaGroundVolumeForm hc ground I) :
    gammaGroundGammaRVCodeForm X (ω.comp (GammaGroundMap.inclusion hX)) = (gammaGroundGammaRVCodeForm I ω).comp (gammaGroundGammaRVCodeInclusion hX) := by
  apply GammaGroundMap.ext
  intro a
  obtain ⟨c, rfl⟩ := (gammaGroundGammaRVCodeBijection X).bijective.surjective a
  change ω (GammaGroundMap.inclusion hX (gammaGroundCodeDecode X
    ((gammaGroundGammaRVCodeBijection X).symm.map ((gammaGroundGammaRVCodeBijection X).map c)))) =
    ω (gammaGroundCodeDecode I ((gammaGroundGammaRVCodeBijection I).symm.map
      (gammaGroundGammaRVCodeInclusion hX ((gammaGroundGammaRVCodeBijection X).map c))))
  rw [GammaGroundBijection.symm_apply_apply, gammaGroundGammaRVCodeBijection_restrict,
    GammaGroundBijection.symm_apply_apply, gammaGroundGammaCodeDecode_inclusion]

end DiamondIntegral.Section3
