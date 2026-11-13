import «section 3».GammaRVCodeLift
import «section 3».GammaCodeRestrictions

/-! Pulling a Gamma form back to all its RV codes commutes with every
source restriction. The comparison uses actual code inclusions. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def gammaRVCodeForm (I : GammaPiece hc S k) (ω : GammaVolumeForm hc I) :
    GammaVolumeForm hc (gammaRVCodeLift I).domain :=
  ω.comp ((codeDecode I).comp (gammaRVCodeBijection I).symm.map)

def gammaCodeInclusion {I X : GammaPiece hc S k} (hX : X.carrier ⊆ I.carrier) :
    Map (codePreimage X) (codePreimage I) := Map.inclusion (fun _ h => hX h)

def gammaRVCodeInclusion {I X : GammaPiece hc S k} (hX : X.carrier ⊆ I.carrier) :
    Map (gammaRVCodeLift X).domain (gammaRVCodeLift I).domain := Map.inclusion (gammaRVCodeLift_mono hX)

theorem gammaRVCodeBijection_restrict {I X : GammaPiece hc S k} (hX : X.carrier ⊆ I.carrier)
    (c : codePreimage X) :
    gammaRVCodeInclusion hX ((gammaRVCodeBijection X).map c) =
      (gammaRVCodeBijection I).map (gammaCodeInclusion hX c) := Subtype.ext rfl

theorem gammaCodeDecode_inclusion {I X : GammaPiece hc S k} (hX : X.carrier ⊆ I.carrier)
    (c : codePreimage X) :
    codeDecode I (gammaCodeInclusion hX c) = Map.inclusion hX (codeDecode X c) := Subtype.ext rfl

theorem gammaRVCodeForm_restrict {I X : GammaPiece hc S k} (hX : X.carrier ⊆ I.carrier)
    (ω : GammaVolumeForm hc I) :
    gammaRVCodeForm X (ω.comp (Map.inclusion hX)) = (gammaRVCodeForm I ω).comp (gammaRVCodeInclusion hX) := by
  apply Map.ext
  intro a
  obtain ⟨c, rfl⟩ := (gammaRVCodeBijection X).bijective.surjective a
  change ω (Map.inclusion hX (codeDecode X
    ((gammaRVCodeBijection X).symm.map ((gammaRVCodeBijection X).map c)))) =
    ω (codeDecode I ((gammaRVCodeBijection I).symm.map
      (gammaRVCodeInclusion hX ((gammaRVCodeBijection X).map c))))
  rw [DefinableBijection.symm_apply_apply, gammaRVCodeBijection_restrict,
    DefinableBijection.symm_apply_apply, gammaCodeDecode_inclusion]

end DiamondIntegral.Section3
