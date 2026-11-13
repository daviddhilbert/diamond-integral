import «section 3».TensorLocalMatches
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m : ℕ}
variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}
variable {X Y : GammaGroundRESUnitChart hc B r} {G H : GammaGroundGammaPiece hc B m}
variable {s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0}
variable {t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0}
variable {L : GammaGroundTensorBox X G} {R : GammaGroundTensorBox Y H}

/-- An inverse-graph match is reversed against the original global map,
retaining the source and target boxes literally. -/
def GammaGroundTensorBoxMatch.unsymm (F : GammaGroundBijection U0 V0)
    (E : GammaGroundTensorBoxMatch F.symm Y H t X G s R L) :
    GammaGroundTensorBoxMatch F X G s Y H t L R where
  bijection := E.bijection.symm
  congruence := gammaGroundUnmeasuredCoefficientCongruence.symm E.congruence
  agrees := by
    intro z
    have h := E.agrees (E.bijection.symm.map z)
    have he : E.bijection.map (E.bijection.symm.map z) = z := E.bijection.map.apply_inverse E.bijection.bijective z
    rw [he] at h
    have hh := congrArg F.map h
    change F.map (s (L.inclusion z)) = F.map (F.map.inverse F.bijective (t (R.inclusion (E.bijection.symm.map z)))) at hh
    rw [GammaGroundMap.apply_inverse] at hh
    exact hh.symm

def GammaGroundTensorLocalMatch.unsymm (F : GammaGroundBijection U0 V0)
    (E : GammaGroundTensorLocalMatch F.symm Y H t X G s) : GammaGroundTensorLocalMatch F X G s Y H t where
  source := E.target
  target := E.source
  data := E.data.unsymm F
  sourceCuts := by
    intro L' hA hG hneA hneG
    obtain ⟨R',⟨d⟩⟩ := E.targetCuts L' hA hG hneA hneG
    exact ⟨R',⟨d.unsymm F⟩⟩
  targetCuts := by
    intro R' hA hG hneA hneG
    obtain ⟨L',⟨d⟩⟩ := E.sourceCuts R' hA hG hneA hneG
    exact ⟨L',⟨d.unsymm F⟩⟩
end DiamondIntegral.Section3
