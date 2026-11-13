import «section 3».GammaGroundMeasuredFiniteGammaGradedComparison
import «section 3».GammaGroundMeasuredGammaGradedComparison
import «section 3».GammaGroundMeasuredFiniteGammaSemiringSquare
/-! The actual finite Gamma inclusion is injective on the positive
semirings as well as on every homogeneous positive component. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

theorem gammaGroundMeasuredFiniteGammaGradedInclusion_class {k : ℕ} (A : GammaGroundMeasuredFiniteGammaObject hc ground k) :
    gammaGroundMeasuredFiniteGammaGradedInclusion (gammaGroundMeasuredFiniteGammaDirectSumClass A) = gammaGroundMeasuredGammaDirectSumClass hc A.obj := by
  change DirectSum.map (fun _ => gammaGroundMeasuredFiniteGammaToGammaKPlus)
    (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k (gammaGroundMeasuredFiniteGammaClass A)) = _
  rw [DirectSum.map_of, gammaGroundMeasuredFiniteGammaToGammaKPlus_class]
  rfl

theorem gammaGroundMeasuredFiniteGammaInclusion_grading :
    (gammaGroundMeasuredGammaPresentationToDirectSum (M := M) (hc := hc) (ground := ground)).comp gammaGroundMeasuredFiniteGammaToGammaSemiring =
      gammaGroundMeasuredFiniteGammaGradedInclusion.comp gammaGroundMeasuredFiniteGammaPresentationToDirectSum := by
  apply PositiveGrothendieck.hom_ext (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground)
  rintro ⟨k, A⟩
  change gammaGroundMeasuredGammaPresentationToDirectSum (gammaGroundMeasuredFiniteGammaToGammaSemiring (gammaGroundMeasuredFiniteGammaSemiringClass A)) =
    gammaGroundMeasuredFiniteGammaGradedInclusion (gammaGroundMeasuredFiniteGammaPresentationToDirectSum (gammaGroundMeasuredFiniteGammaSemiringClass A))
  rw [gammaGroundMeasuredFiniteGammaToGammaSemiring_class, gammaGroundMeasuredGammaPresentationToDirectSum_class,
    gammaGroundMeasuredFiniteGammaPresentationToDirectSum_class, gammaGroundMeasuredFiniteGammaGradedInclusion_class]

theorem gammaGroundMeasuredFiniteGammaToGammaSemiring_injective :
    Function.Injective (gammaGroundMeasuredFiniteGammaToGammaSemiring (M := M) (hc := hc) (ground := ground)) := by
  intro a b h
  apply (gammaGroundMeasuredFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := ground)).injective
  apply gammaGroundMeasuredFiniteGammaGradedInclusion_injective
  have he := congrArg (gammaGroundMeasuredGammaPresentationToDirectSum (hc := hc) (ground := ground)) h
  have ha := RingHom.congr_fun (gammaGroundMeasuredFiniteGammaInclusion_grading (hc := hc) (ground := ground)) a
  have hb := RingHom.congr_fun (gammaGroundMeasuredFiniteGammaInclusion_grading (hc := hc) (ground := ground)) b
  exact ha.symm.trans (he.trans hb)

end DiamondIntegral.Section3
