import «section 3».MeasuredFiniteGammaGradedComparison
import «section 3».MeasuredGammaGradedComparison
import «section 3».MeasuredFiniteGammaSemiringSquare

/-! The actual finite Gamma inclusion is injective on the positive
semirings as well as on every homogeneous positive component. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M}

theorem measuredFiniteGammaGradedInclusion_class {k : ℕ} (A : MeasuredFiniteGammaObject hc S k) :
    measuredFiniteGammaGradedInclusion (measuredFiniteGammaDirectSumClass A) = measuredGammaDirectSumClass hc A.obj := by
  change DirectSum.map (fun _ => measuredFiniteGammaToGammaKPlus)
    (DirectSum.of (MeasuredFiniteGammaKPlus hc S) k (measuredFiniteGammaClass A)) = _
  rw [DirectSum.map_of, measuredFiniteGammaToGammaKPlus_class]
  rfl

theorem measuredFiniteGammaInclusion_grading :
    (measuredGammaPresentationToDirectSum (M := M) (hc := hc) (S := S)).comp measuredFiniteGammaToGammaSemiring =
      measuredFiniteGammaGradedInclusion.comp measuredFiniteGammaPresentationToDirectSum := by
  apply PositiveGrothendieck.hom_ext (measuredFiniteGammaSemiringPresentation hc S)
  rintro ⟨k, A⟩
  change measuredGammaPresentationToDirectSum (measuredFiniteGammaToGammaSemiring (measuredFiniteGammaSemiringClass A)) =
    measuredFiniteGammaGradedInclusion (measuredFiniteGammaPresentationToDirectSum (measuredFiniteGammaSemiringClass A))
  rw [measuredFiniteGammaToGammaSemiring_class, measuredGammaPresentationToDirectSum_class,
    measuredFiniteGammaPresentationToDirectSum_class, measuredFiniteGammaGradedInclusion_class]

theorem measuredFiniteGammaToGammaSemiring_injective :
    Function.Injective (measuredFiniteGammaToGammaSemiring (M := M) (hc := hc) (S := S)) := by
  intro a b h
  apply (measuredFiniteGammaSemiringEquivDirectSum (hc := hc) (S := S)).injective
  apply measuredFiniteGammaGradedInclusion_injective
  have he := congrArg (measuredGammaPresentationToDirectSum (hc := hc) (S := S)) h
  have ha := RingHom.congr_fun (measuredFiniteGammaInclusion_grading (hc := hc) (S := S)) a
  have hb := RingHom.congr_fun (measuredFiniteGammaInclusion_grading (hc := hc) (S := S)) b
  exact ha.symm.trans (he.trans hb)

end DiamondIntegral.Section3
