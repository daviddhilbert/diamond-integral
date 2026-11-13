import «section 3».FiniteGammaGradedComparison
import «section 3».GammaGradedComparison
import «section 3».FiniteGammaSemiringSquare

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

theorem finiteGammaGradedInclusion_class {k : ℕ} (A : FiniteGammaObject hc S k) :
    finiteGammaGradedInclusion (finiteGammaDirectSumClass A) = gammaDirectSumClass hc A.obj := by
  change DirectSum.map (fun _ => finiteGammaToGammaKPlus)
    (DirectSum.of (FiniteGammaKPlus hc S) k (finiteGammaClass A)) = _
  rw [DirectSum.map_of, finiteGammaToGammaKPlus_class]
  rfl

theorem finiteGammaInclusion_grading :
    (gammaPresentationToDirectSum (M := M) (hc := hc) (S := S)).comp finiteGammaToGammaSemiring =
      finiteGammaGradedInclusion.comp finiteGammaPresentationToDirectSum := by
  apply PositiveGrothendieck.hom_ext (finiteGammaSemiringPresentation hc S)
  rintro ⟨k, A⟩
  change gammaPresentationToDirectSum (finiteGammaToGammaSemiring (finiteGammaSemiringClass A)) =
    finiteGammaGradedInclusion (finiteGammaPresentationToDirectSum (finiteGammaSemiringClass A))
  rw [finiteGammaToGammaSemiring_class, gammaPresentationToDirectSum_class,
    finiteGammaPresentationToDirectSum_class, finiteGammaGradedInclusion_class]

theorem finiteGammaToGammaSemiring_injective :
    Function.Injective (finiteGammaToGammaSemiring (M := M) (hc := hc) (S := S)) := by
  intro a b h
  apply (finiteGammaSemiringEquivDirectSum (hc := hc) (S := S)).injective
  apply finiteGammaGradedInclusion_injective
  have he := congrArg (gammaPresentationToDirectSum (hc := hc) (S := S)) h
  have ha := RingHom.congr_fun (finiteGammaInclusion_grading (hc := hc) (S := S)) a
  have hb := RingHom.congr_fun (finiteGammaInclusion_grading (hc := hc) (S := S)) b
  exact ha.symm.trans (he.trans hb)

end DiamondIntegral.Section3
