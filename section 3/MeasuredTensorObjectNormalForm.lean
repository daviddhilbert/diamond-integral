import «section 3».GammaGroundMeasuredTensorMap
import «section 3».GammaGroundMeasuredRESPositiveComparison
import «section 3».PresentationAdditiveNormalForm
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- One actual graded measured RES/Gamma product term in the positive tensor. -/
structure GammaGroundMeasuredTensorTerm (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  residueDegree : ℕ
  gammaDegree : ℕ
  residue : GammaGroundMeasuredRESObject hc B residueDegree
  gamma : GammaGroundMeasuredGammaObject hc B gammaDegree

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def GammaGroundMeasuredTensorTerm.value (t : GammaGroundMeasuredTensorTerm hc B) :
    GammaGroundMeasuredPositiveTensor hc B :=
  gammaGroundMeasuredRESDirectSumClass t.residue ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    gammaGroundMeasuredGammaSemiringClass t.gamma

def GammaGroundMeasuredTensorTerm.rvObject (t : GammaGroundMeasuredTensorTerm hc B) :
    GammaGroundMeasuredRVObject hc B (t.residueDegree+t.gammaDegree) := t.residue.obj.product t.gamma.rvLift

theorem GammaGroundMeasuredTensorTerm.value_image (t : GammaGroundMeasuredTensorTerm hc B) :
    gammaGroundMeasuredTensorMap t.value = gammaGroundMeasuredRVSemiringClass t.rvObject :=
  gammaGroundMeasuredTensorMap_objects t.residue t.gamma

/-- Every positive measured tensor is a finite sum of actual graded product
objects. The construction uses additive normal forms and no cancellation. -/
theorem gammaGroundMeasuredTensor_object_normal_form (t : GammaGroundMeasuredPositiveTensor hc B) :
    ∃ l : List (GammaGroundMeasuredTensorTerm hc B),
      t = (l.map GammaGroundMeasuredTensorTerm.value).sum := by
  have hobj {r : ℕ} (X : GammaGroundMeasuredRESObject hc B r)
      (b : GammaGroundMeasuredGammaPositiveSemiring hc B) :
      ∃ l : List (GammaGroundMeasuredTensorTerm hc B),
        gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B] b =
          (l.map GammaGroundMeasuredTensorTerm.value).sum := by
    apply positivePresentation_additive_induction (gammaGroundMeasuredGammaSemiringPresentation hc B)
      (motive := fun b => ∃ l : List (GammaGroundMeasuredTensorTerm hc B),
        gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B] b =
          (l.map GammaGroundMeasuredTensorTerm.value).sum) _ _ _ b
    · exact ⟨[],by simp only [TensorProduct.tmul_zero,List.map_nil,List.sum_nil]⟩
    · rintro ⟨n,G⟩
      exact ⟨[⟨r,n,X,G⟩],rfl⟩
    · rintro a b ⟨l,hl⟩ ⟨q,hq⟩
      refine ⟨l++q,?_⟩
      rw [TensorProduct.tmul_add,hl,hq,List.map_append,List.sum_append]
  have hleft (a : GammaGroundMeasuredRESDirectSum hc B) : ∀ b : GammaGroundMeasuredGammaPositiveSemiring hc B,
      ∃ l : List (GammaGroundMeasuredTensorTerm hc B),
        a ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B] b = (l.map GammaGroundMeasuredTensorTerm.value).sum := by
    induction a using DirectSum.induction_on with
    | zero => intro b; exact ⟨[],by simp only [TensorProduct.zero_tmul,List.map_nil,List.sum_nil]⟩
    | of r x =>
      obtain ⟨X,rfl⟩ := gammaGroundMeasuredRESClass_surjective x
      exact hobj X
    | add a b ha hb =>
      intro z
      obtain ⟨l,hl⟩ := ha z
      obtain ⟨q,hq⟩ := hb z
      refine ⟨l++q,?_⟩
      rw [TensorProduct.add_tmul,hl,hq,List.map_append,List.sum_append]
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact hleft a b
  | add a b ha hb =>
    obtain ⟨l,hl⟩ := ha
    obtain ⟨q,hq⟩ := hb
    exact ⟨l++q,by rw [hl,hq,List.map_append,List.sum_append]⟩
end DiamondIntegral.Section3
