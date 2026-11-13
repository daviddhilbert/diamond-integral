import «section 3».GammaGroundUnmeasuredTensorMap
import «section 3».GammaGroundRESPositiveComparison
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

/-- One actual graded RES/Gamma product term in the positive tensor. -/
structure GammaGroundUnmeasuredTensorTerm (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  residueDegree : ℕ
  gammaDegree : ℕ
  residue : GammaGroundRESObject hc B residueDegree
  gamma : GammaGroundGammaObject hc B gammaDegree

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def GammaGroundUnmeasuredTensorTerm.value (t : GammaGroundUnmeasuredTensorTerm hc B) :
    GammaGroundUnmeasuredPositiveTensor hc B :=
  gammaGroundRESDirectSumClass t.residue ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    gammaGroundGammaSemiringClass t.gamma

def GammaGroundUnmeasuredTensorTerm.rvObject (t : GammaGroundUnmeasuredTensorTerm hc B) :
    GammaGroundRVObject hc B (t.residueDegree+t.gammaDegree) := t.residue.obj.product t.gamma.rvLift

theorem GammaGroundUnmeasuredTensorTerm.value_image (t : GammaGroundUnmeasuredTensorTerm hc B) :
    gammaGroundUnmeasuredTensorMap t.value = gammaGroundRVSemiringClass t.rvObject :=
  gammaGroundUnmeasuredTensorMap_objects t.residue t.gamma

/-- Every positive tensor is a finite sum of actual graded product
objects. The construction uses additive normal forms and no cancellation. -/
theorem gammaGroundUnmeasuredTensor_object_normal_form (t : GammaGroundUnmeasuredPositiveTensor hc B) :
    ∃ l : List (GammaGroundUnmeasuredTensorTerm hc B),
      t = (l.map GammaGroundUnmeasuredTensorTerm.value).sum := by
  have hobj {r : ℕ} (X : GammaGroundRESObject hc B r)
      (b : GammaGroundGammaPositiveSemiring hc B) :
      ∃ l : List (GammaGroundUnmeasuredTensorTerm hc B),
        gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B] b =
          (l.map GammaGroundUnmeasuredTensorTerm.value).sum := by
    apply positivePresentation_additive_induction (gammaGroundGammaSemiringPresentation hc B)
      (motive := fun b => ∃ l : List (GammaGroundUnmeasuredTensorTerm hc B),
        gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B] b =
          (l.map GammaGroundUnmeasuredTensorTerm.value).sum) _ _ _ b
    · exact ⟨[],by simp only [TensorProduct.tmul_zero,List.map_nil,List.sum_nil]⟩
    · rintro ⟨n,G⟩
      exact ⟨[⟨r,n,X,G⟩],rfl⟩
    · rintro a b ⟨l,hl⟩ ⟨q,hq⟩
      refine ⟨l++q,?_⟩
      rw [TensorProduct.tmul_add,hl,hq,List.map_append,List.sum_append]
  have hleft (a : GammaGroundRESDirectSum hc B) : ∀ b : GammaGroundGammaPositiveSemiring hc B,
      ∃ l : List (GammaGroundUnmeasuredTensorTerm hc B),
        a ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B] b = (l.map GammaGroundUnmeasuredTensorTerm.value).sum := by
    induction a using DirectSum.induction_on with
    | zero => intro b; exact ⟨[],by simp only [TensorProduct.zero_tmul,List.map_nil,List.sum_nil]⟩
    | of r x =>
      obtain ⟨X,rfl⟩ := gammaGroundRESClass_surjective x
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
