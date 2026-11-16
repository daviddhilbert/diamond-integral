import «section 6».VFScalarTemplateMaps
import «section 6».UnaryIndexedMixedFamilies
import «section 6».ComponentMetadataRVTemplates

/-! Actual old coefficient maps at a unary mixed parameter. Singleton
RV-data rows identify their leading terms and inherit the same uniform
bound, without making the VF coefficients globally named constants. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem unaryFamilyParameter_values (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (b : B) :
    vfValues (η b).val=unaryFamilyParameter η b := by
  funext i
  fin_cases i
  rfl

theorem unaryCoefficient_image_good
    (T : ContinuousVFGraphTemplate (M := M) S 1 0 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good) :
    ∀ a : η.image,vfValues a.val ∈ T.good := by
  rintro ⟨a,b,rfl⟩
  rw [unaryFamilyParameter_values]
  exact hGood b

def unaryCoefficientMap (T : ContinuousVFGraphTemplate (M := M) S 1 0 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good) :
    Map B (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (vfScalarTemplateMap T η.image (unaryCoefficient_image_good T η hGood)).comp η.toImage

theorem unaryCoefficientMap_value
    (T : ContinuousVFGraphTemplate (M := M) S 1 0 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good) (b : B) :
    (unaryCoefficientMap T η hGood b).val 0=vfScalarTemplateValue T (unaryFamilyParameter η b) (hGood b) := by
  have hRel := vfScalarTemplateMap_relation T η.image (unaryCoefficient_image_good T η hGood) (η.toImage b)
  have hRaw : Sum.elim (vfValues (η b).val)
      (Sum.elim Fin.elim0 (vfValues (unaryCoefficientMap T η hGood b).val)) ∈ T.graph := hRel.2
  rw [unaryFamilyParameter_values] at hRaw
  have h0 : vfValues (Fin.elim0 : Fin 0 → VF M)=(Fin.elim0 : Fin 0 → M) := funext (fun i => i.elim0)
  have hValue := T.value_mem (unaryFamilyParameter η b) (hGood b) Fin.elim0
  rw [h0] at hValue
  have hEq := vfValues_injective ((hGood b).1.2 Fin.elim0
    (vfValues (unaryCoefficientMap T η hGood b).val)
    (vfValues (T.value (unaryFamilyParameter η b) (hGood b) Fin.elim0)) hRaw hValue)
  exact congrFun hEq 0

theorem unaryCoefficientMap_rv_constant
    (T : ContinuousVFGraphTemplate (M := M) S 1 0 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      ((coefficientRVDataTemplate T).fibre (unaryFamilyParameter η b)).carrier=
        ((coefficientRVDataTemplate T).fibre (unaryFamilyParameter η c)).carrier)
    (b c : B) (hTags : b.val.2=c.val.2) :
    rv M ((unaryCoefficientMap T η hGood b).val 0)=rv M ((unaryCoefficientMap T η hGood c).val 0) := by
  have h := hRows b c hTags
  rw [coefficientRVDataTemplate_fibre T _ (hGood b),coefficientRVDataTemplate_fibre T _ (hGood c)] at h
  have he := Set.singleton_injective h
  have hs := congrFun he (0 : Fin 1)
  simpa only [unaryCoefficientMap_value] using hs

theorem unaryCoefficientMap_bound
    (T : ContinuousVFGraphTemplate (M := M) S 1 0 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good) (γ : Gamma M)
    (hBound : ∀ b : B,∀ u ∈ ((coefficientRVDataTemplate T).fibre (unaryFamilyParameter η b)).carrier,
      ∀ i,(γ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ γ.val) (b : B) :
    (γ⁻¹).val ≤ vfValue ((unaryCoefficientMap T η hGood b).val 0) ∧
      vfValue ((unaryCoefficientMap T η hGood b).val 0) ≤ γ.val := by
  have hu : (fun _ : Fin 1 => rv M ((unaryCoefficientMap T η hGood b).val 0)) ∈
      ((coefficientRVDataTemplate T).fibre (unaryFamilyParameter η b)).carrier := by
    rw [coefficientRVDataTemplate_fibre T _ (hGood b),unaryCoefficientMap_value]
    exact Set.mem_singleton _
  exact hBound b _ hu 0

end DiamondIntegral.Section6
